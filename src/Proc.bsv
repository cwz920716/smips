
import Types::*;
import ProcTypes::*;
import MemTypes::*;
import RFile::*;
import IMemory::*;
import DMemory::*;
import Decode::*;
import Exec::*;
import Cop::*;
import Fifo::*;
import GetPut::*;
import AddrPred::*;
import Scoreboard::*;

typedef UInt#(4) Epoch;

typedef struct {
	Addr pc;
	Addr ppc;
	Epoch epoch;
} Fetch2Decode deriving (Bits);

typedef struct {
	Addr pc;
	Addr ppc;
	Epoch epoch;
	DecodedInst dInst;
} Decode2Issue deriving (Bits);

typedef struct {
	Addr pc;
	Addr ppc;
	Epoch epoch;
	DecodedInst dInst;
        Data rVal1;
        Data rVal2;
} Issue2Execute deriving (Bits);

typedef struct {
	ExecInst eInst;
} Execute2Memory deriving (Bits);

typedef struct {
	ExecInst eInst;
} Memory2WriteBack deriving (Bits);

typedef struct {
	Addr pc;
        Epoch epoch;
} ExecuteRedirect deriving (Bits);

typedef enum {Fetch, Decode, Issue, Execute, Memory, WriteBack} State deriving (Bits, Eq);

(* synthesize *)
module [Module] mkProc(Proc);
  Reg#(Addr) pc <- mkRegU;
  RFile      rf <- mkBypassRFile;
  IMemory  iMem <- mkIMemory;
  DMemory  dMem <- mkDMemory;
  Cop       cop <- mkCop;
  
  // Reg#(State) state <- mkReg(Fetch1);
  // Reg#(Data)     ir <- mkRegU;

  AddrPred addrPred <- mkPcPlus4;
  Fifo#(1, Fetch2Decode) f2d <- mkPipelineFifo();
  Fifo#(1, Decode2Issue) d2i <- mkPipelineFifo();
  Fifo#(1, Issue2Execute) i2e <- mkPipelineFifo();
  Fifo#(1, Execute2Memory) e2m <- mkPipelineFifo();
  Fifo#(1, Memory2WriteBack) m2w <- mkPipelineFifo();
  Fifo#(1, ExecuteRedirect) execRedirect <- mkBypassFifo();
  Scoreboard#(8) sb <- mkPipelineScoreboard();
  
  Reg#(Epoch) fEpoch <- mkReg(0);
  Reg#(Epoch) eEpoch <- mkReg(0);

  Bool memReady = iMem.init.done() && dMem.init.done();

  rule doFetch(cop.started);
    $display("pc: %h: epoch: %d Eepoch: %h", pc, fEpoch, eEpoch);
    if (execRedirect.notEmpty) begin
      fEpoch <= execRedirect.first.epoch;
      pc <= execRedirect.first.pc;
      execRedirect.deq;
    end else begin
      // switch to Get state
      let ppc = addrPred.predPc(pc);
      pc <= ppc;
      f2d.enq (Fetch2Decode{pc: pc, ppc: ppc, epoch: fEpoch});
      iMem.req.put(MemReq{op: Ld, addr: pc, data: ?});
    end
  endrule

  rule doDecode(cop.started && f2d.notEmpty);
    let inst <- iMem.resp.get();

    let pc = f2d.first.pc;
    let ppc = f2d.first.ppc;
    let epoch = f2d.first.epoch;
    let dInst = decode(inst);
    d2i.enq (Decode2Issue{pc: pc, ppc: ppc, epoch: epoch, dInst: dInst});
    f2d.deq;
  endrule

  rule doIssue(cop.started && d2i.notEmpty);
    let pc = d2i.first.pc;
    let ppc = d2i.first.ppc;
    let epoch = d2i.first.epoch;
    let dInst = d2i.first.dInst;
    let stall = sb.search1(dInst.src1) || sb.search2(dInst.src2) || 
                                       sb.search3(dInst.dst);
    if (!stall) begin
      let rVal1 = rf.rd1(validRegValue(dInst.src1));
      let rVal2 = rf.rd2(validRegValue(dInst.src2));  
      i2e.enq (Issue2Execute{pc: pc, ppc: ppc, epoch: epoch, dInst: dInst, rVal1: rVal1, rVal2: rVal2});
      sb.insert(dInst.dst);
      d2i.deq;
    end
  endrule

  rule doExecute(cop.started && i2e.notEmpty);
    let pc = i2e.first.pc;
    let ppc = i2e.first.ppc;
    let inEp = i2e.first.epoch;
    let dInst = i2e.first.dInst;
    let rVal1 = i2e.first.rVal1;
    let rVal2 = i2e.first.rVal2;

    if (inEp == eEpoch) begin   
      $display("pc: %h: R1: %h R2: %h", pc, rVal1, rVal2);

      let copVal = cop.rd(validRegValue(dInst.src1));

      let eInst = exec(dInst, rVal1, rVal2, pc, ppc, copVal);

      if(eInst.iType == Unsupported) begin
        $fwrite(stderr, "Executing unsupported instruction at pc: %x. Exiting\n", pc);
        $finish;
      end

      if(eInst.iType == Ld) begin
        dMem.req.put(MemReq{op: Ld, addr: eInst.addr, data: ?});
      end else if(eInst.iType == St) begin
        dMem.req.put(MemReq{op: St, addr: eInst.addr, data: eInst.data});
      end

      if (eInst.mispredict) begin
        let newEpoch = eEpoch + 1;
        eEpoch <= newEpoch;
        execRedirect.enq (ExecuteRedirect{pc: eInst.addr, epoch: newEpoch});
      end

      e2m.enq (Execute2Memory{eInst: eInst});
    end

    i2e.deq;
  endrule

  rule doMemory(cop.started && e2m.notEmpty);
    let eInst = e2m.first.eInst;

    if (eInst.iType == Ld) begin
      eInst.data <- dMem.resp.get();
    end

    m2w.enq (Memory2WriteBack{eInst: eInst});
    e2m.deq;
  endrule

  rule doWriteBack(cop.started && m2w.notEmpty);
    let eInst = m2w.first.eInst;

    if (isValid(eInst.dst) && validValue(eInst.dst).regType == Normal) begin
      rf.wr(validRegValue(eInst.dst), eInst.data);
    end

    cop.wr(eInst.dst, eInst.data);
    m2w.deq;
    sb.remove;
  endrule
  
  method ActionValue#(Tuple2#(RIndx, Data)) cpuToHost;
    let ret <- cop.cpuToHost;
    return ret;
  endmethod

  method Action hostToCpu(Bit#(32) startpc) if (!cop.started && memReady);
    cop.start;
    pc <= startpc;
  endmethod

  interface MemInit iMemInit = iMem.init;
  interface MemInit dMemInit = dMem.init;
endmodule

