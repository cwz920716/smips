
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
import ROB::*;

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
        Data copVal;
} Issue2Execute deriving (Bits);

typedef struct {
	Addr pc;
        IType iType;
        Maybe#(FullIndx) dst;
        Data data;
} Execute2Memory deriving (Bits);

typedef struct {
	Addr pc;
        Maybe#(FullIndx) dst;
        Data data;
} Memory2WriteBack deriving (Bits);

typedef struct {
	Addr pc;
        Epoch epoch;
} ExecuteRedirect deriving (Bits);

typedef enum {Fetch, Decode, Issue, Execute, Memory, WriteBack} State deriving (Bits, Eq);

(* synthesize *)
module [Module] mkProc(Proc);
  Reg#(Addr) fPc <- mkRegU;
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
    $display("FE pc: %h: epoch: %d Eepoch: %h\n", fPc, fEpoch, eEpoch);
    if (execRedirect.notEmpty) begin
      fEpoch <= execRedirect.first.epoch;
      fPc <= execRedirect.first.pc;
      execRedirect.deq;
    end else begin
      // switch to Get state
      let ppc = addrPred.predPc(fPc);
      fPc <= ppc;
      f2d.enq (Fetch2Decode {pc: fPc, ppc: ppc, epoch: fEpoch});
      iMem.req.put(MemReq{op: Ld, addr: fPc, data: ?});
    end
  endrule

  rule doDecode(cop.started && f2d.notEmpty);
    let inst <- iMem.resp.get();

    let pc = f2d.first.pc;
    let ppc = f2d.first.ppc;
    let epoch = f2d.first.epoch;
    let dInst = decode(inst);
    $display("DE pc: %h", pc);
    d2i.enq (Decode2Issue {pc: pc, ppc: ppc, epoch: epoch, dInst: dInst});
    f2d.deq;
  endrule

  rule doIssue(cop.started && d2i.notEmpty);
    let pc = d2i.first.pc;
    let ppc = d2i.first.ppc;
    let epoch = d2i.first.epoch;
    let dInst = d2i.first.dInst;

    let stall = sb.search1(dInst.src1) || sb.search2(dInst.src2) || sb.search3(dInst.dst);
    $display("IS pc: %h stall: %h R1: %d R2: %d Rd: %d", pc, stall, validRegValue(dInst.src1), validRegValue(dInst.src2), validRegValue(dInst.dst));

    if (!stall) begin
      let rVal1 = rf.rd1(validRegValue(dInst.src1));
      let rVal2 = rf.rd2(validRegValue(dInst.src2));  
      let copVal = cop.rd(validRegValue(dInst.src1));
      i2e.enq (Issue2Execute {pc: pc, ppc: ppc, epoch: epoch, dInst: dInst, rVal1: rVal1, rVal2: rVal2, copVal: copVal});
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
    let copVal = i2e.first.copVal;
    $display("EX pc: %h: R1: %d R2: %d Rd: %d", pc, validRegValue(dInst.src1), validRegValue(dInst.src2), validRegValue(dInst.dst));

    if (inEp == eEpoch) begin   
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
        execRedirect.enq (ExecuteRedirect {pc: eInst.addr, epoch: newEpoch});
      end

      e2m.enq (Execute2Memory{pc: pc, iType: eInst.iType, dst: eInst.dst, data: eInst.data});
    end else begin
      e2m.enq (Execute2Memory{pc: pc, iType: Nop, dst: Invalid, data: ?});
    end

    i2e.deq;
  endrule

  rule doMemory(cop.started && e2m.notEmpty);
    let iType = e2m.first.iType;
    let dst = e2m.first.dst;
    let data = e2m.first.data;
    let pc = e2m.first.pc;
    $display("MEM pc: %h", pc);

    if (iType == Ld) begin
      data <- dMem.resp.get();
    end

    m2w.enq (Memory2WriteBack {pc: pc, dst: dst, data: data});
    e2m.deq;
  endrule

  rule doWriteBack(cop.started && m2w.notEmpty);
    let dst = m2w.first.dst;
    let data = m2w.first.data;
    let pc = m2w.first.pc;
    $display("WB pc: %h", pc);

    if (isValid(dst) && validValue(dst).regType == Normal) begin
      rf.wr(validRegValue(dst), data);
    end

    cop.wr(dst, data);
    m2w.deq;
    sb.remove;
  endrule
  
  method ActionValue#(Tuple2#(RIndx, Data)) cpuToHost;
    let ret <- cop.cpuToHost;
    return ret;
  endmethod

  method Action hostToCpu(Bit#(32) startpc) if (!cop.started && memReady);
    cop.start;
    fPc <= startpc;
  endmethod

  interface MemInit iMemInit = iMem.init;
  interface MemInit dMemInit = dMem.init;
endmodule

