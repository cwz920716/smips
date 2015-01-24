
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

typedef UInt#(4) Epoch;

typedef struct {
	Addr pc;
	Addr ppc;
	Epoch epoch;
} Fetch2GetInst deriving (Bits);

typedef struct {
	Addr pc;
	Addr ppc;
	Epoch epoch;
	Data inst;
} GetInst2Execute deriving (Bits);

typedef struct {
	ExecInst eInst;
} Execute2WriteBack deriving (Bits);

typedef struct {
	Addr pc;
        Epoch epoch;
} ExecuteRedirect deriving (Bits);

typedef enum {Fetch, GetInst, Execute, WriteBack} State deriving (Bits, Eq);

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
  Fifo#(1, Fetch2GetInst) f2g <- mkPipelineFifo();
  Fifo#(1, GetInst2Execute) g2e <- mkPipelineFifo();
  Fifo#(1, Execute2WriteBack) e2w <- mkPipelineFifo();
  Fifo#(1, ExecuteRedirect) execRedirect <- mkBypassFifo();
  
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
      f2g.enq (Fetch2GetInst{pc: pc, ppc: ppc, epoch: fEpoch});
      iMem.req.put(MemReq{op: Ld, addr: pc, data: ?});
    end
  endrule

  rule doGetInst(cop.started && f2g.notEmpty);
    let inst <- iMem.resp.get();

    let pc = f2g.first.pc;
    let ppc = f2g.first.ppc;
    let epoch = f2g.first.epoch;
    g2e.enq (GetInst2Execute{pc: pc, ppc: ppc, epoch: epoch, inst: inst});
    f2g.deq;
  endrule

  rule doExecute(cop.started && g2e.notEmpty);
    let inst = g2e.first.inst;
    let pc = g2e.first.pc;
    let ppc = g2e.first.ppc;
    let inEp = g2e.first.epoch;

    if (inEp == eEpoch) begin
      let dInst = decode(inst);

      let rVal1 = rf.rd1(validRegValue(dInst.src1));
      let rVal2 = rf.rd2(validRegValue(dInst.src2));     
      $display("pc: %h: inst: %h R1: %h R2: %h", pc, inst, rVal1, rVal2);

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

      e2w.enq (Execute2WriteBack{eInst: eInst});
    end

    g2e.deq;
  endrule

  rule doWriteBack(cop.started && e2w.notEmpty);
    let eInst = e2w.first.eInst;

    Data data;
    if (eInst.iType != Ld) begin
      data = eInst.data;
    end else begin
      let memData <- dMem.resp.get();
      data = memData;
    end

    if (isValid(eInst.dst) && validValue(eInst.dst).regType == Normal) begin
      rf.wr(validRegValue(eInst.dst), data);
    end

    cop.wr(eInst.dst, data);
    e2w.deq;
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

