
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
import MapTable::*;

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
} Decode2Reg deriving (Bits);

typedef struct {
	Addr pc;
	Addr ppc;
	Epoch epoch;
	DecodedInst dInst;
        Data rVal1;
        Data rVal2;
        Data copVal;
        ROBIndx indx;
} Issue2Execute deriving (Bits);

typedef struct {
	Addr pc;
	Addr ppc;
        Epoch epoch;
	ExecInst eInst;
        ROBIndx indx;
} Execute2Memory deriving (Bits);

typedef struct {
	Addr pc;
	Addr ppc;
        Epoch epoch;
	ExecInst eInst;
        ROBIndx indx;
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
  MapTable mapTable <- mkBypassMapTable;
  ROB rob <- mkPipelineROB;  

  Fifo#(1, Fetch2Decode) f2d <- mkPipelineFifo();
  Fifo#(1, Decode2Reg) d2r <- mkPipelineFifo();
  Fifo#(1, Issue2Execute) i2e <- mkPipelineFifo();
  Fifo#(1, Execute2Memory) e2m <- mkPipelineFifo();
  Fifo#(1, Memory2WriteBack) m2w <- mkPipelineFifo();
  Fifo#(1, ExecuteRedirect) commitRedirect <- mkBypassFifo();
  Fifo#(1, ExecuteRedirect) regRedirect <- mkBypassFifo();
  
  Reg#(Epoch) fEpoch <- mkReg(0);
  Reg#(Epoch) rEpoch <- mkReg(0);
  Reg#(Epoch) eEpoch <- mkReg(0);

  Bool memReady = iMem.init.done() && dMem.init.done();

  rule doFetch(cop.started);
    // $display("FE pc: %h: epoch: %d Eepoch: %h\n", fPc, fEpoch, eEpoch);
    if (commitRedirect.notEmpty) begin
      fEpoch <= commitRedirect.first.epoch;
      fPc <= commitRedirect.first.pc;
      commitRedirect.deq;
    end else begin
      // switch to Get state
      let ppc = addrPred.predPc(fPc);
      $display("FE pc: %h: ppc: %h\n", fPc, ppc);
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

    f2d.deq;
    d2r.enq(Decode2Reg {pc: pc, ppc: ppc, epoch: epoch, dInst: dInst} );
  endrule

  rule doReg(cop.started && d2r.notEmpty);
    let pc = d2r.first.pc;
    let ppc = d2r.first.ppc;
    let epoch = d2r.first.epoch;
    let dInst = d2r.first.dInst;

    $display("try RE pc: %h redirect: %b now.epoch %h ?= eEpoch %h", pc, regRedirect.notEmpty, epoch, rEpoch);

    if (regRedirect.notEmpty) begin
      rEpoch <= regRedirect.first.epoch;
      regRedirect.deq;
    end else begin

      if (epoch == rEpoch) begin

        // Do some read stuff
        let name1 = mapTable.rd1(validRegValue(dInst.src1));
        let sb1 = rob.rdExecData1( validValue(name1) );
        let rVal1 = rf.rd1(validRegValue(dInst.src1));
        let r1busy = tagged Invalid;
        if ( isValid(dInst.src1) && isValid(name1) ) begin
          if (isValid(sb1)) begin
            rVal1 = validValue(sb1);
          end else begin
            rVal1 = ?;
            r1busy = tagged Valid validValue(name1);
          end
        end

        let name2 = mapTable.rd2(validRegValue(dInst.src2));
        let sb2 = rob.rdExecData2( validValue(name2) );
        let rVal2 = rf.rd2(validRegValue(dInst.src2));
        let r2busy = tagged Invalid;
        if ( isValid(dInst.src2) && isValid(name2) ) begin
          if (isValid(sb2)) begin
            rVal2 = validValue(sb2);
          end else begin
            rVal2 = ?;
            r2busy = tagged Valid validValue(name2);
          end
        end

        let copVal = cop.rd(validRegValue(dInst.src1));

        let robR1busy = r1busy;
        let robRVal1 = rVal1;
        let robR2busy = r2busy;
        let robRVal2 = rVal2;
        let robCopVal = copVal;

        Bool isMem = (dInst.iType == Ld) || (dInst.iType == St);
        Bool stall = rob.existStore && isMem;

        $display("RE pc: %h stall: %b R1busy: %b R2Busy: %b", pc, stall, isValid(robR1busy), isValid(robR2busy));
        if (!stall && rob.notFull) begin
          let nextEntry = rob.nextEntry;
          if (isValid(dInst.dst))
            mapTable.map( validRegValue(dInst.dst), nextEntry );
            rob.enq(ROBEntry {pc: pc, ppc: ppc, epoch: epoch, dInst: dInst, r1busy: robR1busy, 
                              r2busy: robR2busy, rVal1: robRVal1, rVal2: robRVal2, copVal: robCopVal, eInst: ? } );
            $display("ROB enq %h", nextEntry);
            d2r.deq;
        end

      end else begin
        d2r.deq;
      end

    end

  endrule

  rule doIssue(cop.started);
    let readyIndx = rob.readyIdx;
    ROBIndx indx = validValue(readyIndx);
    ROBEntry entry = rob.readyEntry( indx );
    $display("try IS: %b %h", isValid(readyIndx), validValue(readyIndx));

    if ( isValid(readyIndx) ) begin
      rob.issue( indx );
      i2e.enq(Issue2Execute { pc: entry.pc, ppc: entry.ppc, epoch: entry.epoch, dInst: entry.dInst,
                                     rVal1: entry.rVal1, rVal2: entry.rVal2, copVal: entry.copVal, indx: indx});
      $display("IS pc: %h", entry.pc);
    end
  endrule

  rule doExecute(cop.started && i2e.notEmpty);
    let pc = i2e.first.pc;
    let ppc = i2e.first.ppc;
    let epoch = i2e.first.epoch;
    let inEp = i2e.first.epoch;
    let dInst = i2e.first.dInst;
    let rVal1 = i2e.first.rVal1;
    let rVal2 = i2e.first.rVal2;
    let copVal = i2e.first.copVal;
    let indx = i2e.first.indx;
    $display("EX pc: %h: R1: %d R2: %d Rd: %d", pc, validRegValue(dInst.src1), validRegValue(dInst.src2), validRegValue(dInst.dst));

    let eInst = exec(dInst, rVal1, rVal2, pc, ppc, copVal);

    if(eInst.iType == Unsupported) begin
      $fwrite(stderr, "Executing unsupported instruction at pc: %x. Exiting\n", pc);
      // $finish;
    end

    if(eInst.iType == Ld) begin
      dMem.req.put(MemReq{op: Ld, addr: eInst.addr, data: ?});
    end else if(eInst.iType == St) begin
      // dMem.req.put(MemReq{op: St, addr: eInst.addr, data: eInst.data});
    end
    e2m.enq (Execute2Memory{pc: pc, ppc: ppc, epoch: epoch, eInst: eInst, indx: indx});

    i2e.deq;
  endrule

  rule doMemory(cop.started && e2m.notEmpty);
    let pc = e2m.first.pc;
    let ppc = e2m.first.ppc;
    let epoch = e2m.first.epoch;
    let eInst = e2m.first.eInst;
    let indx = e2m.first.indx;
    $display("MEM pc: %h", pc);

    if (eInst.iType == Ld) begin
      let data <- dMem.resp.get();
      eInst.data = data;
    end

    m2w.enq (Memory2WriteBack {pc: pc, ppc: ppc, epoch: epoch, eInst: eInst, indx: indx});
    e2m.deq;
  endrule

  rule doWriteBack(cop.started && m2w.notEmpty);
    let pc = m2w.first.pc;
    let ppc = m2w.first.ppc;
    let epoch = m2w.first.epoch;
    let eInst = m2w.first.eInst;
    let indx = m2w.first.indx;
    $display("WB pc: %h", pc);

    rob.commit( indx, eInst );
    m2w.deq;
  endrule

  rule doCommit(cop.started && rob.notEmpty);
    Maybe#(ROBEntry) committedEntry = rob.first;
    let deqP = rob.firstIndx;
    if ( isValid(committedEntry) ) begin
      let centry = validValue(committedEntry);
      $display("CM pc: %h mispred %b deqP %h now.epoch %h ?= eEpoch %h", centry.pc, centry.eInst.mispredict, deqP, centry.epoch, eEpoch);
      if (centry.epoch == eEpoch) begin 
        let eInst = centry.eInst;
        if (isValid(eInst.dst) && validValue(eInst.dst).regType == Normal) begin
          $display("CM ARF[%h] <- %h", validRegValue(eInst.dst), eInst.data);
          rf.wr(validRegValue(eInst.dst), eInst.data);
        end
        cop.wr(eInst.dst, eInst.data);
        if(eInst.iType == St) begin
          dMem.req2.put(MemReq{op: St, addr: centry.eInst.addr, data: centry.eInst.data});
        end

        if (eInst.mispredict) begin
          let newEpoch = eEpoch + 1;
          eEpoch <= newEpoch;
          commitRedirect.enq (ExecuteRedirect {pc: eInst.addr, epoch: newEpoch});
          regRedirect.enq (ExecuteRedirect {pc: eInst.addr, epoch: newEpoch});
          mapTable.clear;
        end else begin
          if (isValid(eInst.dst) && validValue(eInst.dst).regType == Normal) begin
            mapTable.free(validRegValue(eInst.dst), deqP);
          end
        end
      end
      rob.deq;
    end
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

