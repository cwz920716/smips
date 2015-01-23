
import Types::*;
import ProcTypes::*;
import MemTypes::*;
import RFile::*;
import IMemory::*;
import DMemory::*;
import Decode::*;
import Exec::*;
import Cop::*;
import GetPut::*;

typedef enum {Fetch1, Fetch2, Execute, Memory} State deriving (Bits, Eq);

(* synthesize *)
module [Module] mkProc(Proc);
  Reg#(Addr) pc <- mkRegU;
  RFile      rf <- mkRFile;
  IMemory  iMem <- mkIMemory;
  DMemory  dMem <- mkDMemory;
  Cop       cop <- mkCop;
  
  Reg#(State) state <- mkReg(Fetch1);
  Reg#(Data)     ir <- mkRegU;

  Bool memReady = iMem.init.done() && dMem.init.done();

  rule doFetch1(cop.started && state == Fetch1);
    iMem.req.put(MemReq{op: Ld, addr: pc, data: ?});

    // switch to execute state
    state <= Fetch2;
  endrule

  rule doFetch2(cop.started && state == Fetch2);
    let inst <- iMem.resp.get();

    $display("pc: %h inst: (%h) expanded: ", pc, inst, showInst(inst));

    // store the instruction in a register
    ir <= inst;

    // switch to execute state
    state <= Execute;
  endrule

  rule doExecute(cop.started && state == Execute);
    let inst = ir;

    let dInst = decode(inst);

    let rVal1 = rf.rd1(validRegValue(dInst.src1));
    let rVal2 = rf.rd2(validRegValue(dInst.src2));     

    let copVal = cop.rd(validRegValue(dInst.src1));

    let eInst = exec(dInst, rVal1, rVal2, pc, ?, copVal);

    if(eInst.iType == Unsupported)
    begin
      $fwrite(stderr, "Executing unsupported instruction at pc: %x. Exiting\n", pc);
      $finish;
    end

    if(eInst.iType == Ld)
    begin
      dMem.req.put(MemReq{op: Ld, addr: eInst.addr, data: ?});
      state <= Memory;
    end
    else if(eInst.iType == St)
    begin
      dMem.req.put(MemReq{op: St, addr: eInst.addr, data: eInst.data});
      state <= Fetch1;
    end
    else
    begin
      // switch back to fetch1
      state <= Fetch1;
    end

    if (isValid(eInst.dst) && validValue(eInst.dst).regType == Normal && eInst.iType != Ld)
      rf.wr(validRegValue(eInst.dst), eInst.data);

    pc <= eInst.brTaken ? eInst.addr : pc + 4;

    cop.wr(eInst.dst, eInst.data);
  endrule

  rule doMemory(cop.started && state == Memory);
    let inst = ir;

    let dInst = decode(inst);

    let data <- dMem.resp.get();

    if (isValid(dInst.dst) && validValue(dInst.dst).regType == Normal && dInst.iType == Ld)
      rf.wr(validRegValue(dInst.dst), data);

    // switch back to fetch1
    state <= Fetch1;

    cop.wr(dInst.dst, data);
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

