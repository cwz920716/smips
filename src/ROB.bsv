/*

Copyright (C) 2012 Muralidaran Vijayaraghavan <vmurali@csail.mit.edu>

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and associated documentation files (the "Software"), to deal in the Software without restriction, including without limitation the rights to use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

*/


// Correct use of the register file implies that the same index can't be used for simultaneous read and write from different rules. If different indices are used reads and writes are conflict free. If the reads and writes are in the same rule, write updates the file at the end of the rule.
// We have imitated this conflict free behavior using config regs.
// If we had used ordinary registers, then read<write
// In many designs where we needed Bypass register file, the bypassing was implemented outside the register file, explicitly.


import Types::*;
import ProcTypes::*;
import Vector::*;
import Ehr::*;
import ConfigReg::*;

typedef UInt#(4) Epoch;

typedef Bit#(5)  ROBIndx;

typedef struct {
// enq data
  Addr             pc;
  Addr             ppc;
  Epoch            epoch;
  DecodedInst      dInst;
// (possibly) propogate data
  Maybe#(ROBIndx)  r1busy;
  Maybe#(ROBIndx)  r2busy;
  Data             rVal1;
  Data             rVal2;
// commit data
  ExecInst         eInst;
} ROBEntry deriving(Bits, Eq);

function ROBIndx validRobValue(Maybe#(ROBIndx) idx) = validValue(idx);

interface ROB;
  method Bool notFull;
  method ROBIndx nextEntry;
  method Action enq(ROBEntry x);
  method Bool notEmpty;
  method Action deq;
  method ROBEntry first;
  method Action clear;
  method ROBEntry readyEntry( ROBIndx idx );
  method Maybe#(Data) rdExecData1( ROBIndx idx );
  method Maybe#(Data) rdExecData2( ROBIndx idx );
  method Bool existStore;
  method Maybe#(ROBIndx) readyIdx;
  method Action issue( ROBIndx idx );
  method Action commit( ROBIndx idx, ExecInst eInst );
endinterface

// {notEmpty, first} < deq < commit < {readyEntry, readyIdx} < issue < {rd1, rd2, notFull, nextEntry} < enq < clear

module mkPipelineROB( ROB ) ;
  ROBIndx nb = fromInteger(8);
  ROBIndx n2 = 2*nb;
  Vector#(8, Ehr#(2, ROBEntry)) data <- replicateM(mkEhr(?));
  Vector#(8, Ehr#(3, Bool)) valid <- replicateM( mkEhr(False) );
  Vector#(8, Ehr#(2, Bool)) issued <- replicateM( mkEhr(False) );
  Vector#(8, Ehr#(2, Bool)) committed <- replicateM( mkEhr(False) );
  Ehr#(2, ROBIndx) enqP <- mkEhr(0);
  Ehr#(2, ROBIndx) deqP <- mkEhr(0);
  Ehr#(3, Bool) hasStore <- mkEhr(False);

  ROBIndx cnt0 = enqP[0] >= deqP[0]? enqP[0] - deqP[0]:
                                       (enqP[0]%nb + nb) - deqP[0]%nb;
  ROBIndx cnt1 = enqP[0] >= deqP[1]? enqP[0] - deqP[1]:
                                       (enqP[0]%nb + nb) - deqP[1]%nb;

  function Maybe#(ROBIndx) getReady();
    Maybe#(ROBIndx) ret = tagged Invalid;
    for (ROBIndx i = 0; i < 8; i = i + 1) begin
      if (valid[i][1] && !issued[i][0]) begin
        let rs = data[i][1]; // Reservation Station
        let dInst = rs.dInst;
        if ( !(isValid(dInst.src1) && isValid(rs.r1busy)) && !(isValid(dInst.src2) && isValid(rs.r2busy)) )
          ret = tagged Valid i;
      end
    end
    return ret;
  endfunction

  method Bool notFull = cnt1 < nb;

  method ROBIndx nextEntry if(cnt1 < nb);
    return enqP[0];
  endmethod

  method Action enq(ROBEntry x) if(cnt1 < nb);
    let next = enqP[0]%nb;
    enqP[0] <= (enqP[0] + 1)%n2;
    data[next][1] <= x;
    valid[next][1] <= True;
    issued[next][1] <= False;
    committed[next][1] <= False;
    if (x.dInst.iType == St)
      hasStore[1] <= True;
  endmethod

  method Bool notEmpty = cnt0 != 0;

  method Action deq if(cnt0 != 0);
    deqP[0] <= (deqP[0] + 1)%n2;
    valid[deqP[0]][0] <= False;
  endmethod

  method ROBEntry first if(cnt0 != 0);
    return data[deqP[0]%nb][0];
  endmethod

  method Action clear;
    enqP[1] <= 0;
    deqP[1] <= 0;
    for (int i = 0; i < 8; i = i + 1)
      valid[i][2] <= False;
    hasStore[2] <= False;
  endmethod

  method ROBEntry readyEntry( ROBIndx idx ) if(cnt0 != 0);
    return data[idx][1];
  endmethod

  method Maybe#(Data) rdExecData1( ROBIndx idx ) if(cnt0 != 0);
    Maybe#(Data) ret = tagged Invalid;
    if (valid[idx][1] && committed[idx][1])
      ret = tagged Valid data[idx][1].eInst.data;
    return ret;
  endmethod

  method Maybe#(Data) rdExecData2( ROBIndx idx ) if(cnt0 != 0);
    Maybe#(Data) ret = tagged Invalid;
    if (valid[idx][1] && committed[idx][1])
      ret = tagged Valid data[idx][1].eInst.data;
    return ret;
  endmethod

  method Bool existStore if(cnt0 != 0);
    return hasStore[1];
  endmethod

  method Maybe#(ROBIndx) readyIdx if(cnt0 != 0);
    return getReady();
  endmethod

  method Action issue( ROBIndx idx ) if(cnt0 != 0);
    issued[idx][0] <= True;
  endmethod

  method Action commit( ROBIndx idx, ExecInst eInst ) if(cnt0 != 0);
    for (ROBIndx i = 0; i < 8; i = i + 1) begin
      if (i == idx && valid[i][1] && issued[i][0] && !committed[i][0]) begin
        let cre = data[i][0];
        cre.eInst = eInst;
        data[i][0] <= cre;
        committed[i][0] <= True;
        if (cre.dInst.iType == St && hasStore[0])
          hasStore[0] <= False;
      end else if (i == idx && valid[i][1] && !issued[i][0]) begin
        let rs = data[i][0]; // Reservation Station
        let dInst = rs.dInst;
        if ( isValid(dInst.src1) && isValid(rs.r1busy) && validRobValue(rs.r1busy) == idx ) begin
          rs.rVal1 = eInst.data;
          rs.r1busy = tagged Invalid;
        end
        if ( isValid(dInst.src2) && isValid(rs.r2busy) && validRobValue(rs.r2busy) == idx ) begin
          rs.rVal2 = eInst.data;
          rs.r2busy = tagged Invalid;
        end         
        data[i][0] <= rs;
      end
    end
  endmethod

endmodule
