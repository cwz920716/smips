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

typedef Bit#(4)  ROBIndx;

typedef struct {
// enq data
  Addr             pc;
  Addr             ppc;
  Epoch            epoch;
  DecodedInst      dInst;
// (possibly) propogate data
  Maybe#(ROBIndx)  r1busy;
  Maybe#(ROBIndx)  r2busy;
  Maybe#(Data)     rVal1;
  Maybe#(Data)     rVal2;
// commit data
  ExecInst         eInst;
} ROBEntry deriving(Bits, Eq);

interface ROB;
  method Bool notFull;
  method Action enq(ROBEntry x);
  method Bool notEmpty;
  method Action deq;
  method ROBEntry first;
  method Action clear;
  method ROBEntry readyEntry;
  method ROBIndx readyIdx;
  method Action issue( ROBIndx idx );
  method Action commit( ROBIndx idx, ExecInst eInst );
endinterface

module mkPipelineROB( ROB ) ;
  ROBIndx nb = fromInteger(4);
  ROBIndx n2 = 2*nb;
  Vector#(8, Ehr#(2, ROBEntry)) data <- replicateM(mkEhr(?));
  Ehr#(2, ROBIndx) enqP <- mkEhr(0);
  Ehr#(2, ROBIndx) deqP <- mkEhr(0);

  ROBIndx cnt0 = enqP[0] >= deqP[0]? enqP[0] - deqP[0]:
                                       (enqP[0]%nb + nb) - deqP[0]%nb;
  ROBIndx cnt1 = enqP[0] >= deqP[1]? enqP[0] - deqP[1]:
                                       (enqP[0]%nb + nb) - deqP[1]%nb;

  method Bool notFull = cnt1 < nb;

  method Action enq(ROBEntry x) if(cnt1 < nb);
    enqP[0] <= (enqP[0] + 1)%n2;
    data[enqP[0]%nb][0] <= x;
  endmethod

  method Bool notEmpty = cnt0 != 0;

  method Action deq if(cnt0 != 0);
    deqP[0] <= (deqP[0] + 1)%n2;
  endmethod

  method ROBEntry first if(cnt0 != 0);
    return data[deqP[0]%nb][0];
  endmethod

  method Action clear;
    enqP[1] <= 0;
    deqP[1] <= 0;
  endmethod

  method ROBEntry readyEntry;
    return data[deqP[0]%nb][0];
  endmethod

  method ROBIndx readyIdx;
    return deqP[0];
  endmethod

  method Action issue( ROBIndx idx );
  endmethod

  method Action commit( ROBIndx idx, ExecInst eInst );
  endmethod

endmodule
