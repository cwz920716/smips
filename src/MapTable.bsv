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
import ROB::*;

typedef Bit#(6)  MIndx;

interface MapTable;
    method Action free( RIndx rindx, ROBIndx rename );
    method Action clear;
    method Action map( RIndx rindx, ROBIndx rename );
    method Maybe#(ROBIndx) rd1( RIndx rindx );
    method Maybe#(ROBIndx) rd2( RIndx rindx );
endinterface

module mkBypassMapTable( MapTable );
    Vector#(32, Ehr#(3, Maybe#(ROBIndx))) mtable <- replicateM(mkEhr(tagged Invalid));
/*
  rule print;
    // $display("MT------------------");
    for (MIndx i = 0; i < 32; i = i + 1) begin
      let name = (mtable[i])[0];
      // $display("MapTable[%h] v %b rob %h", i, isValid(name), validValue(name));
    end
  endrule
*/
    method Action free(RIndx rindx, ROBIndx rename);
        let name = (mtable[rindx])[1];
        if ( rindx != 0 && isValid(name) && rename == validValue(name) ) begin
            (mtable[rindx])[1] <= tagged Invalid;
        end
    endmethod

    method Action clear;
        for (MIndx i = 0; i < 32; i = i + 1) begin
            (mtable[i])[0] <= tagged Invalid;
        end
    endmethod

    method Action map(RIndx rindx, ROBIndx rename);
        if (rindx != 0) begin
            (mtable[rindx])[2] <= tagged Valid rename;
        end
    endmethod

    method Maybe#(ROBIndx) rd1(RIndx rindx) = (mtable[rindx])[2];
    method Maybe#(ROBIndx) rd2(RIndx rindx) = (mtable[rindx])[2];
endmodule
