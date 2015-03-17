# smips
Out-of-Order SMIPS Processor in BSV

Author:

  Wenzhi Cui (skeleton code from MIT 6.375)

Includes:

  Re-order Buffer using Tomasulo’s Algorithm

  2-way simultaneous issue and write-back (one-way fetch and decode)

  Load/Store Queue

  A datapath for Load/Store

  A datapath for normal ALU
  
Benchmarks:

  ../../programs/build/median.bench.vmh

  Cycles = 16589

  Insts  = 6871

  PASSED

  SceMi Service thread finished!

  ../../programs/build/multiply.bench.vmh

  Cycles = 28290

  Insts  = 21098

  PASSED

  SceMi Service thread finished!

  ../../programs/build/qsort.bench.vmh

  Cycles = 40473

  Insts  = 21335

  PASSED

  SceMi Service thread finished!

  ../../programs/build/towers.bench.vmh

  Cycles = 34026

  Insts  = 9907

  PASSED

  SceMi Service thread finished!

  ../../programs/build/vvadd.bench.vmh

  Cycles = 4574

  Insts  = 3018

  PASSED

  SceMi Service thread finished!

