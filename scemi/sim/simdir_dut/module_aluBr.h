/*
 * Generated by Bluespec Compiler, version 2014.07.A (build 34078, 2014-07-30)
 * 
 * On Mon Dec 22 14:39:49 CST 2014
 * 
 */

/* Generation options: keep-fires */
#ifndef __module_aluBr_h__
#define __module_aluBr_h__

#include "bluesim_types.h"
#include "bs_module.h"
#include "bluesim_primitives.h"
#include "bs_vcd.h"


/* Class declaration for the module_aluBr module */
class MOD_module_aluBr : public Module {
 
 /* Clock handles */
 private:
 
 /* Clock gate handles */
 public:
  tUInt8 *clk_gate[0];
 
 /* Instantiation parameters */
 public:
 
 /* Module state */
 public:
 
 /* Constructor */
 public:
  MOD_module_aluBr(tSimStateHdl simHdl, char const *name, Module *parent);
 
 /* Symbol init methods */
 private:
  void init_symbols_0();
 
 /* Reset signal definitions */
 private:
 
 /* Port definitions */
 public:
  tUInt32 PORT_aluBr_a;
  tUInt32 PORT_aluBr_b;
  tUInt8 PORT_aluBr_brFunc;
  tUInt8 PORT_aluBr;
  tUInt8 PORT_RDY_aluBr;
 
 /* Publicly accessible definitions */
 public:
  tUInt8 DEF_CAN_FIRE_aluBr;
 
 /* Local definitions */
 private:
 
 /* Rules */
 public:
 
 /* Methods */
 public:
  tUInt8 METH_aluBr(tUInt32 ARG_aluBr_a, tUInt32 ARG_aluBr_b, tUInt8 ARG_aluBr_brFunc);
  tUInt8 METH_RDY_aluBr();
 
 /* Reset routines */
 public:
 
 /* Static handles to reset routines */
 public:
 
 /* Pointers to reset fns in parent module for asserting output resets */
 private:
 
 /* Functions for the parent module to register its reset fns */
 public:
 
 /* Functions to set the elaborated clock id */
 public:
 
 /* State dumping routine */
 public:
  void dump_state(unsigned int indent);
 
 /* VCD dumping routines */
 public:
  unsigned int dump_VCD_defs(unsigned int levels);
  void dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_module_aluBr &backing);
  void vcd_defs(tVCDDumpType dt, MOD_module_aluBr &backing);
};

#endif /* ifndef __module_aluBr_h__ */
