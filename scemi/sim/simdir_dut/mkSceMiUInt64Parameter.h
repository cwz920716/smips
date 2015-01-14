/*
 * Generated by Bluespec Compiler, version 2014.07.A (build 34078, 2014-07-30)
 * 
 * On Mon Dec 22 14:39:49 CST 2014
 * 
 */

/* Generation options: keep-fires */
#ifndef __mkSceMiUInt64Parameter_h__
#define __mkSceMiUInt64Parameter_h__

#include "bluesim_types.h"
#include "bs_module.h"
#include "bluesim_primitives.h"
#include "bs_vcd.h"


/* Class declaration for the mkSceMiUInt64Parameter module */
class MOD_mkSceMiUInt64Parameter : public Module {
 
 /* Clock handles */
 private:
 
 /* Clock gate handles */
 public:
  tUInt8 *clk_gate[0];
 
 /* Instantiation parameters */
 public:
  tUInt64 const PARAM_n;
 
 /* Module state */
 public:
 
 /* Constructor */
 public:
  MOD_mkSceMiUInt64Parameter(tSimStateHdl simHdl, char const *name, Module *parent, tUInt64 ARG_n);
 
 /* Symbol init methods */
 private:
  void init_symbols_0();
 
 /* Reset signal definitions */
 private:
 
 /* Port definitions */
 public:
  tUInt8 PORT_not_used;
  tUInt8 PORT_RDY_not_used;
 
 /* Publicly accessible definitions */
 public:
  tUInt8 DEF_CAN_FIRE_not_used;
 
 /* Local definitions */
 private:
 
 /* Rules */
 public:
 
 /* Methods */
 public:
  tUInt8 METH_not_used();
  tUInt8 METH_RDY_not_used();
 
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
  void dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_mkSceMiUInt64Parameter &backing);
  void vcd_defs(tVCDDumpType dt, MOD_mkSceMiUInt64Parameter &backing);
};

#endif /* ifndef __mkSceMiUInt64Parameter_h__ */
