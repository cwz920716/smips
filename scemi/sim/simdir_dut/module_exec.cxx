/*
 * Generated by Bluespec Compiler, version 2014.07.A (build 34078, 2014-07-30)
 * 
 * On Mon Dec 22 14:39:49 CST 2014
 * 
 */
#include "bluesim_primitives.h"
#include "module_exec.h"


/* Constructor */
MOD_module_exec::MOD_module_exec(tSimStateHdl simHdl, char const *name, Module *parent)
  : Module(simHdl, name, parent),
    INST_instance_brAddrCalc_2(simHdl, "instance_brAddrCalc_2", this),
    INST_instance_alu_1(simHdl, "instance_alu_1", this),
    INST_instance_aluBr_0(simHdl, "instance_aluBr_0", this),
    DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32(66u)
{
  PORT_exec_dInst.setSize(65u);
  PORT_exec_dInst.clear();
  PORT_exec_rVal1 = 0u;
  PORT_exec_rVal2 = 0u;
  PORT_exec_pc = 0u;
  PORT_exec_ppc = 0u;
  PORT_exec_copVal = 0u;
  PORT_exec.setSize(77u);
  PORT_exec.clear();
  PORT_RDY_exec = false;
  symbol_count = 12u;
  symbols = new tSym[symbol_count];
  init_symbols_0();
}


/* Symbol init fns */

void MOD_module_exec::init_symbols_0()
{
  init_symbol(&symbols[0u], "CAN_FIRE_exec", SYM_DEF, &DEF_CAN_FIRE_exec, 1u);
  init_symbol(&symbols[1u], "exec", SYM_PORT, &PORT_exec, 77u);
  init_symbol(&symbols[2u], "exec_copVal", SYM_PORT, &PORT_exec_copVal, 32u);
  init_symbol(&symbols[3u], "exec_dInst", SYM_PORT, &PORT_exec_dInst, 65u);
  init_symbol(&symbols[4u], "exec_pc", SYM_PORT, &PORT_exec_pc, 32u);
  init_symbol(&symbols[5u], "exec_ppc", SYM_PORT, &PORT_exec_ppc, 32u);
  init_symbol(&symbols[6u], "exec_rVal1", SYM_PORT, &PORT_exec_rVal1, 32u);
  init_symbol(&symbols[7u], "exec_rVal2", SYM_PORT, &PORT_exec_rVal2, 32u);
  init_symbol(&symbols[8u], "instance_alu_1", SYM_MODULE, &INST_instance_alu_1);
  init_symbol(&symbols[9u], "instance_aluBr_0", SYM_MODULE, &INST_instance_aluBr_0);
  init_symbol(&symbols[10u], "instance_brAddrCalc_2", SYM_MODULE, &INST_instance_brAddrCalc_2);
  init_symbol(&symbols[11u], "RDY_exec", SYM_PORT, &PORT_RDY_exec, 1u);
}


/* Rule actions */


/* Methods */

tUWide MOD_module_exec::METH_exec(tUWide ARG_exec_dInst,
				  tUInt32 ARG_exec_rVal1,
				  tUInt32 ARG_exec_rVal2,
				  tUInt32 ARG_exec_pc,
				  tUInt32 ARG_exec_ppc,
				  tUInt32 ARG_exec_copVal)
{
  tUInt8 DEF_exec_dInst_BIT_53_CONCAT_IF_exec_dInst_BIT_53__ETC___d5;
  tUInt32 DEF_exec_pc_PLUS_4___d12;
  tUInt32 DEF_x__h171;
  tUInt32 DEF_x__h281;
  tUInt8 DEF_exec_dInst_BIT_32___d13;
  tUInt8 DEF_exec_dInst_BIT_53___d2;
  tUInt8 DEF_exec_dInst_BITS_52_TO_47___d3;
  tUInt32 DEF_exec_dInst_BITS_31_TO_0___d14;
  tUInt32 DEF_aluVal2__h29;
  tUInt32 DEF_aluRes__h30;
  tUInt8 DEF_aluBr___d26;
  tUInt32 DEF_IF_exec_dInst_BIT_32_3_THEN_exec_dInst_BITS_31_ETC___d15;
  tUInt8 DEF_exec_dInst_BITS_64_TO_61___d1;
  tUInt32 DEF_brAddr__h34;
  PORT_exec_dInst = ARG_exec_dInst;
  PORT_exec_rVal1 = ARG_exec_rVal1;
  PORT_exec_rVal2 = ARG_exec_rVal2;
  PORT_exec_pc = ARG_exec_pc;
  PORT_exec_ppc = ARG_exec_ppc;
  PORT_exec_copVal = ARG_exec_copVal;
  DEF_exec_dInst_BITS_64_TO_61___d1 = primExtract8(4u, 65u, ARG_exec_dInst, 32u, 64u, 32u, 61u);
  DEF_aluBr___d26 = INST_instance_aluBr_0.METH_aluBr(ARG_exec_rVal1,
						     ARG_exec_rVal2,
						     ARG_exec_dInst.get_bits_in_word8(1u, 22u, 3u));
  DEF_exec_dInst_BITS_31_TO_0___d14 = ARG_exec_dInst.get_whole_word(0u);
  DEF_exec_dInst_BITS_52_TO_47___d3 = ARG_exec_dInst.get_bits_in_word8(1u, 15u, 6u);
  DEF_exec_dInst_BIT_53___d2 = ARG_exec_dInst.get_bits_in_word8(1u, 21u, 1u);
  DEF_exec_dInst_BIT_32___d13 = ARG_exec_dInst.get_bits_in_word8(1u, 0u, 1u);
  DEF_IF_exec_dInst_BIT_32_3_THEN_exec_dInst_BITS_31_ETC___d15 = DEF_exec_dInst_BIT_32___d13 ? DEF_exec_dInst_BITS_31_TO_0___d14 : DEF_exec_dInst_BITS_31_TO_0___d14;
  DEF_brAddr__h34 = INST_instance_brAddrCalc_2.METH_brAddrCalc(ARG_exec_pc,
							       ARG_exec_rVal1,
							       DEF_exec_dInst_BITS_64_TO_61___d1,
							       DEF_IF_exec_dInst_BIT_32_3_THEN_exec_dInst_BITS_31_ETC___d15,
							       DEF_aluBr___d26);
  DEF_aluVal2__h29 = DEF_exec_dInst_BIT_32___d13 ? DEF_IF_exec_dInst_BIT_32_3_THEN_exec_dInst_BITS_31_ETC___d15 : ARG_exec_rVal2;
  DEF_aluRes__h30 = INST_instance_alu_1.METH_alu(ARG_exec_rVal1,
						 DEF_aluVal2__h29,
						 ARG_exec_dInst.get_bits_in_word8(1u, 25u, 4u));
  switch (DEF_exec_dInst_BITS_64_TO_61___d1) {
  case (tUInt8)2u:
  case (tUInt8)3u:
    DEF_x__h281 = DEF_aluRes__h30;
    break;
  default:
    DEF_x__h281 = DEF_brAddr__h34;
  }
  DEF_exec_pc_PLUS_4___d12 = ARG_exec_pc + 4u;
  switch (DEF_exec_dInst_BITS_64_TO_61___d1) {
  case (tUInt8)7u:
    DEF_x__h171 = ARG_exec_copVal;
    break;
  case (tUInt8)8u:
    DEF_x__h171 = ARG_exec_rVal1;
    break;
  case (tUInt8)3u:
    DEF_x__h171 = ARG_exec_rVal2;
    break;
  case (tUInt8)4u:
  case (tUInt8)5u:
    DEF_x__h171 = DEF_exec_pc_PLUS_4___d12;
    break;
  default:
    DEF_x__h171 = DEF_aluRes__h30;
  }
  DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32.set_bits_in_word((tUInt8)(DEF_x__h171 >> 30u),
										2u,
										0u,
										2u).set_whole_word((((tUInt32)(1073741823u & DEF_x__h171)) << 2u) | (tUInt32)((tUInt8)(DEF_x__h281 >> 30u)),
												   1u).set_whole_word(((((tUInt32)(1073741823u & DEF_x__h281)) << 2u) | (((tUInt32)(!(DEF_brAddr__h34 == ARG_exec_ppc))) << 1u)) | (tUInt32)(DEF_aluBr___d26),
														      0u);
  DEF_exec_dInst_BIT_53_CONCAT_IF_exec_dInst_BIT_53__ETC___d5 = (tUInt8)127u & ((DEF_exec_dInst_BIT_53___d2 << 6u) | (DEF_exec_dInst_BIT_53___d2 ? DEF_exec_dInst_BITS_52_TO_47___d3 : DEF_exec_dInst_BITS_52_TO_47___d3));
  PORT_exec.set_bits_in_word(8191u & (((((tUInt32)(DEF_exec_dInst_BITS_64_TO_61___d1)) << 9u) | (((tUInt32)(DEF_exec_dInst_BIT_53_CONCAT_IF_exec_dInst_BIT_53__ETC___d5)) << 2u)) | (tUInt32)(DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32.get_bits_in_word8(2u,
																																	     0u,
																																	     2u))),
			     2u,
			     0u,
			     13u).set_whole_word(DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32.get_whole_word(1u),
						 1u).set_whole_word(DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32.get_whole_word(0u),
								    0u);
  return PORT_exec;
}

tUInt8 MOD_module_exec::METH_RDY_exec()
{
  DEF_CAN_FIRE_exec = (tUInt8)1u;
  PORT_RDY_exec = DEF_CAN_FIRE_exec;
  return PORT_RDY_exec;
}


/* Reset routines */


/* Static handles to reset routines */


/* Functions for the parent module to register its reset fns */


/* Functions to set the elaborated clock id */


/* State dumping routine */
void MOD_module_exec::dump_state(unsigned int indent)
{
}


/* VCD dumping routines */

unsigned int MOD_module_exec::dump_VCD_defs(unsigned int levels)
{
  vcd_write_scope_start(sim_hdl, inst_name);
  vcd_num = vcd_reserve_ids(sim_hdl, 10u);
  unsigned int num = vcd_num;
  for (unsigned int clk = 0u; clk < bk_num_clocks(sim_hdl); ++clk)
    vcd_add_clock_def(sim_hdl, this, bk_clock_name(sim_hdl, clk), bk_clock_vcd_num(sim_hdl, clk));
  vcd_write_def(sim_hdl, num++, "CAN_FIRE_exec", 1u);
  vcd_write_def(sim_hdl, num++, "IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32", 66u);
  vcd_write_def(sim_hdl, num++, "RDY_exec", 1u);
  vcd_write_def(sim_hdl, num++, "exec", 77u);
  vcd_write_def(sim_hdl, num++, "exec_copVal", 32u);
  vcd_write_def(sim_hdl, num++, "exec_dInst", 65u);
  vcd_write_def(sim_hdl, num++, "exec_pc", 32u);
  vcd_write_def(sim_hdl, num++, "exec_ppc", 32u);
  vcd_write_def(sim_hdl, num++, "exec_rVal1", 32u);
  vcd_write_def(sim_hdl, num++, "exec_rVal2", 32u);
  if (levels != 1u)
  {
    unsigned int l = levels == 0u ? 0u : levels - 1u;
    num = INST_instance_aluBr_0.dump_VCD_defs(l);
    num = INST_instance_alu_1.dump_VCD_defs(l);
    num = INST_instance_brAddrCalc_2.dump_VCD_defs(l);
  }
  vcd_write_scope_end(sim_hdl);
  return num;
}

void MOD_module_exec::dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_module_exec &backing)
{
  vcd_defs(dt, backing);
  if (levels != 1u)
    vcd_submodules(dt, levels - 1u, backing);
}

void MOD_module_exec::vcd_defs(tVCDDumpType dt, MOD_module_exec &backing)
{
  unsigned int num = vcd_num;
  if (dt == VCD_DUMP_XS)
  {
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 66u);
    vcd_write_x(sim_hdl, num++, 1u);
    vcd_write_x(sim_hdl, num++, 77u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 65u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 32u);
    vcd_write_x(sim_hdl, num++, 32u);
  }
  else
    if (dt == VCD_DUMP_CHANGES)
    {
      if ((backing.DEF_CAN_FIRE_exec) != DEF_CAN_FIRE_exec)
      {
	vcd_write_val(sim_hdl, num, DEF_CAN_FIRE_exec, 1u);
	backing.DEF_CAN_FIRE_exec = DEF_CAN_FIRE_exec;
      }
      ++num;
      if ((backing.DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32) != DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32)
      {
	vcd_write_val(sim_hdl, num, DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32, 66u);
	backing.DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32 = DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32;
      }
      ++num;
      if ((backing.PORT_RDY_exec) != PORT_RDY_exec)
      {
	vcd_write_val(sim_hdl, num, PORT_RDY_exec, 1u);
	backing.PORT_RDY_exec = PORT_RDY_exec;
      }
      ++num;
      if ((backing.PORT_exec) != PORT_exec)
      {
	vcd_write_val(sim_hdl, num, PORT_exec, 77u);
	backing.PORT_exec = PORT_exec;
      }
      ++num;
      if ((backing.PORT_exec_copVal) != PORT_exec_copVal)
      {
	vcd_write_val(sim_hdl, num, PORT_exec_copVal, 32u);
	backing.PORT_exec_copVal = PORT_exec_copVal;
      }
      ++num;
      if ((backing.PORT_exec_dInst) != PORT_exec_dInst)
      {
	vcd_write_val(sim_hdl, num, PORT_exec_dInst, 65u);
	backing.PORT_exec_dInst = PORT_exec_dInst;
      }
      ++num;
      if ((backing.PORT_exec_pc) != PORT_exec_pc)
      {
	vcd_write_val(sim_hdl, num, PORT_exec_pc, 32u);
	backing.PORT_exec_pc = PORT_exec_pc;
      }
      ++num;
      if ((backing.PORT_exec_ppc) != PORT_exec_ppc)
      {
	vcd_write_val(sim_hdl, num, PORT_exec_ppc, 32u);
	backing.PORT_exec_ppc = PORT_exec_ppc;
      }
      ++num;
      if ((backing.PORT_exec_rVal1) != PORT_exec_rVal1)
      {
	vcd_write_val(sim_hdl, num, PORT_exec_rVal1, 32u);
	backing.PORT_exec_rVal1 = PORT_exec_rVal1;
      }
      ++num;
      if ((backing.PORT_exec_rVal2) != PORT_exec_rVal2)
      {
	vcd_write_val(sim_hdl, num, PORT_exec_rVal2, 32u);
	backing.PORT_exec_rVal2 = PORT_exec_rVal2;
      }
      ++num;
    }
    else
    {
      vcd_write_val(sim_hdl, num++, DEF_CAN_FIRE_exec, 1u);
      backing.DEF_CAN_FIRE_exec = DEF_CAN_FIRE_exec;
      vcd_write_val(sim_hdl, num++, DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32, 66u);
      backing.DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32 = DEF_IF_exec_dInst_BITS_64_TO_61_EQ_7_THEN_exec_cop_ETC___d32;
      vcd_write_val(sim_hdl, num++, PORT_RDY_exec, 1u);
      backing.PORT_RDY_exec = PORT_RDY_exec;
      vcd_write_val(sim_hdl, num++, PORT_exec, 77u);
      backing.PORT_exec = PORT_exec;
      vcd_write_val(sim_hdl, num++, PORT_exec_copVal, 32u);
      backing.PORT_exec_copVal = PORT_exec_copVal;
      vcd_write_val(sim_hdl, num++, PORT_exec_dInst, 65u);
      backing.PORT_exec_dInst = PORT_exec_dInst;
      vcd_write_val(sim_hdl, num++, PORT_exec_pc, 32u);
      backing.PORT_exec_pc = PORT_exec_pc;
      vcd_write_val(sim_hdl, num++, PORT_exec_ppc, 32u);
      backing.PORT_exec_ppc = PORT_exec_ppc;
      vcd_write_val(sim_hdl, num++, PORT_exec_rVal1, 32u);
      backing.PORT_exec_rVal1 = PORT_exec_rVal1;
      vcd_write_val(sim_hdl, num++, PORT_exec_rVal2, 32u);
      backing.PORT_exec_rVal2 = PORT_exec_rVal2;
    }
}

void MOD_module_exec::vcd_submodules(tVCDDumpType dt, unsigned int levels, MOD_module_exec &backing)
{
  INST_instance_aluBr_0.dump_VCD(dt, levels, backing.INST_instance_aluBr_0);
  INST_instance_alu_1.dump_VCD(dt, levels, backing.INST_instance_alu_1);
  INST_instance_brAddrCalc_2.dump_VCD(dt, levels, backing.INST_instance_brAddrCalc_2);
}
