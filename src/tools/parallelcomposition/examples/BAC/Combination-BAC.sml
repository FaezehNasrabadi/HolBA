open HolKernel Parse
open binariesLib;
open AliceObsTheory;
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_block_collectionLib;
open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_exec_typingLib;
open commonBalrobScriptLib;
open bir_cfgLib;
open bir_cfg_m0Lib;
open bir_symbexec_driverLib;
open Redblackmap;
open bir_symbexec_oracleLib;
open sbir_treeLib;
open sapicplusTheory;
open sapicplusSyntax;
open translate_to_sapicTheory;
open rich_listTheory;
open translate_to_sapicLib;
open messagesTheory;
open messagesSyntax;
open tree_to_processLib;
open  sapic_to_fileLib;
open bir_symbexec_loopLib;


val prog_w_obs =
  concl
      (DB.fetch "AliceObs" "Alice_Spec_Obs_thm");
(*    Error
val prog_bls = (fst o dest_list o is_BirProgram prog_w_obs ;*)
val bl_dict_    = gen_block_dict prog_w_obs;
val prog_lbl_tms_ = get_block_dict_keys bl_dict_;

val prog_vars = gen_vars_of_prog prog_w_obs;

val adv_mem = “BVar "Adv_MEM" (BType_Mem Bit64 Bit8)”;

val prog_vars = adv_mem::prog_vars;

val bv_key = ``BVar "key" (BType_Imm Bit64)``;

val prog_vars = bv_key::prog_vars;

val op_mem = “BVar "Op_MEM" (BType_Mem Bit64 Bit8)”;

val prog_vars = op_mem::prog_vars;
    
val crypto = “BVar "Crypto" (BType_Imm Bit64)”;

val prog_vars = crypto::prog_vars;
    
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;

val adr_dict = Redblackmap.mkDict Term.compare : (term, string) Redblackmap.dict;

val lbl_tm = ``BL_Address (Imm64 2440w)``;

val stop_lbl_tms = [``BL_Address (Imm64 2696w)``];
    
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val init_syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;
		 
val systs_run_a = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [init_syst] stop_lbl_tms adr_dict [];



