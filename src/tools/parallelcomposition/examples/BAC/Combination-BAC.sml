open HolKernel Parse
open binariesLib;
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
open bossLib;
open PPBackEnd;
open boolLib pairLib;
open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;
open bir_obs_modelTheory;
open bir_obs_modelLib;
open AliceTheory;
    
val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl)
  (DB.fetch "Alice" "Alice_thm");
  
val prog_range       =  ((Arbnum.fromInt 0x690), (Arbnum.fromInt 0xBB1));

val entry = Arbnum.fromInt 0;
    
fun embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);

val stack_pointer_portion = Arbnum.fromHexString "0x0";    

val mem_bounds =
      let
        val (mem_base, mem_len) = prog_range;
	val mem_max = Arbnum.+ (mem_base, mem_len);
	val mem_end = (Arbnum.- (Arbnum.- (mem_max, stack_pointer_portion), Arbnum.fromInt 16));
	val (sp_start, sp_end) = (Arbnum.- (mem_max, stack_pointer_portion),
				  Arbnum.- (mem_max, Arbnum.fromInt 16));
      in
	if Arbnum.< (Arbnum.+ (mem_base,stack_pointer_portion), Arbnum.- (mem_max,stack_pointer_portion)) then
          pairSyntax.mk_pair
	    (pairSyntax.mk_pair
		 (wordsSyntax.mk_wordi (embexp_params_cacheable mem_base, 64),
		  wordsSyntax.mk_wordi (embexp_params_cacheable mem_end, 64)),
	     pairSyntax.mk_pair
		 (wordsSyntax.mk_wordi (embexp_params_cacheable sp_start, 64),
		  wordsSyntax.mk_wordi (embexp_params_cacheable sp_end, 64)))
	else
	  raise ERR "scamv_phase_add_obs" "the experiment memory is not properly set"
      end;
        
fun proginst_fun prog = inst [Type`:'observation_type` |-> Type`:bir_val_t`] prog;

val prog_w_obs = (#add_obs (get_obs_model "cache_speculation")) mem_bounds (proginst_fun prog_tm) entry;


val bl_dict_org    = gen_block_dict prog_tm;
val prog_lbl_tms_org = get_block_dict_keys bl_dict_org;
val n_dict_org = bir_cfgLib.cfg_build_node_dict bl_dict_org prog_lbl_tms_org;   
    
val bl_dict_spec    = gen_block_dict prog_w_obs;
val prog_lbl_tms_spec = get_block_dict_keys bl_dict_spec;
val n_dict_spec = bir_cfgLib.cfg_build_node_dict bl_dict_spec prog_lbl_tms_spec;

val prog_vars = gen_vars_of_prog prog_w_obs;
    
val adv_mem = “BVar "Adv_MEM" (BType_Mem Bit64 Bit8)”;

val prog_vars = adv_mem::prog_vars;

val bv_key = ``BVar "key" (BType_Imm Bit64)``;

val prog_vars = bv_key::prog_vars;

val op_mem = “BVar "Op_MEM" (BType_Mem Bit64 Bit8)”;

val prog_vars = op_mem::prog_vars;
    
val crypto = “BVar "Crypto" (BType_Imm Bit64)”;

val prog_vars = crypto::prog_vars;

val adr_dict = Redblackmap.mkDict Term.compare : (term, string) Redblackmap.dict;

val lbl_tm = ``BL_Address (Imm64 2440w)``;

val stop_lbl_tms = [``BL_Address (Imm64 2696w)``];
    
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val init_syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;
    
val systs = symb_exec_to_stop (abpfun cfb) n_dict_org bl_dict_spec [init_syst] stop_lbl_tms adr_dict [];

val _ = print "\n\n";
val _ = print "finished exploration of all paths.\n\n";
val _ = print ("number of stopped symbolic execution states: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
    List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed)));
val _ = print "\n";     
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n";
