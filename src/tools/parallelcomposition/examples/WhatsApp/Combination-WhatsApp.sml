open HolKernel Parse
open binariesLib;
open WhatsAppTheory;
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
open sapic_to_fileLib;
open bir_symbexec_loopLib;
open bir_inst_liftingHelpersLib;

val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl)
      (DB.fetch "WhatsApp" "WhatsApp_session_cipher_encrypt_thm");
    
val bl_dict_    = gen_block_dict prog_tm;
val prog_lbl_tms_ = get_block_dict_keys bl_dict_;

val prog_vars = gen_vars_of_prog prog_tm;
    
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;

val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;    
 (*   
val n = { CFGN_lbl_tm   =  ``BL_Address (Imm64 0x102A0A4E8w)``,
	  CFGN_hc_descr = SOME " ",
	  CFGN_targets  = [],
	  CFGN_type     = CFGNT_Halt
	} : cfg_node;

    
val n_dict = Redblackmap.insertList (n_dict, [(``BL_Address (Imm64 0x102A0A4E8w)``,n)]);

val n = { CFGN_lbl_tm   =  ``BL_Address (Imm64 0x102AEDD0Cw)``,
	  CFGN_hc_descr = SOME " ",
	  CFGN_targets  = [],
	  CFGN_type     = CFGNT_Halt
	} : cfg_node;

    
val n_dict = Redblackmap.insertList (n_dict, [(``BL_Address (Imm64 0x102AEDD0Cw)``,n)]);

val n = { CFGN_lbl_tm   =  ``BL_Address (Imm64 0x102AEECC0w)``,
	  CFGN_hc_descr = SOME " ",
	  CFGN_targets  = [],
	  CFGN_type     = CFGNT_Halt
	} : cfg_node;

    
val n_dict = Redblackmap.insertList (n_dict, [(``BL_Address (Imm64 0x102AEECC0w)``,n)]);

val n = { CFGN_lbl_tm   =  ``BL_Address (Imm64 0x102C598E0w)``,
	  CFGN_hc_descr = SOME " ",
	  CFGN_targets  = [],
	  CFGN_type     = CFGNT_Halt
	} : cfg_node;

    
val n_dict = Redblackmap.insertList (n_dict, [(``BL_Address (Imm64 0x102C598E0w)``,n)]);

val n = { CFGN_lbl_tm   =  ``BL_Address (Imm64 0x102C597C0w)``,
	  CFGN_hc_descr = SOME " ",
	  CFGN_targets  = [],
	  CFGN_type     = CFGNT_Halt
	} : cfg_node;

    
val n_dict = Redblackmap.insertList (n_dict, [(``BL_Address (Imm64 0x102C597C0w)``,n)]);
    
val n = { CFGN_lbl_tm   =  ``BL_Address (Imm64 0x102C5EEC0w)``,
	  CFGN_hc_descr = SOME " ",
	  CFGN_targets  = [],
	  CFGN_type     = CFGNT_Halt
	} : cfg_node;

    
val n_dict = Redblackmap.insertList (n_dict, [(``BL_Address (Imm64 0x102C5EEC0w)``,n)]);
 *)   


fun update_n_dict_ ([], n_dict) = n_dict
    | update_n_dict_ (((lbl_tm)::todo), n_dict) =
	  let
	    val n = { CFGN_lbl_tm   =  lbl_tm,
		  CFGN_hc_descr = SOME " ",
		  CFGN_targets  = [],
		  CFGN_type     = CFGNT_Halt
		} : cfg_node;
	    val n_dict' = if isSome (lookup_block_dict n_dict lbl_tm)
			  then
			      n_dict
			  else
			      Redblackmap.update (n_dict, lbl_tm, K (n));
			      
	  in
	    update_n_dict_ (todo, n_dict')
	  end;    

open binariesCfgVizLib;
open binariesDefsLib;
val g1 = cfg_create "toy" [lbl_tm] n_dict bl_dict_;
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val n_dict' = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));
val ns = List.map (valOf o (lookup_block_dict n_dict'))
		  (#CFGG_nodes g1);

(* val ns = (List.map (valOf o (lookup_block_dict (#CFGG_node_dict g1))) (#CFGG_nodes g1)); *)
val _ = bir_cfg_vizLib.cfg_display_graph_ns ns;
    

(* 
val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

 open HolKernel Parse;
    open binariesLib;
    open binariesTheory;
    open binariesCfgLib;
    open binariesMemLib;
    open bir_programSyntax;
    open bir_valuesSyntax;
    open bir_immSyntax;
    open bir_exec_typingLib;
    open bir_cfgLib;
    open bir_cfg_m0Lib;
    open bir_block_collectionLib;
    open bir_envSyntax;
    open bir_expSyntax;
    open bir_auxiliaryLib;
    open bir_immSyntax;
    open wordsSyntax;
    open String;
    open bir_program_labelsSyntax;
    open bir_block_collectionLib;
    open Redblackmap;
    open Term;

fun fun_address_dict (n:cfg_node) =
    let
        val lbl_tm   = #CFGN_lbl_tm n;
	val descr  = (valOf o #CFGN_hc_descr) n;
	val instrDes = (snd o (list_split_pred #" ") o explode) descr;
	   (* val _ = print ((implode instrDes) ^ "\n"); *)
	val name_adr = if (isPrefix "(bl " (implode instrDes))
		       then let
			       val fname = (implode o fst o (list_split_pred #">") o snd o (list_split_pred #"<")) instrDes;
			   in
			       (lbl_tm, fname)
			   end
		       else if (isPrefix "(blr " (implode instrDes))
		       then let
			       val fname = (implode o fst o (list_split_pred #")") o snd o (list_split_pred #" ")) instrDes;
			   in
			       (lbl_tm, fname)
			   end
		       else if (isPrefix "(b " (implode instrDes))
		       then let
			       val fname = if (isPrefix "(b <" (implode instrDes))
					   then
					       (implode o fst o (list_split_pred #">") o snd o (list_split_pred #"<")) instrDes
					   else
					       (implode o fst o (list_split_pred #")") o snd o (list_split_pred #" ")) instrDes
			   in
			       (lbl_tm, fname)
			   end
		       else (“BL_Address (Imm32 0w)”, " ");
    in
	name_adr
    end;

val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;
	    
	val g1 = cfg_create "toy" prog_lbl_tms_ n_dict bl_dict_;

	val n_dict = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));
	    
	val func_table = Redblackmap.mkDict Term.compare : (term, string) Redblackmap.dict;

orelse )
val n = snd(hd(Redblackmap.listItems n_dict))
	val fun_adr = (List.map (fn x => (fun_address_dict x)) (List.map snd (Redblackmap.listItems n_dict)));

	val func_table' = Redblackmap.insertList (func_table, fun_adr);
val instrDes = explode "(b <0x00ee61c0>)"
   


val lbl_tm = ``BL_Address (Imm64 0xEE60B4w)``;
val stop_lbl_tms = [``BL_Address (Imm64 0xEE6368w)``];
    (*

val loop_pattern = ["CFGNT_CondJump","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

val enter = find_loop n_dict adr_dict [lbl_tm] loop_pattern;

val adr_dict = Redblackmap.insert(adr_dict,enter,"loop"); 
*)
    
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;
val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms adr_dict [];
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

    
val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst))
                         systs_noassertfailed;


val tr = predlist_to_tree predlists;

val vals_list = bir_symbexec_treeLib.symb_execs_vals_term systs_noassertfailed [];
val sort_vals = bir_symbexec_sortLib.refine_symb_val_list vals_list;
    

val valtr =  tree_with_value tr sort_vals;

val _ = print "\n";     
val _ = print ("built a symbolic tree with value");
val _ = print "\n";


val sapic_process = sbir_tree_sapic_process sort_vals (purge_tree valtr);


val _ = print "\n";     
val _ = print ("sapic_process");
val _ = print "\n";
    
val _ =  ( write_sapic_to_file o process_to_string) sapic_process

val _ = print "\n";     
val _ = print ("wrote into file");
val _ = print "\n";



*)
