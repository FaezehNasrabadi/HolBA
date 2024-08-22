open HolKernel Parse
open binariesLib;
open WhatsApp_session_cipher_encryptTheory;
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
     
val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl)
      (DB.fetch "WhatsApp_session_cipher_encrypt" "WhatsApp_session_cipher_encrypt_thm");
    
val bl_dict_    = gen_block_dict prog_tm;
val prog_lbl_tms_ = get_block_dict_keys bl_dict_;

val prog_vars = gen_vars_of_prog prog_tm;

val adv_mem = “BVar "Adv_MEM" (BType_Mem Bit64 Bit8)”;

val prog_vars = adv_mem::prog_vars;

val bv_key = ``BVar "key" (BType_Imm Bit64)``;

val prog_vars = bv_key::prog_vars;

val op_mem = “BVar "Op_MEM" (BType_Mem Bit64 Bit8)”;

val prog_vars = op_mem::prog_vars;
    
val crypto = “BVar "Crypto" (BType_Imm Bit64)”;

val prog_vars = crypto::prog_vars;
    
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;

    

    
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
   
 
    (*

val loop_pattern = ["CFGNT_CondJump","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

val enter = find_loop n_dict adr_dict [lbl_tm] loop_pattern;

val adr_dict = Redblackmap.insert(adr_dict,enter,"loop"); 

val stop_lbl_tms = [``BL_Address (Imm64 0x1309AC4w)``,``BL_Address (Imm64 0x12FCEACw)``,``BL_Address (Imm64 0x12E65D0w)``,``BL_Address (Imm64 0x12CE4B4w)``,``BL_Address (Imm64 0xEE8AB0w)``,``BL_Address (Imm64 0xEE8A90w)``,``BL_Address (Imm64 0xEE8A70w)``,``BL_Address (Imm64 0xEE2398w)``,``BL_Address (Imm64 0xEE2320w)``,``BL_Address (Imm64 0xEDE1CCw)``,``BL_Address (Imm64 0xEDCE78w)``,``BL_Address (Imm64 0xEDCE6Cw)``,``BL_Address (Imm64 0xED4874w)``,``BL_Address (Imm64 0xED481Cw)``,``BL_Address (Imm64 0xED4898w)``,``BL_Address (Imm64 0x12BA3C4w)``];
*)

val lbl_tm = ``BL_Address (Imm64 0xED4898w)``;

val bl = (valOf o (lookup_block_dict bl_dict_)) lbl_tm;
	     val (lbl_block_tm, stmts, est) = dest_bir_block bl;
val bl_dict_ = update_bl_dict_ ([lbl_tm],bl_dict_)
 

fun update_bl_dict_ ([], bl_dict) = bl_dict
    | update_bl_dict_ (((lbl_tm)::todo), bl_dict) =
	  let
	    
	    val bl_dict' = if isSome (lookup_block_dict bl_dict lbl_tm)
			  then
			      bl_dict
			  else
let val n =  “<|bb_label :=
                  BL_Address_HC (Imm64 0xED4898w) "140F454F (b 0x012ba59c)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 0x12BA59Cw)))|>”
in
			      Redblackmap.update (bl_dict, lbl_tm, K (n))
end;
			      
	  in
	    update_bl_dict_ (todo, bl_dict')
	  end; 


val lbl_tm = ``BL_Address (Imm64 0xED4898w)``;

val bl_dict_ = update_bl_dict_ ([lbl_tm],bl_dict_)

lookup_block_dict adr_dict ``BL_Address (Imm64 0xEE6320w)``
*)
val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;
      
val lbl_tm = ``BL_Address (Imm64 0xEE60B4w)``;
(* val lbl_tm = ``BL_Address (Imm64 0xEE6118w)``; 
``BL_Address (Imm64 0xEE61C0w)``*)
    (* val lbl_tm = ``BL_Address (Imm64 0xEE629Cw)``; *)
val stop_lbl_tms = [``BL_Address (Imm64 0x1309AC4w)``,
		      ``BL_Address (Imm64 0x12E65D0w)``,
		      ``BL_Address (Imm64 0x12CE4B4w)``,
		      ``BL_Address (Imm64 0xEE8AB0w)``,
		      ``BL_Address (Imm64 0xEE8A90w)``,
		      ``BL_Address (Imm64 0xEE8A70w)``,
		      ``BL_Address (Imm64 0xEE2398w)``,
		      ``BL_Address (Imm64 0xEE2320w)``,
		      ``BL_Address (Imm64 0xEDE1CCw)``,
		      ``BL_Address (Imm64 0xEDCE78w)``,
		      ``BL_Address (Imm64 0xEDCE6Cw)``,
		      ``BL_Address (Imm64 0xED4874w)``,
		      ``BL_Address (Imm64 0xED481Cw)``,
		      ``BL_Address (Imm64 0xED4898w)``,
		      ``BL_Address (Imm64 0x12BA3C4w)``,
		      ``BL_Address (Imm64 0x12BDFE8w)``,
		      ``BL_Address (Imm64 0xEE636Cw)``,
		      ``BL_Address (Imm64 0xEEA368w)``,
		      ``BL_Address (Imm64 0xEEA36Cw)``,
		      ``BL_Address (Imm64 0x12BA8C4w)``,
		      ``BL_Address (Imm64 0xEE61C0w)``,
		      ``BL_Address (Imm64 0xEE61D0w)``,
		      ``BL_Address (Imm64 0xEE9064w)``];
    
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;

val g1 = cfg_create "toy" [lbl_tm] n_dict bl_dict_;

val n_dict = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));
    
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

val _ = print "Get predlists";
val _ = print "\n";
    
val tree = predlist_to_tree predlists;

val _ = print "Get tree";
val _ = print "\n";
    
val vals_list = bir_symbexec_treeLib.symb_execs_vals_term systs_noassertfailed [];

val _ = print "Get vals_list";
val _ = print "\n";
	
val sort_vals = bir_symbexec_sortLib.refine_symb_val_list vals_list;

val _ = print "Get sort_vals";
val _ = print "\n";    

val valtr =  tree_with_value tree sort_vals;
     
val _ = print ("built a symbolic tree with value");
val _ = print "\n";


val sapic_process = sbir_tree_sapic_process sort_vals (purge_tree valtr);

    
val _ = print ("built sapic_process");
val _ = print "\n";
    
val _ =  ( write_sapic_to_file o process_to_string) sapic_process
     
val _ = print ("wrote into file");
val _ = print "\n";

