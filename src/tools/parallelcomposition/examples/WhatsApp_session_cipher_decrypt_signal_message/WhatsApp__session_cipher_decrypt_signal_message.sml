open HolKernel Parse
open binariesLib;
open WhatsApp_session_cipher_decrypt_signal_messageTheory;
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
      (DB.fetch "WhatsApp_session_cipher_decrypt_signal_message" "WhatsApp_session_cipher_decrypt_signal_message_thm");
    
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

val ephemeral = “BVar "Ephemeral" (BType_Imm Bit64)”;

val prog_vars = ephemeral::prog_vars;
    
val root = “BVar "Root" (BType_Imm Bit64)”;

val prog_vars = root::prog_vars;


    
    
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;
  (*
val lbl_tm = ``BL_Address (Imm64 0xEE6A5Cw)``;
    
val g1 = cfg_create "toy1" [lbl_tm] n_dict bl_dict_;

val n_dict = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));
 
val g2 = cfg_create "toy2" [lbl_tm] n_dict bl_dict_;
    
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g2))) (#CFGG_nodes g2);
val _ = bir_cfg_vizLib.cfg_display_graph_ns ns;    
 
lookup_block_dict adr_dict ``BL_Address (Imm64 0xEE6320w)``

val lbl_tm = ``BL_Address (Imm64 0x12F85DCw)``
val bl = ((valOf o (lookup_block_dict bl_dict_)) lbl_tm) handle _ => ((valOf o (lookup_block_dict bl_dict_)) (bir_symbexec_loopLib.next_pc lbl_tm));
	     
val (lbl_block_tm, stmts, est) = dest_bir_block bl;

val loop_pattern = ["CFGNT_Basic","CFGNT_CondJump","CFGNT_Basic",
		    "CFGNT_Basic","CFGNT_Basic","CFGNT_Basic",
		    "CFGNT_Basic","CFGNT_CondJump","CFGNT_Call","CFGNT_CondJump",
		    "CFGNT_Basic","CFGNT_Call","CFGNT_Call","CFGNT_CondJump",
		    "CFGNT_Call","CFGNT_CondJump","CFGNT_Call","CFGNT_Basic",
		    "CFGNT_Basic","CFGNT_Basic","CFGNT_Jump"];

val loop_pattern = ["CFGNT_Call","CFGNT_Basic",
		    "CFGNT_Basic","CFGNT_Basic",
		    "CFGNT_Jump","CFGNT_Basic","CFGNT_CondJump"];

val loop_pattern = ["CFGNT_Basic","CFGNT_CondJump",
		    "CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic",
		    "CFGNT_Basic","CFGNT_CondJump","CFGNT_Call"];

val loop_pattern = ["CFGNT_Call","CFGNT_CondJump",
		    "CFGNT_Basic","CFGNT_Call","CFGNT_Call","CFGNT_CondJump",
		    "CFGNT_Call","CFGNT_CondJump","CFGNT_Call","CFGNT_Basic",
		    "CFGNT_Basic","CFGNT_Basic","CFGNT_Jump","CFGNT_Basic","CFGNT_CondJump"];	
val stmt = “ [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "R27" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R8" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "R27" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                           Bit32) Bit64)]”
val stmt = “[]”
(can dest_comb) stmt      
val _ = print("enter address to loop "^(term_to_string enter)^"\n");
  *)
    
val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;    


(* val adr_dict = Redblackmap.insert(adr_dict,``BL_Address (Imm64 0xEE6884w)``,"loop"); *)

    
val lbl_tm = ``BL_Address (Imm64 0xEE65F8w)``;
    
val g1 = cfg_create "toy1" [lbl_tm] n_dict bl_dict_;

val n_dict = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));
	     
val stop_lbl_tms = [
    ``BL_Address (Imm64 0xEE672cw)``,
      ``BL_Address (Imm64 0xEE6AE4w)``,
      ``BL_Address (Imm64 0xEE6B80w)``,
      “BL_Address (Imm64 0x12C1B70w)”,
      “BL_Address (Imm64 0x12F83A8w)”,
      “BL_Address (Imm64 0x12EC14Cw)”,
      “BL_Address_HC (Imm64 0xEE68ACw)”,
     “BL_Address (Imm64 0xEE6700w)”,
      “BL_Address (Imm64 0xEE6710w)”,
      “BL_Address (Imm64 0xEE676Cw)”,
      “BL_Address_HC (Imm64 0xEE681Cw)”
];
    
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

