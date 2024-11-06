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

(*

val current_prog = “BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm64 0xED4A10w) "B94002A9 (ldr w9,[x21])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2 (BExp_Den (BVar "R21" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R9" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_Den (BVar "R21" (BType_Imm Bit64)))
                    BEnd_LittleEndian Bit32) Bit64)];
         bb_last_statement :=
           BStmt_Jmp (BLE_Label (BL_Address (Imm64 0xED4A14w)))|>;]”;

	val obs_hol_type = ``:bir_val_t``;
	fun add_obs mb t = rand (concl (EVAL ``add_obs_mem_addr_pc_armv8 ^mb ^t``));
	fun proginst_fun_gen obs_type prog =
	    inst [Type`:'a` |-> obs_type] prog;
	fun embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);
	val proginst_fun = proginst_fun_gen obs_hol_type;


 *)


fun add_obs_to_bir embexp_params_memory current_prog =
    let 
	open bir_obs_modelTheory;

	fun add_obs mb t = rand (concl (EVAL ``add_obs_mem_addr_pc_armv8 ^mb ^t``));
	fun proginst_fun prog = inst [Type`:'observation_type` |-> Type`:bir_val_t`] prog;
	fun embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);
	
	val mem_bounds =
	    let
		val (mem_base, mem_len) = embexp_params_memory;
		val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
	    in
		pairSyntax.mk_pair
		    (wordsSyntax.mk_wordi (embexp_params_cacheable mem_base, 64),
		     wordsSyntax.mk_wordi (embexp_params_cacheable mem_end, 64))
	    end;
	val lifted_prog_w_obs = add_obs mem_bounds (proginst_fun (current_prog));

    in
	lifted_prog_w_obs
    end;
     
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


val embexp_params_memory = ((Arbnum.fromInt 0x00000000000450c), (Arbnum.fromInt 0x000000001b7ba37));

val prog_w_obs = add_obs_to_bir embexp_params_memory prog_tm;
    
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
(*val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

val func_table = Redblackmap.mkDict Term.compare : (term, string) Redblackmap.dict;
val n_dict = bir_cfgLib.cfg_build_node_dict  bl_dict_ prog_lbl_tms_;
val n = hd  (List.map (#CFGN_hc_descr o snd) (Redblackmap.listItems n_dict))
val lbl_tm   = #CFGN_lbl_tm n;
	val descr  = (valOf o #CFGN_hc_descr) n;
	val instrDes = (snd o (list_split_pred #" ") o explode) descr;	
val fun_adr = (List.map (fn x => (fun_address_dict x)) (List.map snd (Redblackmap.listItems n_dict)));
 *)   
val lbl_tm = ``BL_Address (Imm64 0xEE60B4w)``;

val stop_lbl_tms = [``BL_Address (Imm64 0xEE6190w)``,“BL_Address (Imm64 0x12BB178w)”];
(*

val lbl_tm = ``BL_Address (Imm64 0xEE6128w)``;

val stop_lbl_tms = [``BL_Address (Imm64 0xEE613Cw)``,“BL_Address (Imm64 0xEE61C0w)”];


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
		      ``BL_Address (Imm64 0xEE9064w)``];*)
    
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;

val g1 = cfg_create "toy" [lbl_tm] n_dict bl_dict_;

val n_dict = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));

(*
val lbl_tm = SYST_get_pc syst; 
	     val bl = (valOf o (lookup_block_dict bl_dict_)) lbl_tm;
	     val (lbl_block_tm, stmts, est) = dest_bir_block bl;
	     val s_tms = (fst o listSyntax.dest_list) stmts;*)
		 
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



fun get_obs_exps_syst syst =
let 

    val symb_list = Redblackmap.listItems (SYST_get_vals syst);

    val obs_exp_list = List.map snd (rev (List.filter (fn (a,_) => (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a))) symb_list));

    val obs_exps = List.map  (fn x => bir_symbexec_funcLib.symbval_bexp x)  obs_exp_list

in 
    listSyntax.mk_list(obs_exps,bir_exp_t_ty)
end

val ops_lists = List.map get_obs_exps_syst systs_noassertfailed;
    

   (* 


 open bslSyntax;

  fun symbval_eq_to_bexp (bv, symbv) =
    let
      val bv_exp = bden bv;

      val bexp =
       case symbv of
          SymbValBE (exp,_) =>
            beq (bv_exp, exp)
        | SymbValInterval ((exp1, exp2), _) =>
            band (ble (exp1, bv_exp), ble (bv_exp, exp2))
        | _ => raise ERR "symbval_eq_to_bexp" "cannot handle symbolic value type";
      
      (* val _ = print (term_to_string bv); *)
      (* val _ = print "\n"; *)
      (* val _ = print (term_to_string bexp); *)
      (* val _ = print "\n"; *)
    in
	bexp
    end;


fun get_obs_exps_syst syst =
let 

    val symb_list = Redblackmap.listItems (SYST_get_vals syst);

    val obs_exp_list = List.map snd (rev (List.filter (fn (a,_) => (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a))) symb_list));

    val obs_exps = List.map  (fn x => bir_symbexec_funcLib.symbval_bexp x)  obs_exp_list

in 
    listSyntax.mk_list(obs_exps,bir_exp_t_ty)
end

List.map get_obs_exps_syst systs_noassertfailed

listSyntax.mk_list

List.map symbval_eq_to_bexp obs_exp_list

Redblackmap.foldl

HOL_Interactive.toggle_quietdec(); 
open Term;
HOL_Interactive.toggle_quietdec(); 

List.filter ()

val Obs_dict_primed = Redblackmap.map (fn (a,b) => (if (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a)) then b)) vals;

val pred = SYST_get_pred syst;
    val env  = SYST_get_env  syst;
    val vals = SYST_get_vals syst;

    val entry_vars = symbvalbe_dep_empty;
    val entry_vars = Redblackset.addList(entry_vars, pred);
    val entry_vars = Redblackset.addList(entry_vars, (List.map snd o Redblackmap.listItems) env);
    val entry_vars = Redblackset.filter (is_bvar_bound vals) entry_vars;

    val deps = Redblackset.foldl (deps_union vals) symbvalbe_dep_empty entry_vars;

    val keep_vals = Redblackset.filter (is_bvar_bound vals) (Redblackset.union(entry_vars, deps));

    val num_vals = Redblackmap.numItems vals;
    val num_keep_vals = Redblackset.numItems keep_vals;

    val num_diff = num_vals - num_keep_vals;



val bv = “BVar "92_observe_exp" (BType_Imm Bit64)”;


val keep_vals = Redblackset.filter (is_bvar_bound vals) (Redblackset.union(entry_vars, deps));

val syst = hd systs_noassertfailed;

 val find_val = List.find (fn (a,_) => Term.term_eq a bv) vals_list;

val symb_list = Redblackmap.listItems (SYST_get_vals syst);

val obs_exp_list = (List.map snd (List.filter (fn (a,_) => (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a))) symb_list));

val obs_exps = List.map  (fn x => bir_symbexec_funcLib.symbval_bexp x)  obs_exp_list

(lookup_block_dict (SYST_get_vals syst) “BVar "116_observe_exp" (BType_Imm Bit64)”)


val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst))
                         systs_noassertfailed;

val _ = print "Get predlists";
val _ = print "\n";
    
val predlists_refined = List.map (fn lst => bir_symbexec_sortLib.removeDuplicates lst) predlists;
val _ = print "Get refined predlists";    
val _ = print "\n";
(* val _ = printTermList predlists_refined; *)
    
val tree = predlist_to_tree predlists_refined;

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


val refined_process = refine_process sapic_process;

val rset = ((Redblackset.empty Term.compare): term Redblackset.set);
    
val process_with_live_vars = process_live_vars rset refined_process;
val _ = print ("built a refined process with live variables");
val _ = print "\n";

	
val _ =  ( write_sapic_to_file o process_to_string) process_with_live_vars;
     
val _ = print ("wrote into file");
val _ = print "\n";


*)
