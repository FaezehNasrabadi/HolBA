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
  
val lbl_tm = ``BL_Address (Imm64 0xEE60B4w)``;

val stop_lbl_tms = [``BL_Address (Imm64 0xEE6190w)``,“BL_Address (Imm64 0x12BB178w)”];

 *) 
val lbl_tm = ``BL_Address (Imm64 0xEE6128w)``;

val stop_lbl_tms = [``BL_Address (Imm64 0xEE613Cw)``,“BL_Address (Imm64 0xEE61C0w)”];

(*
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
    
val init_syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;

val g1 = cfg_create "toy" [lbl_tm] n_dict bl_dict_;

val n_dict = update_n_dict_ ((#CFGG_nodes g1),(#CFGG_node_dict g1));

(*
val lbl_tm = SYST_get_pc syst; 
	     val bl = (valOf o (lookup_block_dict bl_dict_)) lbl_tm;
	     val (lbl_block_tm, stmts, est) = dest_bir_block bl;
	     val s_tms = (fst o listSyntax.dest_list) stmts;*)
		 
val systs_run_a = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [init_syst] stop_lbl_tms adr_dict [];
(*val _ = print "\n\n";
val _ = print "finished exploration of all paths.\n\n";
val _ = print ("number of stopped symbolic execution states: " ^ (Int.toString (length systs)));
val _ = print "\n\n";*)

val (systs_noassertfailed_run_a, systs_assertfailed_run_a) =
    List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs_run_a;
(*val _ = print ("number of \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed)));
val _ = print "\n";     
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n";*)

val systs_run_b = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [init_syst] stop_lbl_tms adr_dict [];


val (systs_noassertfailed_run_b, systs_assertfailed_run_b) =
    List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs_run_b;
    
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

    in
	bexp
    end;

 fun collect_pred_expsdeps vals (bv, (exps, deps)) =
      let
      val symbv = find_bv_val "collect_pred_expsdeps" vals bv;
      val _ = if true then () else
              print ("pred: " ^ (symbv_to_string symbv) ^ "\n");

      val deps_delta = deps_of_symbval "collect_pred_expsdeps" symbv;
      val _ = if true then () else
              print ("pred_deps: " ^ (List.foldr (fn (x,s) => s ^ "; " ^ (term_to_string x)) "" (Redblackset.listItems deps_delta)) ^ "\n \n");

      val exp =
       case symbv of
          SymbValBE (x, _) => x
        | _ => raise ERR "collect_pred_expsdeps" "cannot handle symbolic value type";
      
    in
      (exp::exps, Redblackset.union(deps_delta, deps))
      end;
     
fun get_pred_exps_syst syst =
    let
	val vals  = SYST_get_vals syst;
	val pred_bvl = SYST_get_pred syst;	  

	val pred_flt = (List.filter (fn a => (String.isSuffix "_cnd" ((fst o dest_BVar_string) a))) pred_bvl);
	    
	val (pred_conjs, pred_deps) =
            List.foldr (collect_pred_expsdeps vals) ([], symbvalbe_dep_empty) pred_flt;

	val pred_conjs_exp = conj_preds_exps (tl pred_conjs) (hd pred_conjs);

	val pred_depsl_ = Redblackset.listItems pred_deps;
	val pred_depsl  = List.filter (is_bvar_bound vals) pred_depsl_;

	val valsl = List.map (fn bv => (bv, find_bv_val "get_pred_exps_syst" vals bv))
                             pred_depsl;
	val vals_eql =
            List.map symbval_eq_to_bexp valsl;

	val final_exp = conj_preds_exps vals_eql pred_conjs_exp;
	    
    in
	final_exp
    end

	  

fun get_obs_exps_syst syst =
let 

    val symb_list = Redblackmap.listItems (SYST_get_vals syst);

    val obs_exp_list = (rev (List.filter (fn (a,_) => (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a))) symb_list));

    val exp_ls = List.map symbval_eq_to_bexp obs_exp_list;

    val exps = conj_preds_exps (tl exp_ls) (hd exp_ls);

in 
   exps
end


    
fun exp_to_model exps =
    let
	
	val word_relation = bir_exp_to_wordsLib.bir2bool exps;

	(* val _ = print_term  (word_relation); *)
	    
	val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;
  
    in
	model
    end

(*   
val symb_syst1 = List.nth(systs_noassertfailed,1);

val symb_syst2 = List.nth(systs_noassertfailed,2);

val pred_exps1 = get_pred_exps_syst symb_syst1; 

val obs_exps1 = get_obs_exps_syst symb_syst1;
    
val pred_exps2 = get_pred_exps_syst symb_syst2;

val obs_exps2 = get_obs_exps_syst symb_syst2;


val obs_exps12 = ``(BExp_BinPred BIExp_Equal
		      ^obs_exps1
		      ^obs_exps2
		     )``; 

 
val exps_vs_p1 = conj_preds_exps [pred_exps1] obs_exps12;

val exps_vs_p2_final = conj_preds_exps [pred_exps2] exps_vs_p1;


val exps_vs_p2_final = conj_preds_exps [pred_exps2] pred_exps1;
    
val uls = exp_to_model obs_exps12;


val uls = exp_to_model pred_exps1;
val uls = exp_to_model pred_exps2;
 

fun obs_equal symb_syst1 symb_syst2 =
    let
	val pred_exps1 = get_pred_exps_syst symb_syst1; 

	val obs_exps1 = get_obs_exps_syst symb_syst1;
	    
	val pred_exps2 = get_pred_exps_syst symb_syst2;

	val obs_exps2 = get_obs_exps_syst symb_syst2;


	val obs_exps12 = ``(BExp_BinPred BIExp_Equal
			    ^obs_exps1
			    ^obs_exps2
			   )``; 

	val exps_vs_p1 = conj_preds_exps [pred_exps1] obs_exps12;

	val exps_vs_p2_final = conj_preds_exps [pred_exps2] exps_vs_p1;

	val word_relation = bir_exp_to_wordsLib.bir2bool exps_vs_p2_final;

	val equal = ((HolSmtLib.Z3_ORACLE_PROVE word_relation; true)
			handle HOL_ERR e => false);
    in
	equal
    end

   
fun obs_equal symb_syst1 symb_syst2 =
    let
	val obs_exps1 = get_obs_exps_syst symb_syst1;

	val obs_exps2 = get_obs_exps_syst symb_syst2;


	val obs_exps12 = ``(BExp_BinPred BIExp_Equal
			    ^obs_exps1
			    ^obs_exps2
			   )``; 

	val word_relation = bir_exp_to_wordsLib.bir2bool obs_exps12;

	val equal = ((Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation; true)
		     handle HOL_ERR e => false);

    in
	equal
    end
 *)
fun obs_equal symb_syst1 symb_syst2 =
    let
	val pred_exps1 = get_pred_exps_syst symb_syst1; 

	val obs_exps1 = get_obs_exps_syst symb_syst1;
	    
	val pred_exps2 = get_pred_exps_syst symb_syst2;

	val obs_exps2 = get_obs_exps_syst symb_syst2;


	val obs_exps12 = ``(BExp_BinPred BIExp_Equal
			    ^obs_exps1
			    ^obs_exps2
			   )``; 

	val exps_vs_p1 = conj_preds_exps [pred_exps1] obs_exps12;

	val exps_vs_p2_final = conj_preds_exps [pred_exps2] exps_vs_p1;

	val word_relation = bir_exp_to_wordsLib.bir2bool exps_vs_p2_final;

	val (model,equal) = ((Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation, true)
			handle HOL_ERR e => ([],false));
    in
	(model,equal) 
    end
    
fun subset_sval_cval exp (sval,cval)  =
    let
	val subexp1 = mk_BExp_Den(mk_BVar_string (sval,“BType_Imm Bit64”));
	val subexp2 = mk_BExp_Const(mk_Imm64(cval))
	val ref_exp =  subst[subexp1 |-> subexp2] exp;
    in
	ref_exp
    end;

open scamv_enumLib;

fun triangleWith f xs ys =
(*  full product: List.concat (map (fn a => map (fn b => f a b) xs) ys);*)
    let fun go g [] _ = []
          | go g _ [] = []
          | go g (x::xs) (y::ys) =
            (List.map (fn p => g x p) (y::ys)) @
            go g xs ys
    in
        if length ys < length xs
        then (* take upper triangle *)
            go (fn x => fn y => f y x) ys xs
        else (* take lower triangle *)
            go f xs ys
    end;


val full_product = triangleWith (fn x => fn y => { a_run = x, b_run = y})
                                 systs_noassertfailed_run_a systs_noassertfailed_run_b;


    
(* roundrobin_list full_product 
    open embexp_logsLib;
    open bir_scamv_driverLib;

(String.isSubstring "9_R22" "v10_9_R22")

*)
val obs_eq_systs = (List.filter (fn spec => snd(obs_equal (#a_run spec) (#b_run spec))) full_product);

val _ = print ("number of \"observation equal\" final state pairs found: " ^ (Int.toString (length obs_eq_systs)));
val _ = print "\n";


fun sval_cval_bir (sval,cval)  =
    if ((fst o dest_type o type_of) cval) = "fmap" then
	let
	    val _ = (print o fst o dest_type o type_of) cval;
	    val deep = Redblackset.empty Term.compare;
	    val var = mk_BVar_string (sval,“BType_Imm Bit64”);
	    val value = (SymbValBE (“BExp_Const (Imm64 0x0w)”,deep));
	in
	    (var,value)
	end
    else
	let
	    val _ = (print o fst o dest_type o type_of) cval;
	    val deep = Redblackset.empty Term.compare;
	    val var = mk_BVar_string (sval,“BType_Imm Bit64”);
	    val value = (SymbValBE (mk_BExp_Const(mk_Imm64(cval)),deep));
	in
	    (var,value)
	end
    

(* Redblackmap.listItems vals1 
Redblackmap.insertList (vals1,)
*)    
fun add_model_obs_equal symb_syst1 symb_syst2 =
    let
	val model = fst(obs_equal symb_syst1 symb_syst2);

	val mlist = List.map sval_cval_bir model;
	    
	val vals1 = SYST_get_vals symb_syst1;

	val vals2 = SYST_get_vals symb_syst1;
	    
	val syst1 = SYST_update_vals (Redblackmap.insertList (vals1,mlist)) symb_syst1;

	val syst2 = SYST_update_vals (Redblackmap.insertList (vals2,mlist)) symb_syst2;
	    
    in
	{ a_run = syst1, b_run = syst2}
    end
    

val syst_w_conc_vals = (List.map (fn spec => (add_model_obs_equal  (#a_run spec) (#b_run spec))) obs_eq_systs);


val obs_eq_systs = (List.filter (fn spec => snd(obs_equal (#a_run spec) (#b_run spec))) syst_w_conc_vals);

val _ = print ("number of \"observation equal\" final state pairs found: " ^ (Int.toString (length obs_eq_systs)));
val _ = print "\n";
  (*  
val b =  “0”;

(print o fst o dest_type o type_of) b
val spec = hd full_product;

val symb_syst1 = (#a_run spec);

val symb_syst2 = (#b_run spec);
    
val pred_exps1 = get_pred_exps_syst symb_syst1; 

val obs_exps1 = get_obs_exps_syst symb_syst1;
    
val pred_exps2 = get_pred_exps_syst symb_syst2;

val obs_exps2 = get_obs_exps_syst symb_syst2;


val obs_exps12 = ``(BExp_BinPred BIExp_Equal
		      ^obs_exps1
		      ^obs_exps2
		     )``; 

 
val exps_vs_p1 = conj_preds_exps [pred_exps1] obs_exps12;

val exps_vs_p2_final = conj_preds_exps [pred_exps2] exps_vs_p1;



    
    
      
fun enumerate_relation path_dom static_obs_dom dynamic_obs_dom =
    let (* compute all interesting path pairs *)
        val paths = triangleWith (fn x => fn y => { a_run = x, b_run = y})
                                 path_dom path_dom;
        (* compute all interesting dynamic observation traces *)
        val obs_specs = buildLeavesIds dynamic_obs_dom;
        val dyn_spec = triangleWith (fn x => fn y => { a_run = x, b_run = y })
                                    obs_specs obs_specs;

        (* static obs always occur in their respective path *)
        val static_obs = List.map (fn id => (true,id)) static_obs_dom;

        (* add the static observations (always true) to the dyn ones *)
        val spec =
            if null dyn_spec (* no dynamic observations *)
            then [{a_run = static_obs, b_run = static_obs}]
            else
                List.map (fn spec => {a_run = static_obs @ (#a_run spec),
                                      b_run = static_obs @ (#b_run spec) })
                         dyn_spec;

        (* compute pairs of path * observation spec *)
        val specs =
            triangleWith (fn path_spec => fn obs_spec =>
                             { a_run = (#a_run path_spec,
                                        #a_run obs_spec),
                               b_run = (#b_run path_spec,
                                        #b_run obs_spec)})
                         paths spec;
        fun effective_length xs =
            length (List.filter (fn (b,x) => b) xs);

        (* discard specs with different number of observations *)
        val full_specs =
            List.filter (fn spec =>
                            effective_length (snd (#a_run spec)) =
                            effective_length (snd (#b_run spec)))
                        specs;

        (* iterator *)
(*        val len = length full_specs;
        fun next_test_case n =
            SOME (List.nth (full_specs, n mod len))
                     handle _ => NONE; *)
    in
        (full_specs, roundrobin_list full_specs)
    end;		 
    
val sval = "sy_SP_EL0";
val cval = “0x800060C0w”;
  open bir_expSyntax;
  open bir_envSyntax;
  open bir_smtLib;

  fun proc_preds (vars, asserts) pred =
    List.foldr (fn (exp, (vl1,al)) =>
      let val (_,vl2,a) = bexp_to_smtlib [] vl1 exp in
        (vl2, a::al)
      end) (vars, asserts) pred;


val vars    = Redblackset.empty smtlib_vars_compare;
	val asserts = [];

	(* process the predicate conjuncts *)
	val (vars, asserts) = proc_preds (vars, asserts) pred_conjs;

	(* process the symbolic values *)
	val (vars, asserts) = proc_preds (vars, asserts) vals_eql;
val result = querysmt bir_smtLib_z3_prelude vars asserts;

val ops_lists = List.map get_obs_exps_syst systs_noassertfailed;
 
val uls = List.map exp_to_model ops_lists;



fun get_obs_exps_syst syst =
let 

    val symb_list = Redblackmap.listItems (SYST_get_vals syst);

    val obs_exp_list = List.map snd (rev (List.filter (fn (a,_) => (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a))) symb_list));

    val obs_exps = List.map  (fn x => bir_symbexec_funcLib.symbval_bexp x)  obs_exp_list

in 
    listSyntax.mk_list(obs_exps,bir_exp_t_ty)
end

val ops_lists = List.map get_obs_exps_syst systs_noassertfailed;
    





val word_relation = bir_exp_to_wordsLib.bir2bool exps;

	(* val _ = print_term  (word_relation); *)
	    
	val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;

	(* val _ = (List.map (fn (x,y) => (print (x^" : "^(term_to_string y) ^"\n"))) model); *)

	val tgt_val = (List.find (fn (x,y) => x = "sy_target") model);


val symb_syst1 = List.nth(systs_noassertfailed,1);
val symb_syst2 = List.nth(systs_noassertfailed,2);

check_feasible symb_syst2



fun conj_preds_exps tms exp =
    let

	val exps = ``(BExp_BinExp BIExp_And
		      ^exp
		      ^(hd tms)
		     )``;   

    in
	if (List.null (tl tms))
	     then  exps
	else (conj_preds_exps (tl tms) exps)
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


val syst = hd systs_noassertfailed;
val obs_exp_list = (rev (List.filter (fn (a,_) => (String.isSuffix "observe_exp" ((fst o dest_BVar_string) a))) symb_list));

val exp_ls = List.map symbval_eq_to_bexp obs_exp_list

val exps = conj_preds_exps (tl exp_ls) (hd exp_ls);


Redblackmap.foldl

HOL_Interactive.toggle_quietdec(); 
open Redblackmap;
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
