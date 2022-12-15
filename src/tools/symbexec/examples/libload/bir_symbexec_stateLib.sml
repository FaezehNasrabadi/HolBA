structure bir_symbexec_stateLib =
struct

local
  val ERR      = Feedback.mk_HOL_ERR "bir_symbexec_stateLib"
  val wrap_exn = Feedback.wrap_exn   "bir_symbexec_stateLib"
in (* outermost local *)
(* symbolic values *)
datatype symb_value =
    SymbValBE       of (term * term Redblackset.set)
  | SymbValInterval of ((term * term) * term Redblackset.set)
                    (* TODO: generalize this later *)
                    (* memory layout: flash, globals, stack;
                                      size of first (constants) and middle portion (globals) *)
  | SymbValMem      of (term *
                        (Arbnum.num * Arbnum.num * Arbnum.num) *
                        ((Arbnum.num -> Arbnum.num option) *
                         (Arbnum.num, term * term Redblackset.set) Redblackmap.dict *
                         (* notes: need to keep information what on the stack is unknown after merging!
                                   use free variables for this *)
                         (term * (Arbnum.num, term * term Redblackset.set) Redblackmap.dict)
                        ) *
                        term Redblackset.set);

val symbvalbe_dep_empty = Redblackset.empty Term.compare;

val symbvdebugOn = false;
fun memmap_string_fold ((addr, (exp, deps)), str) =
  "[" ^ (Arbnum.toString addr) ^ " -> " ^ (term_to_string exp) ^ "]\n" ^ str;
fun symbv_to_string_raw verb (SymbValBE (exp, deps)) =
       ("SymbValBE (" ^
        (term_to_string exp) ^
        ", " ^
        (Int.toString (Redblackset.numItems deps)) ^
        ")")
  | symbv_to_string_raw verb (SymbValInterval ((min, max), deps)) =
       ("SymbValInterval ((" ^
        (term_to_string min) ^
        ", " ^
        (term_to_string max) ^
        "), " ^
        (Int.toString (Redblackset.numItems deps)) ^
        ")")
  | symbv_to_string_raw verb (SymbValMem (basem_bv, _, (_, mapglobl, (sp, mapstack)), deps)) =
       "SymbValMem (" ^ (if not verb then "" else
           "\nbasem= " ^ (term_to_string basem_bv) ^
           "\nglobl=" ^
           (List.foldr memmap_string_fold "" (Redblackmap.listItems mapglobl)) ^
           "\t,\nsp=" ^
           (term_to_string sp) ^
           "\t,\nstack=\n" ^
           (List.foldr memmap_string_fold "" (Redblackmap.listItems mapstack)) ^
           "\t,\ndeps=\n" ^
           (Int.toString (Redblackset.numItems deps))
       ) ^ "\t)";
fun symbv_to_string symbv = symbv_to_string_raw symbvdebugOn symbv;


(* symbolic states *)
datatype symb_state =
  SymbState of {
      SYST_pc     : term,
      SYST_env    : (term, term) Redblackmap.dict,
      SYST_status : term,
      (* symbolic observation list: id, condition, value list, aggregation function *)
      SYST_obss   : (Arbnum.num * term * term list * term) list,
      (* list of indirect jumps *)
      SYST_indjmp   : term list,
      (* path condition conjuncts *)
      SYST_pred   : term list,
      (* abstracted symbolic values for some "fresh" variables *)
      SYST_vals   : (term, symb_value) Redblackmap.dict
    };

val BST_Running_tm =
  ``BST_Running``;
val BST_AssertionViolated_tm =
  ``BST_AssertionViolated``;
val BST_AssumptionViolated_tm =
  ``BST_AssumptionViolated``;

fun SYST_get_pc     (SymbState systr) =
  #SYST_pc systr;
fun SYST_get_env    (SymbState systr) =
  #SYST_env systr;
fun SYST_get_status (SymbState systr) =
  #SYST_status systr;
fun SYST_get_obss   (SymbState systr) =
  #SYST_obss systr;
fun SYST_get_indjmp   (SymbState systr) =
  #SYST_indjmp systr;
fun SYST_get_pred   (SymbState systr) =
    #SYST_pred systr;
fun SYST_get_vals   (SymbState systr) =
  #SYST_vals systr;

fun SYST_mk pc env status obss indjmp pred vals =
  SymbState {SYST_pc     = pc,
             SYST_env    = env,
             SYST_status = status,
             SYST_obss   = obss,
             SYST_indjmp   = indjmp,
	     SYST_pred   = pred,
             SYST_vals   = vals };

fun SYST_update_pc pc' (SymbState systr) =
  SYST_mk (pc')
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
	  (#SYST_indjmp systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_env env' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (env')
          (#SYST_status systr)
          (#SYST_obss   systr)
	  (#SYST_indjmp systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_status status' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (status')
          (#SYST_obss   systr)
	  (#SYST_indjmp systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_obss obss' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (obss')
	  (#SYST_indjmp systr)
          (#SYST_pred   systr)
          (#SYST_vals   systr);
fun SYST_update_indjmp indjmp' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
	  (indjmp')
          (#SYST_pred   systr)
          (#SYST_vals   systr);    
fun SYST_update_pred pred' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
	  (#SYST_indjmp systr)
          (pred')
          (#SYST_vals   systr);
fun SYST_update_vals vals' (SymbState systr) =
  SYST_mk (#SYST_pc     systr)
          (#SYST_env    systr)
          (#SYST_status systr)
          (#SYST_obss   systr)
	  (#SYST_indjmp systr)
          (#SYST_pred   systr)
          (vals');


fun state_is_running syst =
  identical (SYST_get_status syst) BST_Running_tm;
(*val bv = ``BVar "sy_MEM" (BType_Mem Bit32 Bit8)``;*)
(* fresh variables and initial state variables *)
local
  open bir_envSyntax;
  open bir_expSyntax;
  val freshvarcounter_ = ref (0:int);
  fun get_fresh_var_counter () =
    let val i = !freshvarcounter_; in
    (freshvarcounter_ := i + 1; i) end;
in
  fun get_bvar_fresh bv =
    let
      val (s, bty) = dest_BVar_string bv;
     (* val new_s = "fr_" ^ (Int.toString (get_fresh_var_counter ())) ^ "_" ^ s;*)
      val new_s = (Int.toString (get_fresh_var_counter ())) ^ "_" ^ s;
    in
      mk_BVar_string (new_s, bty)
    end;

  fun get_bvar_init bv =
    let
      val (s, bty) = dest_BVar_string bv;
      val new_s = "sy_" ^ s;
    in
      mk_BVar_string (new_s, bty)
    end;

  fun is_bvar_init bv =
    let
      val (s, _) = dest_BVar_string bv;
    in
      String.isPrefix "sy_" s
    end;

  fun is_bvar_free vals bv =
    (not o isSome o Redblackmap.peek) (vals,bv);

  fun is_bvar_initorfree vals bv =
    (is_bvar_init) bv orelse
    (is_bvar_free vals) bv;

  fun is_bvar_bound vals bv =
    not (is_bvar_initorfree vals bv);

  fun get_symbv_bexp_free_sz varstr ty_sz =
    let
      open bslSyntax;
      open bir_envSyntax;
      open bir_valuesSyntax;

      val ty = case ty_sz of
                   1 => BType_Imm1_tm
                |  8 => BType_Imm8_tm
                | 16 => BType_Imm16_tm
                | 32 => BType_Imm32_tm
                | _  => raise ERR "get_symbv_bexp_free_sz" ("cannot handle size " ^ (Int.toString ty_sz));

      val bv_fr = get_bvar_fresh (mk_BVar_string (varstr, ty));
      val deps = Redblackset.add (symbvalbe_dep_empty, bv_fr);
    in
      (bden (bv_fr), deps)
    end;
end


(* initial state *)
local
  open bir_envSyntax;
in
  fun init_state lbl_tm prog_vars =
    let
      val envlist_progvars = List.map (fn bv => (bv, get_bvar_init bv)) prog_vars;
    in
      SYST_mk lbl_tm
              (Redblackmap.fromList Term.compare envlist_progvars)
              BST_Running_tm
              []
	      []
              []
              (Redblackmap.fromList Term.compare [])
    end;
end


(* state update primitives *)
fun insert_symbval bv_fresh symbv syst =
  let
    val vals  = SYST_get_vals syst;

    (* make sure that bv_fresh is indeed fresh and is not an initial variable *)
    val _ = if (not o is_bvar_init) bv_fresh then () else
            raise ERR "insert_symbval" ("variable cannot be an initial variable: " ^ (term_to_string bv_fresh));
    val _ = if (not o isSome o Redblackmap.peek) (vals, bv_fresh) then () else
            raise ERR "insert_symbval" ("variable needs to be fresh: " ^ (term_to_string bv_fresh));

    val vals' = Redblackmap.insert (vals, bv_fresh, symbv);
  in
    (SYST_update_vals vals') syst
  end;

fun update_envvar bv bv_fresh syst =
  let
    val env   = SYST_get_env  syst;

    val _ = if (isSome o Redblackmap.peek) (env, bv) then () else
            raise ERR
                  "update_envvar"
                  ("can only update existing state variables, tried to update: " ^ (term_to_string bv));
    val env'  = Redblackmap.insert (env, bv, bv_fresh);
  in
    (SYST_update_env env') syst
  end;

(* helper functions *)
fun find_bv_val err_src_string vals bv =
    (valOf o Redblackmap.peek) (vals,bv)
    handle Option => raise ERR
                             err_src_string
                             ("coudln't find value for " ^ (term_to_string bv));

fun get_state_symbv err_src_string bv syst =
  let
    val env  = (SYST_get_env  syst);
    val vals = (SYST_get_vals syst);

    val bv_fr = find_bv_val (err_src_string ^ "::get_state_symbv::env")
                            env  bv;
    val symbv = find_bv_val (err_src_string ^ "get_state_symbv::vals")
                            vals bv_fr;
  in
    symbv
  end;


(* symbval dependencies *)
fun deps_of_symbval err_src_string symbv =
  case symbv of
          SymbValBE (_,deps) => deps
        | SymbValInterval (_, deps) => deps
        | SymbValMem (_, _, _, deps) => deps
(*
        | _ => raise ERR err_src_string "cannot handle symbolic value type to find dependencies";
*)

fun deps_union vals (bv, deps) =
  let
    val symbv = find_bv_val "deps_union" vals bv;
    val deps_delta = deps_of_symbval "deps_union" symbv;
  in
    Redblackset.union (deps_delta, deps)
  end;

fun deps_find_symbval err_src_string vals bv =
  if is_bvar_initorfree vals bv
  then Redblackset.add(symbvalbe_dep_empty,bv) else (
    deps_of_symbval err_src_string (find_bv_val err_src_string vals bv)
    handle e => raise wrap_exn ("deps_find_symbval::expect bir expression for variable: " ^ (term_to_string bv)) e
  );


(* tidy up states *)
fun tidyup_state_vals syst =
  let
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

    val _ = if num_diff = 0 then () else
            if num_diff < 0 then
              raise ERR "tidyup_state_vals" "this shouldn't be negative"
            else
              if true then () else
              print ("TIDIED UP " ^ (Int.toString num_diff) ^ " VALUES.\n");

    val vals' = Redblackset.foldl
                (fn (bv,vals_) => Redblackmap.insert(vals_, bv, find_bv_val "tidyup_state_vals" vals bv))
                (Redblackmap.mkDict Term.compare)
                keep_vals;
  in
    (SYST_update_vals vals') syst
  end;


(* check feasibility of states *)
local
  open bir_expSyntax;
  open bir_envSyntax;
  open bir_smtLib;

  fun proc_preds (vars, asserts) pred =
    List.foldr (fn (exp, (vl1,al)) =>
      let val (_,vl2,a) = bexp_to_smtlib [] vl1 exp in
        (vl2, a::al)
      end) (vars, asserts) pred;

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
      (*
      val _ = print (term_to_string bv);
      val _ = print "\n";
      *)
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
              print ("pred_deps: " ^ (List.foldr (fn (x,s) => s ^ "; " ^ (term_to_string x)) "" (Redblackset.listItems deps_delta)) ^ "\n");

      val exp =
       case symbv of
          SymbValBE (x, _) => x
        | _ => raise ERR "collect_pred_expsdeps" "cannot handle symbolic value type";
      (*
      val _ = print (term_to_string exp);
      val _ = print "\n";
      *)
    in
      (exp::exps, Redblackset.union(deps_delta, deps))
    end;

in (* local *)
fun check_feasible syst =
    let
	val vals  = SYST_get_vals syst;
	val pred_bvl = SYST_get_pred syst;

	val (pred_conjs, pred_deps) =
            List.foldr (collect_pred_expsdeps vals) ([], symbvalbe_dep_empty) pred_bvl;

	val pred_depsl_ = Redblackset.listItems pred_deps;
	val pred_depsl  = List.filter (is_bvar_bound vals) pred_depsl_;

	val valsl = List.map (fn bv => (bv, find_bv_val "check_feasible" vals bv))
                             pred_depsl;
	val vals_eql =
            List.map symbval_eq_to_bexp valsl;

	(* memory accesses should not end up here (actually only SymbValBE should be relevant),
    ignore this detail for now *)

	(* start with no variable and no assertions *)
	val vars    = Redblackset.empty smtlib_vars_compare;
	val asserts = [];

	(* process the predicate conjuncts *)
	val (vars, asserts) = proc_preds (vars, asserts) pred_conjs;

	(* process the symbolic values *)
	val (vars, asserts) = proc_preds (vars, asserts) vals_eql;

	val result = querysmt bir_smtLib_z3_prelude vars asserts;

	val _ = if result = BirSmtSat orelse result = BirSmtUnsat then () else
		raise ERR "check_feasible" "smt solver couldn't determine feasibility"

	val resultvalue = result <> BirSmtUnsat;

	val _ = if resultvalue then () else
		if true then () else
		print "FOUND AN INFEASIBLE PATH...\n";
    in
	resultvalue
    end;

(*
fun add_pred be pred =
    let      
	val pred_conj = ``(BExp_BinExp BIExp_And
				       (BExp_BinExp BIExp_Or
						    (BExp_BinPred BIExp_Equal
								  (BExp_Const (Imm64 0w))
						     ^be)
						    (BExp_BinPred BIExp_Equal
								  (BExp_Const (Imm64 10w))
						     ^be))
			   ^(pred)
			  )``;
    in
	pred_conj
    end;
      

fun add_pred_eq be pred =
    let
	val tgt = ``BExp_Den (BVar "target" (BType_Imm Bit64))``;

	val pred_conj = ``(BExp_BinExp BIExp_And
				       (BExp_BinPred BIExp_Equal
					^tgt
					^be)
			   
			   ^(pred)
			  )``;   

    in
	pred_conj
    end;


    
fun add_pred_neq be pred =
    let
	val tgt = ``BExp_Den (BVar "target" (BType_Imm Bit64))``;

	val pred_conj = ``(BExp_BinExp BIExp_And
				       (BExp_BinPred BIExp_NotEqual
					^tgt
					^be)
			   
			   ^(pred)
			  )``;   

    in
	pred_conj
    end;*)

fun add_pred pred =
    let
	val tgt = ``BExp_Den (BVar "target" (BType_Imm Bit64))``;
	    
	val pred_conj = ``(BExp_BinExp BIExp_And
				       (BExp_BinExp BIExp_Or
						    (BExp_BinPred BIExp_Equal
								  (BExp_Const (Imm64 0w))
						     ^tgt)
						    (BExp_BinPred BIExp_Equal
								  (BExp_Const (Imm64 10w))
						     ^tgt))
			   ^(pred)
			  )``;
    in
	pred_conj
    end;
    
fun conj_preds_exps tms exp =
    let
	val tgt = ``BExp_Den (BVar "target" (BType_Imm Bit64))``;

	val exps = ``(BExp_BinExp BIExp_And
		      ^exp
		      ^(hd tms)
		     )``;   

    in
	if (List.null (tl tms))
	     then  exps
	else (conj_preds_exps (tl tms) exps)
    end;
    
fun add_pred_eq be =
    let
	val tgt = ``BExp_Den (BVar "target" (BType_Imm Bit64))``;

	val pred = ``(BExp_BinPred BIExp_Equal
		      ^tgt
		      ^be)
		     ``;   

    in
	pred
    end;


fun add_pred_neq be  =
    let
	val tgt = ``BExp_Den (BVar "target" (BType_Imm Bit64))``;

	val pred = ``(BExp_BinPred BIExp_NotEqual
					^tgt
					^be)``;   

    in
	pred
    end;
                       
fun subset_mem_exp vals_eql exp =
    let
	val (bop, subexp1, subexp2) = (dest_BExp_BinPred (hd vals_eql));
	val ref_exp =  subst[subexp1 |-> subexp2] exp;

    in
	if (List.null (tl vals_eql))
	then  ref_exp
	else (subset_mem_exp (tl vals_eql) ref_exp)
    end;

(*

fun subset_mem_exp exp =
    let

	val pred = if (bir_expSyntax.is_BExp_BinExp exp) then
		       let
			   val (bop1, subexp1, subexp2) = (dest_BExp_BinExp) exp;
			   val b = if (bir_expSyntax.is_BExp_BinExp subexp1)
				   then (subset_mem_exp subexp1)
				   else if (bir_expSyntax.is_BExp_BinExp subexp2)
				   then (subset_mem_exp subexp2)
				   else if (bir_expSyntax.is_BExp_BinPred subexp1)
				   then
				       let
					   val (bop11, subexp11, subexp22) = (dest_BExp_BinPred) subexp1;
					   val res = if identical bop11 bir_exp_immSyntax.BIExp_Equal_tm then
							 let
							     val name = (fst o dest_BVar_string o dest_BExp_Den) subexp11;
							     val tm = if (String.isSuffix "MEM" name)
								      then subst[subexp11 |-> subexp22] exp
								      else exp;
							 in
							     tm
							 end
						     else exp;

				       in
					   res
				       end
				   else if (bir_expSyntax.is_BExp_BinPred subexp2)
				   then
				       let
					   val (bop11, subexp11, subexp22) = (dest_BExp_BinPred) subexp2;
					   val res = if identical bop11 bir_exp_immSyntax.BIExp_Equal_tm then
							 let
							     val name = (fst o dest_BVar_string o dest_BExp_Den) subexp11;
							     val tm = if (String.isSuffix "MEM" name)
								      then subst [subexp11 |-> subexp22] exp
								      else exp;
							 in
							     tm
							 end
						     else exp;

				       in
					   res
				       end
				   else exp;

		       in
			   b
		       end
		       else exp;

    in
	pred
    end;
					   
					   
					     

open Option;
open bir_immSyntax;
open bir_exp_to_wordsLib;
val model =
   [("target", “10w”), ("SP_EL0", “0x800000000000010w”),
    ("tmp_SP_EL0", “0x7FFFFFFFFFFFFE0w”), ("R0", “10w”),
    ("R1", “0x800000000000000w”), ("R0", “0w”), ("R0", “0w”),
    ("MEM", “FUN_FMAP (K 0w) 𝕌(:word64)”), ("R0", “0w”),
    ("MEM", “FUN_FMAP (K 0w) 𝕌(:word64)”)];*)
 (*val word_relation = (List.map (fn x => bir_exp_to_wordsLib.bir2bool x) pred_conjs_be);

			       val _ = print_term  (word_relation);
			       val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;*)
				   
			       (*val tgt_val = if (isSome model)
					       then (List.find (fn (x,y) => x = "target") (valOf model))
					       else raise ERR "possible_target" "cannot find model";*)

    
fun possible_target exps pred_conjs_be vars asserts vals_eql tgts =
    let
	
	(* process the predicate conjuncts *)
	val (vars, asserts) = proc_preds (vars, asserts) (pred_conjs_be);

	(* process the symbolic values *)
	val (vars, asserts) = proc_preds (vars, asserts) vals_eql;

	val result = querysmt bir_smtLib_z3_prelude vars asserts;

	val targets =  if (result = BirSmtSat) then
			   let
			       (* val model = querysmt_model bir_smtLib_z3_prelude vars asserts; *)
			       
			       (* val _ = print_term  (exps); *)

			       val word_relation = bir_exp_to_wordsLib.bir2bool exps;

			       (* val _ = print_term  (word_relation); *)
				   
			       val model = Z3_SAT_modelLib.Z3_GET_SAT_MODEL word_relation;

			       val _ = (List.map (fn (x,y) => (print (x^" : "^(term_to_string y) ^"\n"))) model);

			       val tgt_val = (List.find (fn (x,y) => x = "target") model);   
			       val t = if (isSome tgt_val)
				       then (bir_expSyntax.mk_BExp_Const o bir_immSyntax.mk_Imm64 o snd o valOf) tgt_val
				       else raise ERR "possible_target" "cannot find target value";
				   
			       val tgts = t::tgts;
			       val pred = add_pred_neq t;
			       val exps1 = conj_preds_exps [exps] pred; 
			   in
			       (possible_target exps1 (pred::pred_conjs_be) vars asserts vals_eql tgts)
			   end
		       else
			   tgts;
	    
    in
	targets
	
    end;
    

    
fun symbval_get_bexp symbv =
    let
	val bexp =
	    case symbv of
		SymbValBE (exp,_) => exp
              | SymbValInterval ((exp1,exp2), _) => exp1 (* we need to fix it later*)
              | SymbValMem (exp, _, _, _) => exp (* we need to fix it later*)
	      | _ => raise ERR "symbval_bexp" "cannot handle symbolic value type";
    in
	bexp
    end;
      
fun check_feasible_exp be syst =
    let
      val vals  = SYST_get_vals syst;
      val pred_bvl = SYST_get_pred syst;

      val (pred_conjs, pred_deps) =
        List.foldr (collect_pred_expsdeps vals) ([], symbvalbe_dep_empty) pred_bvl;

      val pred_depsl_ = Redblackset.listItems pred_deps;
      val pred_depsl  = List.filter (is_bvar_bound vals) pred_depsl_;

      val valsl = List.map (fn bv => (bv, find_bv_val "check_feasible_eq" vals bv))
                           pred_depsl;
      val vals_eql =
        List.map symbval_eq_to_bexp valsl;

      (* start with no variable and no assertions *)
      val vars    = Redblackset.empty smtlib_vars_compare;
      val asserts = [];

      val env  = (SYST_get_env  syst);

      val bv_fr = find_bv_val "check_feasible_exp" env  (dest_BExp_Den be);

      val symbv = find_bv_val "check_feasible_exp" vals bv_fr;	  

      val pred = add_pred_eq (symbval_get_bexp symbv);

      val preds = add_pred pred;

	  val _ = print_term  (preds); 

      val exp = conj_preds_exps pred_conjs preds;

      val ref_exps = subset_mem_exp vals_eql exp;
	  
      val resultvalue = possible_target ref_exps (pred::pred_conjs) vars asserts vals_eql [];
    in
      resultvalue
    end;
     
    
end (* local *)

end (* outermost local *)

end (* struct *)

