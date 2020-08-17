structure bir_symbexec_coreLib =
struct

local
  open bir_symbexec_stateLib;

  open bir_constpropLib;
  open bir_envSyntax;
  open bir_exp_helperLib;
in (* outermost local *)


(* primitive for symbolic/abstract computation for expressions *)
local
  open bir_expSyntax;

  fun subst_fun env (bev, (e, vars)) =
    let
      val bv_ofvars = find_bv_val "subst_fun" env bev;
    in
      (subst_exp (bev, mk_BExp_Den bv_ofvars, e),
       bv_ofvars::vars)
    end;

  open bslSyntax;
  val var_add_const_match_tm = bplus (bden ``x:bir_var_t``, bconstimm ``y:bir_imm_t``);

  fun compute_val_try vals (besubst, besubst_vars) deps_l2 =
    let
      val all_deps_const = List.all (fn bv =>
             (is_bvar_bound vals) bv andalso
             (case find_bv_val "compute_val_try" vals bv of
                 SymbValBE (exp,_) => is_BExp_Const exp
               | _ => false)
           ) besubst_vars;

      val depends_on_single_interval =
             length besubst_vars = 1 andalso
             (is_bvar_bound vals) (hd besubst_vars) andalso
             (case find_bv_val "compute_val_try" vals (hd besubst_vars) of
                 SymbValInterval _ => true
               | _ => false);
    in
      if all_deps_const then
        if List.null besubst_vars then NONE else
        let
          val _ = if Redblackset.isEmpty deps_l2 then () else
                  raise ERR "compute_val_try" "deps_l2 is not empty. Unexpected here.";

          fun subst_fun_symbvalbe vals (bv_dep, e) =
            let
              val symbv_dep = find_bv_val "compute_val_try" vals bv_dep;
              val exp = case symbv_dep of
                           SymbValBE (exp,_) => exp
                         | _ => raise ERR "compute_val_try" "cannot happen";
            in
              subst_exp (bv_dep, exp, e)
            end;

          val becomp = List.foldr (subst_fun_symbvalbe vals) besubst besubst_vars;
        in
          SOME (SymbValBE (becomp, symbvalbe_dep_empty))
        end
      else if depends_on_single_interval then
        let
          val (vs, _) = hol88Lib.match var_add_const_match_tm besubst;
          val bv      = fst (List.nth (vs, 0));
          val imm_val = fst (List.nth (vs, 1));

          val _ = if identical bv (hd besubst_vars) then () else
                  raise ERR "compute_val_try" "something is not right 1...";

          val ((itv_exp1, itv_exp2), itv_deps) =
             (case find_bv_val "compute_val_try" vals bv of
                 SymbValInterval x => x
               | _ => raise ERR "compute_val_try" "something is not right 2...");

          fun add_const exp imm_val =
            if is_BExp_Den exp then bplus (exp, bconstimm imm_val) else
            let
              val (vs, _) = hol88Lib.match var_add_const_match_tm exp;
              val bv_       = fst (List.nth (vs, 0));
              val imm_val_2 = fst (List.nth (vs, 1));

              val add_tm = ``bir_bin_exp BIExp_Plus ^imm_val ^imm_val_2``;
              val res_tm = (snd o dest_eq o concl o EVAL) add_tm;
            in
              bplus (bden bv_, bconstimm res_tm)
            end;
        in
          SOME (SymbValInterval ((add_const itv_exp1 imm_val,
                                  add_const itv_exp2 imm_val),
                                 itv_deps))
        end
        handle HOL_ERR _ => NONE
      else
        NONE
    end;

  fun compute_val_and_resolve_deps vals (besubst, besubst_vars) =
    let
      val deps_l2 = List.foldr (Redblackset.union)
                               symbvalbe_dep_empty
                               (List.map (deps_find_symbval "compute_val_and_resolve_deps" vals) besubst_vars);
    in
      case compute_val_try vals (besubst, besubst_vars) deps_l2 of
         SOME x => x
       | NONE   =>
          let
            val deps = Redblackset.addList(deps_l2, besubst_vars);
            val be_new_val = SymbValBE (besubst, deps);
          in
            be_new_val
          end
    end;

in (* local *)
  fun compute_valbe be syst =
    let
      val env  = SYST_get_env  syst;
      val vals = SYST_get_vals syst;

      val be_vars = get_birexp_vars be;
      val besubst_with_vars = List.foldr (subst_fun env) (be, []) be_vars;
    in
      compute_val_and_resolve_deps vals besubst_with_vars
    end;
end (* local *)


(* primitive to compute expression and store result using fresh variable *)
  fun state_insert_symbval_from_be bv_fr be syst =
      insert_symbval bv_fr (compute_valbe be syst) syst;

(* primitive to carry out assignment *)
  fun state_assign_bv bv be syst =
    let
      val bv_fresh = (get_bvar_fresh) bv;
    in
      (update_envvar bv bv_fresh o
       state_insert_symbval_from_be bv_fresh be
      ) syst
    end;

  fun state_make_interval bv syst =
    let
      val env    = SYST_get_env syst;
      val bv_val = find_bv_val "state_make_interval" env bv;
      val _ = if is_bvar_init bv_val then () else
              raise ERR "state_make_interval" "can only make interval values from initial variables currently";

      val exp   = bir_expSyntax.mk_BExp_Den bv_val;
      val deps  = Redblackset.add (symbvalbe_dep_empty, bv_val);
      val symbv = SymbValInterval ((exp, exp), deps);

      val bv_fresh = (get_bvar_fresh) bv;
    in
      (update_envvar bv bv_fresh o
       insert_symbval bv_fresh symbv
      ) syst
    end;

(* primitives for adding conjuncts to the path predicate *)
local
  fun state_add_pred bv_str pred syst =
    let
      val bv = bir_envSyntax.mk_BVar_string (bv_str, bir_valuesSyntax.BType_Bool_tm);
      val bv_fresh = get_bvar_fresh bv;
    in
      (SYST_update_pred ((bv_fresh)::(SYST_get_pred syst)) o
       state_insert_symbval_from_be bv_fresh pred
      ) syst
    end;
in (* local *)
  fun state_add_preds bv_str preds syst =
    List.foldr (fn (pred, syst_) => state_add_pred bv_str pred syst_) syst preds;
end (* local *)

(* primitives for branching states based on a boolean condition expression *)
  fun state_branch str_prefix cnd f_bt f_bf syst =
    let
        val cnd_bv = bir_envSyntax.mk_BVar_string (str_prefix ^ "_cnd", bir_valuesSyntax.BType_Bool_tm);
        val cnd_bv_t = get_bvar_fresh cnd_bv;
        val cnd_bv_f = get_bvar_fresh cnd_bv;
    in
        List.concat [
          (f_bt o
           SYST_update_pred ((cnd_bv_t)::(SYST_get_pred syst)) o
           state_insert_symbval_from_be cnd_bv_t cnd
          ) syst
         ,
          (f_bf o
           SYST_update_pred ((cnd_bv_f)::(SYST_get_pred syst)) o
           state_insert_symbval_from_be cnd_bv_f (bslSyntax.bnot cnd)
          ) syst
        ]
    end;

  fun state_branch_simp str_prefix cnd f_bt f_bf syst =
      state_branch str_prefix cnd (fn s => [f_bt s]) (fn s => [f_bf s]) syst

end (* outermost local *)

end (* struct *)