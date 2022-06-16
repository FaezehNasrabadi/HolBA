(* these dependencies probably need cleanup *)
(* ================================================ *)
open HolKernel boolLib liteLib simpLib Parse bossLib;
open bir_inst_liftingTheory
open bir_lifting_machinesTheory
open bir_lifting_machinesLib bir_lifting_machinesLib_instances;
open bir_interval_expTheory bir_update_blockTheory
open bir_exp_liftingLib bir_typing_expSyntax
open bir_typing_expTheory
open bir_extra_expsTheory
open bir_lifter_general_auxTheory
open bir_programSyntax bir_interval_expSyntax
open bir_program_labelsTheory
open bir_immTheory
open intel_hexLib
open bir_inst_liftingLibTypes
open PPBackEnd Parse

open bir_inst_liftingHelpersLib;
(* ================================================ *)

open bir_wm_instTheory;

open bir_prog_freuseTheory;
open freuse_wpTheory freuse_smtTheory;

open bir_wp_interfaceLib;

open bir_compositionLib;

open HolBACoreSimps;

val _ = new_theory "freuse_composition";

val bir_att_sec_add_1_comp_ct =
(* TODO: Why not use
  label_ct_to_simp_ct_predset
    bir_att_sec_add_1_ht
    contract_1_imp_taut_thm;
  ?
*)
  use_pre_str_rule_simp
    (HO_MATCH_MP (HO_MATCH_MP bir_label_jgmt_impl_weak_jgmt (not_empty_set (get_contract_ls bir_att_sec_add_1_ht))) bir_att_sec_add_1_ht)
    contract_1_imp_taut_thm;

val bir_att_sec_call_1_ct = bir_att_sec_call_1_ht;
val bir_att_sec_call_2_ct = bir_att_sec_call_2_ht;

(* TODO: in composition function, make conditional "return" jump work *)
(* TODO: enable usage of variable blacklist set with assumptions -> bigger compositional reasoning *)


fun try_disch_all_assump_w_EVAL t =
  let
    val t_d      = DISCH_ALL t;
    val assum_tm = (fst o dest_imp o concl) t_d;
    val t_as     = EVAL assum_tm;
    val t2       = REWRITE_RULE [t_as] (DISCH assum_tm t)
  in
    try_disch_all_assump_w_EVAL t2
  end
  handle HOL_ERR _ => t;

(* ====================================== *)
(* Turn the contracts generated by WP tool into compositional ones *)

(* TODO: Make label_ct_to_simp_ct_predset_assmpt *)
val att_sec_add_assmpt = ``((v3:word32) <> 260w) /\ ((v4:word32) <> 260w) /\ (v4 <> v3)``;

(*
(* -------------------------------------------------------- *)
(* Didrik's code to mechanize (works without variable set v4s) *)

val bir_att_sec_add_1_comp_ct =
  label_ct_to_simp_ct_assmpt_predset
    bir_att_sec_add_1_ct
    contract_1_imp_taut_thm
    att_sec_add_assmpt;

val bir_att_sec_add_2_comp_ct =
  label_ct_to_simp_ct_no_taut_assmpt_predset
    bir_att_sec_add_2_ct
    att_sec_add_assmpt;

(* -------------------------------------------------------- *)
*)

val bir_att_sec_call_1_comp_ct =
  label_ct_to_simp_ct_predset
    bir_att_sec_call_1_ct
    contract_2_imp_taut_thm;

val bir_att_sec_call_2_comp_ct =
  label_ct_to_simp_ct_predset
    bir_att_sec_call_2_ct
    contract_3_imp_taut_thm;


(* ====================================== *)
(* ADD function *)

(*
(* -------------------------------------------------------- *)
(* Didrik's code to mechanize the big chunk up to call 1 (works without variable set v4s) *)

val bir_att_sec_add_ct =
  bir_compose_seq_assmpt_predset
    bir_att_sec_add_1_comp_ct
    bir_att_sec_add_2_comp_ct
    [] att_sec_add_assmpt;

(* -------------------------------------------------------- *)
*)

  val ct_assmpt = ``(FINITE v4s) /\
                    ((BL_Address (Imm32 v3)) NOTIN v4s) /\
                    ((BL_Address (Imm32 260w)) NOTIN ((BL_Address (Imm32 v3)) INSERT v4s))``;

  val assumes = ASSUME ct_assmpt;

val notin_insert_neq_thm = prove(``!set el. el NOTIN set ==> (set <> el INSERT set)``,

REPEAT STRIP_TAC >>
subgoal `el IN (el INSERT set')` >- (
  FULL_SIMP_TAC (std_ss++pred_setLib.PRED_SET_ss) []
) >>
METIS_TAC [pred_setTheory.NOT_EQUAL_SETS]
);
  val fix3_thm = (UNDISCH_ALL o prove) (``
^ct_assmpt ==>
(!l.
          l IN BL_Address (Imm32 v3) INSERT v4s ==>
          ((if l = BL_Address (Imm32 260w) then
              bir_att_sec_add_1_post v1 v2 v3
            else bir_exp_false) =
           bir_exp_false))``,
  REPEAT STRIP_TAC >>
  CASE_TAC >>
  METIS_TAC []
);
  val fix3_2_thm = (UNDISCH_ALL o prove) (``
^ct_assmpt ==>
(!l.
          l IN v4s ==>
          ((if l = BL_Address (Imm32 v3) then
              bir_att_sec_add_2_post v1 v2
            else bir_exp_false) =
           bir_exp_false))``,
  REPEAT STRIP_TAC >>
  CASE_TAC >>
  METIS_TAC []
);


  fun fix_assmt ct =
    REWRITE_RULE [(SIMP_CONV (std_ss++pred_setLib.PRED_SET_ss) [assumes] o
                  fst o dest_imp o concl) ct] ct;

  fun fix_assmt2 ct =
    let
      val ante_term = (fst o dest_imp o concl) ct
      val ante_term2 =
        EQT_ELIM (
          SIMP_CONV std_ss [assumes, pred_setTheory.SUBSET_OF_INSERT,
                            pred_setTheory.PSUBSET_DEF, notin_insert_neq_thm]
            ante_term
        )
    in
      SIMP_RULE std_ss [ante_term2] ct
    end;

  fun fix_assmt3 ct =
    REWRITE_RULE [(SIMP_CONV std_ss [fix3_thm, fix3_2_thm] o
                  fst o dest_imp o concl) ct] ct;

  fun populate_blacklist_set_hack elabels simp_ct =
    let
      val simp_ct1 =
	((SPEC elabels) o
	 (HO_MATCH_MP bir_simp_wl_to_bl_set_rule_thm))
	simp_ct;
      val simp_ct1_1 = fix_assmt simp_ct1;
      val simp_ct1_2 = fix_assmt2 simp_ct1_1;
      val simp_ct1_3 = fix_assmt3 simp_ct1_2;
      val simp_ct1 =
        REWRITE_RULE [pred_setTheory.UNION_EMPTY,
		      pred_setTheory.INSERT_DIFF,
		      pred_setTheory.COMPONENT,
		      (REWRITE_RULE [pred_setTheory.SUBSET_OF_INSERT]
		       (Q.SPECL [`a`,`b INSERT a`] pred_setTheory.SUBSET_DIFF_EMPTY)),
		      pred_setTheory.DIFF_EQ_EMPTY,
		      assumes]
		     simp_ct1_3
    in
      simp_ct1
    end;

(* For debugging:
  val elabels = ``(BL_Address (Imm32 v3)) INSERT v4s``;
  val simp_ct = bir_att_sec_add_1_comp_ct;
*)
  val simp_ct1 = populate_blacklist_set_hack ``(BL_Address (Imm32 v3)) INSERT v4s`` bir_att_sec_add_1_comp_ct;

  val ct2_undisch = ((UNDISCH o UNDISCH o (Q.SPECL [`v1`, `v2`, `v3`, `v4s`])) bir_att_sec_add_2_ht);
  val simp_ct2_ = 
    HO_MATCH_MP
      (HO_MATCH_MP bir_label_jgmt_impl_weak_jgmt (not_empty_set (get_contract_ls ct2_undisch))) ct2_undisch;


(* For debugging:
  val elabels = ``v4s:bir_label_t->bool``;
  val simp_ct = simp_ct2_;
*)
  val simp_ct2 = populate_blacklist_set_hack ``v4s:bir_label_t->bool`` simp_ct2_;


(* For debugging:
  val def_list = [bprog_add_times_two_def, bir_att_sec_add_2_post_def,
		  bir_att_sec_add_1_post_def];

  val assmpt = ct_assmpt;
*)
  val bir_att_sec_add_ct =
    bir_compose_seq_assmpt_predset simp_ct1 simp_ct2 [freuse_def, bir_att_sec_add_2_post_def, bir_att_sec_add_1_post_def] ct_assmpt;


(* ====================================== *)
(* call 1 *)
val bir_att_sec_add_0x4_ct = (try_disch_all_assump_w_EVAL o
                              ((INST [``v3:word32`` |-> ``0x004w:word32``,
                                      ``v4s:bir_label_t->bool`` |-> ``{BL_Address (Imm32 0x008w)}``])))
                             bir_att_sec_add_ct;

val bir_att_sec_call_1_simp_ct =
  bir_compose_seq_predset
    bir_att_sec_call_1_comp_ct
    bir_att_sec_add_0x4_ct
    [bir_att_sec_call_1_post_def, bir_att_sec_add_1_pre_def];


(* ====================================== *)
(* call 2 *)
val bir_att_sec_add_0x8_ct = (try_disch_all_assump_w_EVAL o
                              ((INST [``v3:word32`` |-> ``0x008w:word32``,
                                      ``v4s:bir_label_t->bool`` |-> ``{}:bir_label_t->bool``,
                                      ``v2:word32`` |-> ``v1:word32``])))
                             bir_att_sec_add_ct;

val bir_att_sec_call_2_simp_ct =
  bir_compose_seq_predset
    bir_att_sec_call_2_comp_ct
    bir_att_sec_add_0x8_ct
    [bir_att_sec_call_2_post_def, bir_att_sec_add_1_pre_def];


(* ====================================== *)
(* composition of the function body *)
val bir_att_sec_call_2_simp_ct_inst =
  inst_vars bir_att_sec_call_2_simp_ct
    [(``v1:word32``, ``(v1:word32) + (v2:word32)``)];

val bir_att_sec_call_2_simp_ct_fix =
  use_pre_str_rule_simp
    bir_att_sec_call_2_simp_ct_inst
    bir_att_sec_call_1_taut_thm;

val bir_att_body_simp_ct =
  bir_compose_seq_predset
    bir_att_sec_call_1_simp_ct
    bir_att_sec_call_2_simp_ct_fix
    [];

(* experiment with postcondition weakening *)
val bir_att_sec_call_1_simp_ct_alt =
  use_post_weak_rule_simp
    bir_att_sec_call_1_simp_ct
    ``BL_Address (Imm32 4w)``
    bir_att_sec_call_1_taut_thm;

val bir_att_body_simp_ct_alt =
  bir_compose_seq_predset
    bir_att_sec_call_1_simp_ct_alt
    bir_att_sec_call_2_simp_ct_inst
    [];

val _ =
  if identical (concl bir_att_body_simp_ct_alt) (concl bir_att_body_simp_ct)
  then ()
  else
    raise ERR "composition of example code"
              "composition using two types of contract weakening does not give the same result";


(* ====================================== *)
(* final composition, needs postcondition weakening *)
val bir_att_post_ct =
  use_post_weak_rule_simp
    bir_att_body_simp_ct_alt
    ``BL_Address (Imm32 8w)``
    bir_att_post_taut_thm;


(* ====================================== *)
(* store theorem after final composition *)
val bir_att_ct = save_thm("bir_att_ct",
  REWRITE_RULE [bir_att_sec_2_post_def, bir_att_sec_call_1_pre_def]
    bir_att_post_ct
);

val _ = export_theory();
