(* HOL_Interactive.toggle_quietdec(); *)
open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavingconcreteTheory;
open parallelcompositionconcreteTheory;
open translate_to_sapicTheory;
open sbir_treeTheory;
open sapicplusTheory;
open messagesTheory;
open dolevyaoTheory;
open traceinclusionTheory;
open XORexampleTheory;
open bir_programTheory;
open bir_program_valid_stateTheory;
open HolBACoreSimps;
open bir_backlifterTheory;
open bir_program_multistep_propsTheory;
open arithmeticTheory;
open bir_auxiliaryTheory;
open optionTheory;
(* HOL_Interactive.toggle_quietdec(); *)

val _ = new_theory "arm8_vs_bir_comp_attacker";


Inductive arm8_mrel:
[~nil:]
  (arm8_mrel ms ([]:('cevent + 'ceventS) list) ms) /\
[~moveForw:]
  (
  ((arm8_mrel ms (mev:('cevent + 'ceventS) list) ms'')∧(arm8_mrel ms'' ([me]:('cevent + 'ceventS) list) ms'))
  ==> (arm8_mrel ms ((me::mev):('cevent + 'ceventS) list) ms')
  )/\
[~moveBack:]
  (
  ((arm8_mrel ms ((me::mev):('cevent + 'ceventS) list) ms')∧(arm8_mrel ms'' ([me]:('cevent + 'ceventS) list) ms'))
  ==> (arm8_mrel ms (mev:('cevent + 'ceventS) list) ms'')
  )
End                                

Inductive bir_mrel:
[~nil:]
 (bir_mrel p bs ([]:('cevent + 'ceventS) list) bs) /\
[~moveForw:]
  (
  ((bir_mrel birprog bs (bev:('cevent + 'ceventS) list) bs'')∧(bir_mrel birprog bs ([be]:('cevent + 'ceventS) list) bs'))
  ==> (bir_mrel birprog bs ((be::bev):('cevent + 'ceventS) list) bs')
  )/\
[~moveBack:]
  (
  ((bir_mrel birprog bs ((be::bev):('cevent + 'ceventS) list) bs')∧(bir_mrel birprog bs ([be]:('cevent + 'ceventS) list) bs'))
  ==> (bir_mrel birprog bs (bev:('cevent + 'ceventS) list) bs'')
  )
End                                


(*                        
val arch_t = List.nth((snd o strip_comb o concl) XORexampleTheory.XORexample_thm, 0);
val arch_def = Define `
    arch = ^(arch_t)
                `;
                
val interval_t = List.nth((snd o strip_comb o concl) XORexampleTheory.XORexample_thm, 1);
val interval_def = Define `
    interval = ^(interval_t)
                `;
                
val arm8prog_t = List.nth((snd o strip_comb o concl) XORexampleTheory.XORexample_thm, 2);
val arm8prog_def = Define `
    arm8prog = ^(arm8prog_t)
             `;

val birprog_t = List.nth((snd o strip_comb o concl) XORexampleTheory.XORexample_thm, 3);
val birprog_def = Define `
    birprog = ^(birprog_t)
`;


val lifter_thm = REWRITE_RULE [GSYM arch_def,GSYM interval_def,GSYM arm8prog_def,GSYM birprog_def] XORexampleTheory.XORexample_thm;
*)

(* =================================================================================== *)

(* NOTATION: FROM PROOF-PRODUCING SYMBOLIC EXECUTION -- adjusted/generalized from "bir_backlifterTheory.bir_is_lifted_prog_MULTI_STEP_EXEC_compute" *)
(* =================================================================================== *)
val bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm =
  prove(
  ``!mu bs bs' ms mla (p:'a bir_program_t) (r:('c, 'd, 'b) bir_lifting_machine_rec_t)
      mms n' lo c_st c_addr_labels.
    bir_is_lifted_prog r mu mms p ==>
    bmr_rel r bs ms ==>
    MEM (BL_Address mla) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address mla)) ==>
    EVERY (bmr_ms_mem_contains r ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
    ?ms' li.
    (FUNPOW_OPT r.bmr_step_fun c_addr_labels ms = SOME ms') /\
    bmr_ms_mem_unchanged r ms ms' mu /\
    EVERY (bmr_ms_mem_contains r ms') mms /\
    (bs'.bst_pc = bir_block_pc (BL_Address li)) /\
    MEM (BL_Address li) (bir_labels_of_program p) /\
    bmr_rel r bs' ms'
``,

REPEAT STRIP_TAC >>
ASSUME_TAC (ISPECL [``r:('c, 'd, 'b) bir_lifting_machine_rec_t``, ``mu:'c word_interval_t``,
                    ``mms:(('c word)# ('d word) list) list``,
                    ``p:'a bir_program_t``] bir_inst_liftingTheory.bir_is_lifted_prog_MULTI_STEP_EXEC) >>
REV_FULL_SIMP_TAC std_ss [] >>
bir_auxiliaryLib.QSPECL_X_ASSUM ``!n ms bs. _`` [`n'`, `ms`, `bs`] >>
REV_FULL_SIMP_TAC (std_ss++holBACore_ss) [bir_programTheory.bir_state_is_terminated_def]
);

val bmr_rel_to_mrel = new_axiom ("bmr_rel_to_mrel",
``∀p r bs ms bs' ms' (x:('cevent + 'ceventS) list).
     ((bmr_rel r bs ms)∧(bmr_rel r bs' ms')) ⇔ ((bir_mrel p bs x bs')∧(arm8_mrel ms x ms'))``)
     
val lifted_to_traces_thm = store_thm(
  "lifted_to_traces_thm",
  ``!mu bs bs' ms mla (p:'a bir_program_t)
      mms n' lo c_st c_addr_labels.
    bir_is_lifted_prog arm8_bmr mu mms p ==>
    bmr_rel arm8_bmr bs ms ==>
    MEM (BL_Address mla) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address mla)) ==>
    EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
     (∃bs'' ms''.
        (traces (bir_mrel p) bs bs'') = (traces arm8_mrel ms ms'')
     )
     ``,
     FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [traces_def,MAP,IMAGE_DEF,EXTENSION] >>
  rpt strip_tac >>
  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm >>
   Q.EXISTS_TAC `bs'` >>
  Q.EXISTS_TAC `ms'` >>
  metis_tac[bmr_rel_to_mrel]
)

val lifted_to_traces_eventS_thm =
  INST_TYPE
    [Type.gamma |-> ``:'ceventS``]
    lifted_to_traces_thm;

val compose_arm8_bir_vs_attacker_thm = store_thm(
  "compose_arm8_bir_vs_attacker_thm",
  ``!mu bs bs' ms mla (p:'a bir_program_t)
      mms n' lo c_st c_addr_labels (MTrn:('cevent + 'ceventS, 'cstate) mctrel) as as''.
    bir_is_lifted_prog arm8_bmr mu mms p ==>
    bmr_rel arm8_bmr bs ms ==>
    MEM (BL_Address mla) (bir_labels_of_program p) ==>
    (bs.bst_pc = bir_block_pc (BL_Address mla)) ==>
    EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ==>
    (bir_exec_to_addr_label_n p bs n' =
         BER_Ended lo c_st c_addr_labels bs') ==>
    ~bir_state_is_terminated bs ==>
    ~bir_state_is_terminated bs' ==>
     (∃bs'' ms''.
        ((comptraces ((bir_mrel p) || MTrn) (bs,as) (bs'',as'')) = (comptraces (arm8_mrel || MTrn) (ms,as) (ms'',as'')))
     )
     ``,
     rpt strip_tac >>
  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm >>             
  IMP_RES_TAC lifted_to_traces_eventS_thm >>
  Q.EXISTS_TAC `bs''` >>
  Q.EXISTS_TAC `ms''` >>
  ‘traces MTrn as as'' = traces MTrn as as''’  by (SIMP_TAC std_ss []) >>       
  SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [binterleave_composition_concrete,binterleave_ts,MAP,IMAGE_DEF,EXTENSION] >>
  GEN_TAC >>
  EQ_TAC >-(
    rpt strip_tac >>
    Q.EXISTS_TAC `t1` >>
    Q.EXISTS_TAC `t2` >>
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [traces_def] >>
    IMP_RES_TAC EXTENSION >>
    PAT_X_ASSUM ``!x. A `` (ASSUME_TAC o (Q.SPECL [‘t1’]))>>
    PAT_X_ASSUM ``!x. A `` (ASSUME_TAC o (Q.SPECL [‘t1’]))>>
    PAT_X_ASSUM ``!x. A `` (ASSUME_TAC o (Q.SPECL [‘t1’]))>>
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) []
    )(*end of bir to arm8*) >>
  rpt strip_tac >>
  Q.EXISTS_TAC `t1` >>
  Q.EXISTS_TAC `t2` >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [traces_def] >>
  IMP_RES_TAC EXTENSION >>
  PAT_X_ASSUM ``!x. A `` (ASSUME_TAC o (Q.SPECL [‘t1’]))>>
  PAT_X_ASSUM ``!x. A `` (ASSUME_TAC o (Q.SPECL [‘t1’]))>>
  PAT_X_ASSUM ``!x. A `` (ASSUME_TAC o (Q.SPECL [‘t1’]))>>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) []  
  )


val _ = export_theory();
