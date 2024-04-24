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




(*  

                
  GEN_TAC >>
  EQ_TAC >-(
    strip_tac >>
  Induct_on ‘x’ >- (
    metis_tac[bir_mrel_nil,arm8_mrel_nil]
    )(*NIL*) >>
    rpt strip_tac >>


        
    IMP_RES_TAC TranRelSnocRev >>
    PAT_X_ASSUM ``!s'. A `` (ASSUME_TAC o (Q.SPECL [‘bs'’]))>>
    PAT_X_ASSUM ``!s'. A `` (ASSUME_TAC o (Q.SPECL [‘bs'’]))>>
    IMP_RES_TAC bir_mrel_single >>
    IMP_RES_TAC bir_rel_def >>
    PAT_X_ASSUM ``!n' lo c_st. A `` (ASSUME_TAC o (Q.SPECL [‘n'’,‘lo’,‘c_st’]))>>
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) []>>
    rw[] >>
         
    IMP_RES_TAC arm8_rel_def >>
    IMP_RES_TAC arm8_mrel_single >>
    IMP_RES_TAC arm8_mrel_moveForw >>
    PAT_X_ASSUM ``!ms' mev. A `` (ASSUME_TAC o (Q.SPECL [‘ms'''’,‘x'’]))>>
    PAT_X_ASSUM ``!ms'' me. A `` (ASSUME_TAC o (Q.SPECL [‘ms'’,‘c_addr_labels’]))>>
    ASSUME_TAC (ISPECL [``(ms':arm8_state)``, ``(c_addr_labels:num)``, ``(ms':arm8_state)``] arm8_rel_def) >>
    
    RES_TAC

               
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [FUNPOW_OPT_def,arithmeticTheory.FUNPOW] >>
                  rw[option_case_def]
    ASSUME_TAC (ISPECL [``((λx. option_CASE x NONE arm8_bmr.bmr_step_fun):(arm8_state option -> arm8_state option))``, ‘(SOME ms'):arm8_state option’, ``(c_addr_labels:num)``, ``(SOME ms'):arm8_state option``] step_n_def) >> 
                  
                  rw[]
)(*bir to arm8*)                         

Cases_on ‘c_addr_labels’
        
     Cases_on ‘birprog’ >>
     Cases_on ‘interval’ >>
     FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [bmr_rel_def,bir_is_lifted_prog_def,bir_program_string_labels_guarded_def,bir_is_valid_labels_def,WI_wfe_def,bir_labels_of_program_def,bir_exec_to_addr_label_def,traces_def,MAP,EVERY_DEF,IMAGE_DEF,ALL_DISTINCT,EXTENSION,EVERY_CONJ,EVERY_FILTER,EXISTS_LIST_EQ_MAP,EVERY_MAP,arm8_bmr_def] >>
     PAT_X_ASSUM ``!ms bs li. A `` (ASSUME_TAC o (Q.SPECL [‘ms’,‘bs’,‘li’]))>>
     RES_TAC >>
     IMP_RES_TAC EVERY_CONJ
                 FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [] >>
     Induct_on ‘arm8prog’ >- (
      rewrite_tac[EVERY_DEF] >>
                 FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [bir_machine_lifted_imm_def,APPEND,arm8_PSTATE_lifted_imms_LIST_def,arm8_REGS_lifted_imms_LIST_def,arm8_EXTRA_lifted_imms_LIST_def] >>            
      rw[]>>
      RES_TAC
      )(*NIL*)




                 
                        
IMP_RES_TAC EVERY_FILTER
IMP_RES_TAC EXISTS_LIST_EQ_MAP
IMP_RES_TAC EVERY_MAP
FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) []
IMP_RES_TAC MAP_ID
RES_TAC
DB.find "EVERY"

WF_bmr_ms_mem_contains_def
FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [arm8_bmr_def]
bir_machine_lifted_imm_def
        
rewrite_tac[bmr_rel_def]

arm8_state_is_OK_def
RES_TAC


FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [bmr_rel_def,bir_is_lifted_prog_def,bir_program_string_labels_guarded_def,bir_is_valid_labels_def,WI_wfe_def,bir_labels_of_program_def,bir_exec_to_addr_label_def,traces_def,MAP,EVERY_DEF,IMAGE_DEF,ALL_DISTINCT,EXTENSION]




FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [traces_def,MAP,IMAGE_DEF,EXTENSION]
Induct_on ‘x’
rw[]


                
            rewrite_tac[bir_is_lifted_prog_def]>>
            rewrite_tac[bir_program_string_labels_guarded_def]
                       rewrite_tac[ bir_is_valid_labels_def]
                                    rewrite_tac[WI_wfe_def]
                                    Cases_on ‘birprog’
                                    Cases_on ‘interval’
                                             
                                    Cases_on ‘arm8prog’
                                              

rewrite_tac[bir_labels_of_program_def]
rewrite_tac[bir_exec_to_addr_label_def]
        
Cases_on ‘l’ >- (
FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) []
bir_program_string_labels_guarded_def
bmr_rel_def

bir_exec_to_addr_label_def

 )(*NIL*)             
         
  Q.EXISTS_TAC `ms` >>
       Q.EXISTS_TAC `bs` >>
       Q.EXISTS_TAC `ms'` >>
Q.EXISTS_TAC `bs'` >>
  rpt strip_tac >>
  PAT_X_ASSUM ``!ms bs li. A `` (ASSUME_TAC o (Q.SPECL [‘ms’,‘bs’,‘li’]))>>
     RES_TAC >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
     IMP_RES_TAC bir_is_valid_labels_def
                 Cases_on ‘birprog’
            IMP_RES_TAC bir_labels_of_program_def
                        
IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC

            bir_is_valid_labels_def
bir_state_is_terminated_def
bir_exec_step_n_REWR_NOT_TERMINATED
rw[bir_exec_step_n_REWRS]
bir_is_valid_labels_def
IMP_RES_TAC  bir_exec_step_n_REWRS

bir_exec_step_state




bir_exec_step_n_def

                
  );
  arch_t

arm8_step.NextStateARM8
 arm8_bmr_def

DB.find "bir_is_lifted_prog_MULTI_STEP_EXEC_compute"


bir_lifting_machinesTheory.bmr_rel_def

bir_backlifterTheory.bir_pre_arm8_to_bir_def
bir_backlifterTheory.bir_post_bir_to_arm8_def


(bir_exec_to_addr_label_n p bs n' = BER_Ended lo c_st c_addr_labels bs')

bir_inst_liftingTheory.bir_exec_to_addr_label_n_def
bir_inst_liftingTheory.bir_exec_to_addr_label_def
bir_programTheory.bir_exec_to_labels_n_def
bir_programTheory.bir_exec_to_labels_def

bir_programTheory.bir_exec_steps_GEN_def
bir_programTheory.bir_exec_infinite_steps_COUNT_STEPS_def
bir_programTheory.bir_exec_infinite_steps_fun_def
bir_programTheory.bir_exec_infinite_steps_fun_COUNT_PCs_def
bir_programTheory.bir_state_COUNT_PC_def

bir_wm_instTheory.bir_label_jgmt_impl_weak_jgmt

bir_htTheory.bir_exec_to_labels_triple_def

bir_program_terminationTheory???

bir_backlifterTheory.arm8_triple_def

                 
val compose_bir_attacker_vs_sbir_DY_thm = store_thm(
  "compose_bir_attacker_vs_sbir_DY_thm",
  ``∀T0 Re0 NRe0 i Re NRe Tre
            (Sym:(Var_t -> bool)) (Sym':(Var_t -> bool)) (P:('SPpred + DYpred -> bool)) (P':('SPpred + DYpred -> bool)) S2 S2' (SBIR:(SapicFact_t + (Name_t, Var_t) sync_event, 'SPpred, ((sbir_event, real, (bir_var_t, bir_val_t) symb_interpret_t) stree), Var_t) mtrel) (Ded:('SPpred) tded) (ded3':('SPpred + DYpred) tded).

        (
        (sim T0 (Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0))) ∧
        ((traces (SBIR,Ded) (Sym,(IMAGE OUTL P),T0) (Sym',(IMAGE OUTL P'),Tre)) ⊆
         (traces (sapic_position_multi_transitions_with_symb,Ded) (Sym,(IMAGE OUTL P),(Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0))) (Sym',(IMAGE OUTL P'),(Pconfig ((symbtree_to_sapic Tre,i,Re,NRe))))))
        ) ==> (
      (comptraces (BIR,bir_Ded) (Attmultranrel,Attdeduction) ded3 (Sym,P,T0,S2) (Sym',P',Tre,S2')) ⊆
      (comptraces (SBIR,sbir_Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,T0,S2) (Sym',P',Tre,S2'))
      ) ``,
        rewrite_tac[binterleave_composition_generaldeduction,binterleave_ts,symbtree_to_sapic_trace_inclusion_thm] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[]


  );


``!Sym Sym' P P' S1 S1' S2 S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded2:('pred2) tded) (Ded3:('pred1 + 'pred2) tded).
(
     (subset_one
      (traces ((InterpretRelOne:(( 'event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel # ('pred1) tded) -> ('cevent1 + 'ceventS, 'cstate1) mctrel) (MTrn1,Ded1)) ((InterpretStOne:'state1 -> 'cstate1) S1) ((InterpretStOne:'state1 -> 'cstate1) S1'))
      (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1'))) ∧
     (subset_two
      (traces ((InterpretRelTwo:(( 'event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel # ('pred2) tded) -> ( 'cevent2 + 'ceventS, 'cstate2) mctrel) (MTrn2,Ded2)) ((InterpretStTwo:'state2 -> 'cstate2) S2) ((InterpretStTwo:'state2 -> 'cstate2) S2'))
      (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2')))
) ==>
(subset_comp
   (comptraces (composeMuRe ((InterpretRelOne:(( 'event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel # ('pred1) tded) -> ('cevent1 + 'ceventS, 'cstate1) mctrel) (MTrn1,Ded1)) ((InterpretRelTwo:(( 'event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel # ('pred2) tded) -> ( 'cevent2 + 'ceventS, 'cstate2) mctrel) (MTrn2,Ded2))) (((InterpretStOne:'state1 -> 'cstate1) S1),((InterpretStTwo:'state2 -> 'cstate2) S2)) (((InterpretStOne:'state1 -> 'cstate1) S1'),((InterpretStTwo:'state2 -> 'cstate2) S2')))
   (comptraces (MTrn1,Ded1) (MTrn2,Ded2) Ded3 (Sym,P,S1,S2) (Sym',P',S1',S2'))
) ``



val lifted_to_traces_thm = store_thm(
  "lifted_to_traces_thm",
  ``!mu bs bs' ms ms' mla (p:'a bir_program_t)
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
     (
        (traces (bir_mrel p) bs bs') = (traces arm8_mrel ms ms')
     )
     ``,
     rpt strip_tac >>
  IMP_RES_TAC bir_is_lifted_prog_MULTI_STEP_EXEC_compute_GEN_thm >>
  FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [traces_def,MAP,IMAGE_DEF,EXTENSION] >>
  GEN_TAC >>
  EQ_TAC >-(
    strip_tac >>
  Induct_on ‘x’ >- (
    metis_tac[bir_mrel_nil,arm8_mrel_nil]
    )(*NIL*) >>
    rpt strip_tac >>
    IMP_RES_TAC TranRelSnocRev >>
    PAT_X_ASSUM ``!s'. A `` (ASSUME_TAC o (Q.SPECL [‘bs’]))>>
    PAT_X_ASSUM ``!s'. A `` (ASSUME_TAC o (Q.SPECL [‘bs'’]))>>
    RES_TAC >>
    IMP_RES_TAC bir_mrel_single >>
    IMP_RES_TAC bir_rel_def >>
    PAT_X_ASSUM ``!n' lo c_st. A `` (ASSUME_TAC o (Q.SPECL [‘n'’,‘lo’,‘c_st’]))>>
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) []>>
    rw[] >>
    IMP_RES_TAC arm8_rel_def >>
    IMP_RES_TAC arm8_mrel_single >>
    IMP_RES_TAC arm8_mrel_moveForw >>
    PAT_X_ASSUM ``!ms' mev. A `` (ASSUME_TAC o (Q.SPECL [‘ms'''’,‘x'’]))>>
    PAT_X_ASSUM ``!ms'' me. A `` (ASSUME_TAC o (Q.SPECL [‘ms'’,‘c_addr_labels’]))>>
    ASSUME_TAC (ISPECL [``(ms':arm8_state)``, ``(c_addr_labels:num)``, ``(ms':arm8_state)``] arm8_rel_def) >>
    
    RES_TAC

               
    FULL_SIMP_TAC (std_ss++listSimps.LIST_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss++abstract_hoare_logicSimps.bir_wm_SS++holBACore_ss) [FUNPOW_OPT_def,arithmeticTheory.FUNPOW] >>
                  rw[option_case_def]
    ASSUME_TAC (ISPECL [``((λx. option_CASE x NONE arm8_bmr.bmr_step_fun):(arm8_state option -> arm8_state option))``, ‘(SOME ms'):arm8_state option’, ``(c_addr_labels:num)``, ``(SOME ms'):arm8_state option``] step_n_def) >> 
                  
                  rw[]
)(*bir to arm8*)                         
    
*)

val _ = export_theory();
