open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open listTheory;
open parallelcompositionconcreteTheory;
open interleavingconcreteTheory;
open parallelcompositiongeneraldeductionTheory;
open interleavinggeneraldeductionTheory;
open derived_rules_generaldeductionTheory;
open bir_comp_attacker_vs_sbir_comp_DYTheory;
open arm8_vs_bir_comp_attackerTheory;
open sapic_comp_DY_sapicplusTheory;
open sbir_sapic_comp_DYTheory;
open traceinclusionTheory;
open bir_backlifterTheory;
open bir_program_multistep_propsTheory;
open arithmeticTheory;
open bir_auxiliaryTheory;
open optionTheory;
open HolBACoreSimps;
val _ = new_theory "instantiations";




val end_to_end_correctness_thm = store_thm(
  "end_to_end_correctness_thm",
  ``
  !mu ms mla (birprog:'observation_type bir_program_t)  mms n' lo c_st c_addr_labels
      (AMTrn:('attevent + 'ceventS, 'cstate) mctrel) Re0 NRe0 i Re NRe Pr0 Pr (Sym:(Var_t -> bool))
      (Sym':(Var_t -> bool)) (P:('SPpred + DYpred -> bool)) (P':('SPpred + DYpred -> bool))
      (T0:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree) (Tre:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree) (Ded:('SPpred) tded) (ded3:('SPpred + DYpred) tded).

    bir_is_lifted_prog arm8_bmr mu mms birprog ==>
    bmr_rel arm8_bmr ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0) ms ==>
    MEM (BL_Address mla) (bir_labels_of_program birprog) ==>
    (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0).bst_pc = bir_block_pc (BL_Address mla)) ==>
    EVERY (bmr_ms_mem_contains arm8_bmr ms) mms ==>
    (bir_exec_to_addr_label_n birprog ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0) n' =
     BER_Ended lo c_st c_addr_labels ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) Tre)) ==>
    ~bir_state_is_terminated ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0) ==>
    ~bir_state_is_terminated ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) Tre) ==>
    (∃ms'.
       (
       (arm8_att_comptraces ((arm8_mrel:arm8_state -> ('cevent + 'ceventS) list -> arm8_state -> bool) || AMTrn) (ms,((InterpretStTwo:DYstate -> 'cstate) ESt)) (ms',((InterpretStTwo:DYstate -> 'cstate) ESt))) =
       (bir_att_comptraces ((bir_mrel (birprog:'observation_type bir_program_t)) || AMTrn) (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0),((InterpretStTwo:DYstate -> 'cstate) ESt))  (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) Tre),((InterpretStTwo:DYstate -> 'cstate) ESt)))
       )
       ==>
       (subset_comp
        (bir_att_comptraces (composeMuRe (bir_mrel (birprog:'observation_type bir_program_t)) AMTrn) (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0),((InterpretStTwo:DYstate -> 'cstate) ESt)) (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) Tre),((InterpretStTwo:DYstate -> 'cstate) ESt)))
        (comptraces_tree (symbolic_tree_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,T0,ESt) (Sym',P',Tre,ESt))
       ) ==>
       ((IMAGE (MAP sbirEvent_vs_DY_to_sapicFact_vs_DY) (comptraces_tree (symbolic_tree_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,T0,ESt) (Sym',P',Tre,ESt))) ⊆
        (comptraces_sapic (sapic_position_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,(Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0)),ESt) (Sym',P',(Pconfig ((symbtree_to_sapic Tre),i,Re,NRe)),ESt))
       ) ==>
       (comptraces (sapic_position_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,(Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0)),ESt) (Sym',P',(Pconfig ((symbtree_to_sapic Tre),i,Re,NRe)),ESt)) =
       (sapic_plus_traces sapic_plus_position_multi_transitions_with_symb (Sym,P,(Pconfig_plus ((symbtree_to_sapic T0),0,Re0,NRe0))) (Sym',P',(Pconfig_plus ((symbtree_to_sapic Tre),i,Re,NRe))))
    )

    ``,
    
    rpt strip_tac >>
  IMP_RES_TAC compose_arm8_bir_vs_attacker_thm >>
  PAT_X_ASSUM ``!as'' as MTrn. A `` (ASSUME_TAC o (Q.SPECL [‘(InterpretStTwo ESt)’,‘(InterpretStTwo ESt)’,‘(AMTrn)’]))>>            
  REV_FULL_SIMP_TAC std_ss [] >>
  Q.EXISTS_TAC `ms''` >>
  rw[] >>
  metis_tac[comptraces_sapic_vs_DY_EQ_sapic_plus_traces_thm]
  (*ASSUME_TAC (ISPECL [“t:'a”,“Re0:sapic_renaming_t”, “NRe0:sapic_name_renaming_t”, “i:real”, “Re:sapic_renaming_t”, “NRe:sapic_name_renaming_t”, “((symbtree_to_sapic (T0:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree)):Process_t)”, “((symbtree_to_sapic (Tre:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree)):Process_t)”, “Sym:(Var_t -> bool)”, “Sym':(Var_t -> bool)”, “P:('SPpred + DYpred -> bool)”, “P':('SPpred + DYpred -> bool)”, “Ded:('SPpred) tded”, “ded3:('SPpred + DYpred) tded”] comptraces_sapic_vs_DY_EQ_sapic_plus_traces_thm) >>
 REV_FULL_SIMP_TAC std_ss [] *)
  )

val _ = export_theory();
