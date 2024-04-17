open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavinggeneraldeductionTheory;
open parallelcompositiongeneraldeductionTheory;
open translate_to_sapicTheory;
open derived_rules_generaldeductionTheory;
open sbir_treeTheory;
open sapicplusTheory;
open messagesTheory;
open dolevyaoTheory;

val _ = new_theory "sbir_sapic_comp_DY";

val comptraces_sapic_def =
Define`
      comptraces_sapic ((MTrn1:('event1 + 'eventS, 'SPpred, (sbir_event, real,
                                              (bir_var_t, bir_exp_t)
                                              symb_interpret_t) stree, 'symb) mtrel),(Ded1:('SPpred) tded)) ((MTrn2:('event2 + 'eventS, DYpred, DYstate, Var_t) mtrel),(Ded2:(DYpred) tded)) (ded3:('SPpred + DYpred) tded) ((Sym:Var_t set),(P: ('SPpred + DYpred) set),(S1: (sbir_event, real,
                                              (bir_var_t, bir_exp_t)
                                              symb_interpret_t) stree),(S2: DYstate)) ((Sym':Var_t set),(P': ('SPpred + DYpred) set),(S1': (sbir_event, real,
                                              (bir_var_t, bir_exp_t)
                                              symb_interpret_t) stree),(S2': DYstate)) =
{(t: ((('event1 + 'eventS) + 'event2 + 'eventS) option list))|  
 (symbolicParlComp (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
}
`;

val comptraces_tree_def =
Define`
      comptraces_tree ((MTrn1:('event1 + 'eventS, 'SPpred, 'state1, Var_t) mtrel),(Ded1:('SPpred) tded)) ((MTrn2:('event2 + 'eventS, DYpred, DYstate, Var_t) mtrel),(Ded2:(DYpred) tded)) (ded3:('SPpred + DYpred) tded) ((Sym:Var_t set),(P: ('SPpred + DYpred) set),(S1: 'state1),(S2: DYstate)) ((Sym':Var_t set),(P': ('SPpred + DYpred) set),(S1': 'state1),(S2': DYstate)) =
{(t: ((('event1 + 'eventS) + 'event2 + 'eventS) option list))|  
 (symbolicParlComp (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
}
`;
        
val compose_sbir_sapic_vs_DY_thm = store_thm(
  "compose_sbir_sapic_vs_DY_thm",
  ``∀T0 Re0 NRe0 i Re NRe Tre (Sym:(Var_t -> bool)) (Sym':(Var_t -> bool)) (P:('SPpred + DYpred -> bool)) (P':('SPpred + DYpred -> bool)) (Ded:('SPpred) tded) (ded3:('SPpred + DYpred) tded).

        (
        (sim T0 (Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0))) ∧
        ((IMAGE (MAP sbirEvent_to_sapicFact) (traces_of_tree T0)) ⊆ (traces_of_sapic (Pconfig ((symbtree_to_sapic T0),0,Re0,NRe0))))
        ) ==> (
      (comptraces_tree (symbolic_tree_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,T0,ESt) (Sym',P',Tre,ESt)) ⊆
      (comptraces_sapic (sapic_position_multi_transitions_with_symb,Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,(Pconfig (Pr0,0,Re0,NRe0)),ESt) (Sym',P',(Pconfig (Pr,i,Re,NRe)),ESt))
      ) ``,
        rewrite_tac[binterleave_composition_generaldeduction,binterleave_ts,symbtree_to_sapic_trace_inclusion_thm] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[]


  );




val _ = export_theory();
