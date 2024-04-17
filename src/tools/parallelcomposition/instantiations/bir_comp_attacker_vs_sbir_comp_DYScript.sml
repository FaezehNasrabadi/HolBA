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

val _ = new_theory "bir_comp_attacker_vs_sbir_comp_DY";

   (*  
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

  
*)

val _ = export_theory();
