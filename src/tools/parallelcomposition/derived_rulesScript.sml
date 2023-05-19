open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open parallelcompositionTheory;
open propertyTheory;
open sigma_algebraTheory;


val _ = new_theory "derived_rules";

val composeDed_prop_thm = store_thm(
  "composeDed_prop_thm", ``
∀(ded1:('pred1) tded) (ded2:('pred2) tded) (P:('pred1 + 'pred2) set) (F1: 'pred1) (F2: 'pred2).
(composeDed ded1 ded2 P (INL F1) ==> (ded1 (IMAGE OUTL P) F1)) ∧
(composeDed ded1 ded2 P (INR F2) ==> (ded2 (IMAGE OUTR P) F2))
                                       ``,
  REPEAT GEN_TAC >>
  REWRITE_TAC [composeDed_def]
  );
  
val composeDed_commutative_pred1_thm = store_thm(
  "composeDed_commutative_pred1_thm", ``
∀(ded1:('pred1) tded) (ded2:('pred2) tded) (P:('pred1 + 'pred2) set) (P':('pred2 + 'pred1) set) (F: 'pred1).
(((IMAGE OUTL P) = (IMAGE OUTR P')) ∧ ((IMAGE OUTR P) = (IMAGE OUTL P'))) ⇒ (composeDed ded1 ded2 P (INL F) = composeDed ded2 ded1 P' (INR F))
                                       ``,
  REPEAT GEN_TAC >>
  REPEAT STRIP_TAC >>
  REWRITE_TAC [composeDed_def]>>
  ASM_SIMP_TAC std_ss []              
  );


val composeDed_commutative_pred2_thm = store_thm(
  "composeDed_commutative_pred2_thm", ``
∀(ded1:('pred1) tded) (ded2:('pred2) tded) (P:('pred1 + 'pred2) set) (P':('pred2 + 'pred1) set) (F: 'pred2).
(((IMAGE OUTL P) = (IMAGE OUTR P')) ∧ ((IMAGE OUTR P) = (IMAGE OUTL P'))) ⇒ (composeDed ded1 ded2 P (INR F) = composeDed ded2 ded1 P' (INL F))
                                       ``,
  REPEAT GEN_TAC >>
  REPEAT STRIP_TAC >>
  REWRITE_TAC [composeDed_def]>>
  ASM_SIMP_TAC std_ss []              
  );

 
val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!MTrn1 Ded1 MTrn2 Ded2 MTrn Ded (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 ((MTS1 ⊑ MTS2) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded))) ==> ((MTS1 || MTS) ⊑ (MTS2 || MTS)) ``
  ,
  
  REPEAT GEN_TAC >>        
  REWRITE_TAC [traceRefinement_def,traces_def,trace_rules,trace_cases,trace_ind,trace_cases,tracePropertyNot_def]>>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REWRITE_TAC [composeMultiOperation_def]>>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!Phi. A`` (ASSUME_TAC o (Q.SPECL [`Phi`]))>>
  Cases_on `MTS1 = MTS2 ∧ MTrn1 = MTrn2 ∧ Ded1 = Ded2`  >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>  
  EVERY [REPEAT STRIP_TAC] >>
  cheat
        );

(*
WIP                
SET_TAC [Q.SPECL [`MTS`, `t`] trace_cases,composeMuRe_cases,composeRel_def] 

       
REWRITE_TAC [composeMuRe_cases,composeRel_def]


 PSet_ind.SET_INDUCT_TAC 
 Induct_on `t`
PAT_X_ASSUM ``A = t`` (ASSUME_TAC o GSYM)

FULL_SIMP_TAC (std_ss) [listTheory.EVERY_DEF]
        

 DISCH_TAC >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC


  SIMP_TAC (std_ss ++ SET_SPEC_ss) []
*)




        
val _ = export_theory();

