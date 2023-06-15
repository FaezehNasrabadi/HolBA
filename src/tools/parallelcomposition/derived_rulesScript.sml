open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open parallelcompositionTheory;
open propertyTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
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

(*
val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!MTrn1 Ded1 MTrn2 Ded2 MTrn Ded (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 ((MTS1 ⊑ MTS2) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded))) ==> ((MTS1 || MTS) ⊑ (MTS2 || MTS)) ``
  ,
  
  REPEAT GEN_TAC >>
  REWRITE_TAC [traceRefinement_def]>>
              REWRITE_TAC [traces_def]>>
              REWRITE_TAC [trace_def]>>
           ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
                          REPEAT STRIP_TAC >>
                             Cases_on `MTS1 = MTS2`  >>
 FULL_SIMP_TAC (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) []>>
 
                         REPEAT EQ_TAC >> REPEAT STRIP_TAC >>
                         PAT_X_ASSUM ``!t. A`` (ASSUME_TAC o (Q.SPECL [`t`]))>>
Q.EXISTS_TAC `MTrn'` >> Q.EXISTS_TAC `Ded'` >>
REPEAT STRIP_TAC >>
CONJUNCT2

        DISCH                 
  REWRITE_TAC [traceRefinement_def,traces_def]>>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REWRITE_TAC [composeMultiOperation_def]>>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``?MTrn' Ded'. A`` (ASSUME_TAC o (Q.SPECL [`MTrn'`,`Ded'`])) >>
  Cases_on `MTS1 = MTS2 ∧ MTrn1 = MTrn2 ∧ Ded1 = Ded2`  >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>  
  EVERY [REPEAT GEN_TAC] >>
  cheat
        );

 FULL_SIMP_TAC (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) []
WIP                
SET_TAC [Q.SPECL [`MTS`, `t`] trace_cases,composeMuRe_cases,composeRel_def] 

       
REWRITE_TAC [composeMuRe_def]
REWRITE_TAC [evtrace_def]

 PSet_ind.SET_INDUCT_TAC 
 Induct_on `t`
PAT_X_ASSUM ``A = t`` (ASSUME_TAC o GSYM)

FULL_SIMP_TAC (std_ss) [listTheory.EVERY_DEF]
        

 UNDISCH_TAC `` (∀Conf Conf' e ev.
           (MTrn1 Conf [] Conf' ⇒ x = [] ∧ Conf = Conf') ∧
           (MTrn1 Conf (e::ev) Conf' ⇒ x = e::ev ∧ Conf ≠ Conf')) ⇒
        ∀Conf Conf' e ev.
          (MTrn2 Conf [] Conf' ⇒ x = [] ∧ Conf = Conf') ∧
          (MTrn2 Conf (e::ev) Conf' ⇒ x = e::ev ∧ Conf ≠ Conf')`` >> ONCE_ASM_REWRITE_TAC [] >> POP_ASSUM K_TAC


  SIMP_TAC (std_ss ++ SET_SPEC_ss) []

 REWRITE_TAC [ASSUME ``case [] of
          [] => x = [] ∧ Conf = Conf'
        | v2::v3 => x = [] ∧ Conf ≠ Conf'``]



REWRITE_TAC [traceRefinement_def]>>
              REWRITE_TAC [traces_def]>>
              REWRITE_TAC [trace_def]>>
ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) [] >>
REPEAT GEN_TAC >>
REPEAT EQ_TAC >>
ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>

       Cases_on `MTrn1 = MTrn2 ∧ Ded1 = Ded2`  >>
       ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
       FULL_SIMP_TAC (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) [] >>
       REPEAT STRIP_TAC >>
       REPEAT EQ_TAC >>
val thm = ASSUME ``(!Conf Conf' e ev. A) ==> B``;
val term = UNDISCH thm;
DISCH_TAC THEN (ASSUME_TAC (ASSUME ``(!Conf Conf' e ev. A) ==> B``));

        REWRITE_TAC [traceRefinement_def,traces_def]>>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REWRITE_TAC [composeMultiOperation_def]>>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REPEAT STRIP_TAC >>
  REPEAT EQ_TAC >> REPEAT STRIP_TAC >>
  PAT_X_ASSUM ``!t. A`` (ASSUME_TAC o (Q.SPECL [`t`]))>>
  Q.EXISTS_TAC `Conf` >> Q.EXISTS_TAC `Conf'` >>
  Induct_on `t` >>
  ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []>>
  REPEAT GEN_TAC >>


REV_FULL_SIMP_TAC (std_ss) []
  FULL_SIMP_TAC (srw_ss()) []
REV_FULL_SIMP_TAC (arith_ss) []
  ASM_SIMP_TAC (list_ss) []

  ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
Q.EXISTS_TAC `Conf` >> Q.EXISTS_TAC `Conf'` >>
  
 REWRITE_TAC [listTheory.LENGTH_EQ_CONS]
        PAT_X_ASSUM ``?Conf Conf'. A`` (ASSUME_TAC o (Q.SPECL [`Conf`,`Conf'`]))
        METIS_TAC [evtrace_def,composeMuRe_def,composeRel_def]
        ALL_TAC

        PAT_X_ASSUM ``!t. t = e::ev`` (ASSUME_TAC o (Q.SPECL [`t`,`e`,`ev`]))
*)




        
val _ = export_theory();

(*
val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 ((MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
)==> (MTS1 ⊑ MTS2) ==> ((MTS1 || MTS) ⊑ (MTS2 || MTS)) ``
  ,
       POP_ASSUM (ASSUME_TAC (DISCH_ALL (ASSUME ``(!Conf Conf' e ev. A) ==> B``)) )
       PAT_X_ASSUM ``(!Conf Conf' e ev. A) ==> B`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]))       
DISCH_TAC
REWRITE_TAC [traceRefinement_def] >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
REWRITE_TAC [composeMultiOperation_def]
REWRITE_TAC [traces_def] >>
ASM_REWRITE_TAC [trevtrace_def]
ASM_REWRITE_TAC [evtrace_def]
Cases_on `MTrn1 = MTrn2` 
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
REPEAT STRIP_TAC
IMP_REWRITE_RULE I
UNDITSH
ASM_CASES_TAC ``x = []``
ASM_REWRITE_TAC [ASSUME ``Conf = (Sym,P,S)``]
`(MTrn1 Conf [] Conf) ∨ (MTrn2 Conf' [] Conf')` by DECIDE_TAC
              
ASM_REWRITE_TAC[Q.SPECL [`Conf`, `Conf'`] composeMuRe_def]
             
SET_TAC [Q.SPECL [`Conf`, `Conf'`] composeMuRe_def]        
FULL_SIMP_TAC std_ss []
ASM_CASES_TAC        
ASM_REWRITE_TAC []
FULL_SIMP_TAC (simpLib.++(bossLib.bool_ss, boolSimps.LET_ss)) [composeMuRe_def]
RES_TAC
IMP_RES_TAC(evtrace_def)
IMP_RES_TAC(evtrace_def)
            DB.find_in "NOT" (DB.find "SUBSET");
        DB.find "CASE";
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t

rw[]
REWRITE_TAC [NOT_CONS_NIL]
(MATCH_MP_TAC ( tautLib.TAUT_PROVE ``if p then x = [] /\ Conf = Conf' else q``)) `case [] of [] => x = [] /\ Conf = Conf' | v2::v3 => x = [] /\ Conf ≠ Conf'
CONV_TAC (REDEPTH_CONV (RATOR_CONV (RAND_CONV (REWR_CONV `case [] of [] => x = [] /\ Conf = Conf' | v2::v3 => x = [] /\ Conf <> Conf'`)))) []

val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTS1) ⊆ (traces MTS2)) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((comptraces (MTS1 || MTS)) ⊆ (comptraces (MTS2 || MTS))) ``
  ,
       
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
REWRITE_TAC [composeMultiOperation_def]>>
REWRITE_TAC [comptraces_def] >>
REWRITE_TAC [traces_def] >>
REPEAT GEN_TAC>>
Cases_on `MTrn1 = MTrn2` >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
ASM_REWRITE_TAC [SUBSET_DEF]>>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>          
REPEAT STRIP_TAC>>
PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]))>>
PAT_X_ASSUM ``∀x. A`` (ASSUME_TAC o (Q.SPECL [`x`]))>>
PAT_X_ASSUM ``!Sym P S Sym' P' S'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S`,`Sym'`,`P'`,`S'`]))>>      
Induct_on `t'`
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
rw[]
Induct_on `x`
listTheory.MEM
        Induct_on `t'`
Cases_on `Conf'' = Conf'³'`
ISR INR
RES_TAC
CONJUNCTS_TAC o SPEC_ALL
  Cases_on `OUTL(x') ∈ LIST_TO_SET(x)`
  Cases_on `(IMAGE OUTL (LIST_TO_SET(x'))) = LIST_TO_SET(x)`
  IMAGE OUTL      
Q.EXISTS_TAC `Sym` >> Q.EXISTS_TAC `P` >>
            Q.EXISTS_TAC `S1` >> Q.EXISTS_TAC `S2` >>
            Q.EXISTS_TAC `Sym'` >> Q.EXISTS_TAC `P'` >>
            Q.EXISTS_TAC `S1'` >> Q.EXISTS_TAC `S2'` >>
      IMP_RES_TAC(composeMuRe_def)
      SRW_TAC[][]
      REWRITE_TAC[ASSUME ``Conf = (Sym,P1<+>P,S1,S')``] by PROVE_TAC []
METIS_TAC [composeMuRe_def,composeRel_def] 
Cases_on `x = x`
          Q.SPECL [`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]
Q.EXISTS_TAC `t'` 
PAT_X_ASSUM ``!t' Conf Conf'. A`` (ASSUME_TAC o (Q.SPECL [`t'`,`Conf`,`Conf'`]))>>
PAT_X_ASSUM ``!Conf Conf' e ev. A`` (ASSUME_TAC o (Q.SPECL [`Conf`,`Conf'`,`e`,`ev`]))>>
          !Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys).
                 ((MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2'))
) ==> (( ((MTrn1,Ded1) || (MTrn2,Ded2))) = ( ((MTrn2,Ded2) || (MTrn1,Ded1))))
IN_DEF
Induct_on `e`
  REWRITE_TAC [composeMultiOperation_def]>>
REWRITE_TAC [comptraces_def]>>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
REPEAT STRIP_TAC >>
       REPEAT EQ_TAC >>
       REPEAT STRIP_TAC >>



!Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTS1) ⊆ (traces MTS2)) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1')  ∧
                 (MTrn2 Conf2 t2 Conf2') ∧
                 (MTrn Conf t Conf') 
) ==> ((comptraces (MTS1 || MTS)) ⊆ (comptraces (MTS2 || MTS)))


  !MTrn MTrn1 MTrn2 Ded Ded1 Ded2 (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 ((MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded))
)==> (MTS1 ⊑ MTS2) ==> ((MTS1 || MTS) ⊑ (MTS2 || MTS)) 

(∀x. A(x)) ==> B 

  !MTrn MTrn1 Ded Ded1 (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 ((MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn1,Ded1)) ∧ (MTS = (MTrn,Ded)) ∧ (MTS1 ⊑ MTS2)
)==> ((MTS1 || MTS) ⊑ (MTS2 || MTS))


!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' t1 t2 t (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2: ('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 (((tracesone MTrn1 Conf1 t1 Conf1') ⊆ (tracesone MTrn1 Conf2 t2 Conf2')) ∧
                (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((tracestwo (composeMultiOperation MTrn1 Conf1 t1 Conf1' MTrn2 Conf t Conf')) ⊆ (tracestwo (MTrn1 Conf2 t2 Conf2' MTrn2 Conf t Conf')))

  
!Sym1 Sym1' Sym2 Sym2' Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' t1 t2 t (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2: ('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 (((MTrn1 Conf1 t1 Conf1') = (MTrn1 Conf2 t2 Conf2')) ∧
                (Conf1 = (Sym1,P1,S1)) ∧ (Conf1' = (Sym1',P1',S1')) ∧
                (Conf2 = (Sym2,P2,S2)) ∧ (Conf2' = (Sym2',P2',S2')) ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((composeMultiOperation MTrn1 Conf1 t1 Conf1' MTrn2 Conf t Conf') = (composeMultiOperation MTrn1 Conf2 t2 Conf2' MTrn2 Conf t Conf'))
              
*)
