open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open parallelcompositionsimpleTheory;
open propertyTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
val _ = new_theory "derived_rules";

 (*
val same_relation_compose_one_thm = store_thm(
  "same_relation_compose_one_thm", ``
 ∀Conf1 Conf1' Conf2 Conf2' Conf Conf' Ded Ded1 Ded2 t1 t2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 (((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn1 Conf2 t2 Conf2')) 
) ==> ((comptraces ((MTrn1,Ded1) || (MTrn,Ded))) ⊆ (comptraces ((MTrn1,Ded2) || (MTrn,Ded))))                                                      
      ``,
REWRITE_TAC [composeMultiOperation_def,comptraces_def,traces_def] >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
  );

val same_relation_compose_two_thm = store_thm(
  "same_relation_compose_two_thm", ``
 ∀Conf1 Conf1' Conf2 Conf2' Conf3 Conf3' Conf3 Conf4 Conf4' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) Ded4 Ded3 Ded1 Ded2 t1 t2 t3 t4.
                 (((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn1 Conf2 t2 Conf2')) ∧ ((traces MTrn2 Conf3 t3 Conf3') ⊆ (traces MTrn2 Conf4 t4 Conf4')) 
) ==> ((comptraces ((MTrn1,Ded1) || (MTrn2,Ded2))) ⊆ (comptraces ((MTrn1,Ded3) || (MTrn2,Ded4))))                                                      
      ``,
REWRITE_TAC [composeMultiOperation_def,comptraces_def,traces_def] >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
  );*)
(*
val trace_elimination_thm = store_thm(
  "trace_elimination_thm", ``
 ∀Sym1 P1 S1 Sym1' P1' S1' Sym2 P2 S2 Sym2' P2' S2' Ded1 Ded2 t1 t2 (MTrn1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (MTrn2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel).
                 ((traces MTrn1 (Sym1,P1,S1) t1 (Sym1',P1',S1')) ⊆ (IMAGE (MAP OUTL) (comptraces (FST ((MTrn1,Ded1) || (MTrn2,Ded2))) ((Sym1∪Sym2),(P1<+>P2),S1,S2) (combinelists t1 t2) ((Sym1'∪Sym2'),(P1'<+>P2'),S1',S2')))) ∧  ((traces MTrn2 (Sym2,P2,S2) t2 (Sym2',P2',S2')) ⊆ (IMAGE (MAP OUTR) (comptraces (FST ((MTrn1,Ded1) || (MTrn2,Ded2))) ((Sym1∪Sym2),(P1<+>P2),S1,S2) (combinelists t1 t2) ((Sym1'∪Sym2'),(P1'<+>P2'),S1',S2'))))
      ``,
      REWRITE_TAC [composeMultiOperation_def,comptraces_def,traces_def] >>
              ASM_REWRITE_TAC [SUBSET_DEF]>>
                           ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
REPEAT GEN_TAC >> rw[]
                                    
                                                                FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [combinelists_def]
                                                                              
                           IMP_RES_TAC AND_INTRO_THM
                                                                                                                                                             REWRITE_TAC[combinelists_def]>>rw[]
                                                                                                                                                                                                GEN_TAC
                                                                                                                                                                                                
                                            ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
                                            REPEAT GEN_TAC
                                            FULL_SIMP_TAC std_ss [combinelists_def]
                                            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
                                                          IMP_RES_TAC combinelists_def
                                                          rw[]
                                                                RES_TAC
                                            STRIP_TAC
                                            Induct_on `t1'`
                                            Induct_on `t2'`
                                            PAT_X_ASSUM ``∀t1 t2. A`` (ASSUME_TAC o (Q.SPECL [`t1`,`t2`]))
                                                              Induct_on `(combinelists t1 t2)` >>
                                                           Induct_on `t1` >> Induct_on `t2`
                                                                                         Cases_on `t1 = [] ∧ t2 = []`
  ); 

*)  
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
DB.find "IMAGE_def"
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
Q.EXISTS_TAC `rel1` >> Q.EXISTS_TAC `rel2` >>
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
RES_TAC
        PAT_X_ASSUM ``!t. t = e::ev`` (ASSUME_TAC o (Q.SPECL [`t`,`e`,`ev`]))
        FULL_SIMP_TAC std_ss [composeMuRe_def]
        FULL_SIMP_TAC std_ss [composeMuRe_config_thm]
        REWRITE_TAC [composeMuRe_def]
*)




        
val _ = export_theory();

(*
val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 ((MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) /\
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
IMP_RES_TAC(composeMuRe_def)
            DB.find_in "NOT" (DB.find "SUBSET");
        DB.find "SET_TO_LIST";
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t

rw[]
REWRITE_TAC [NOT_CONS_NIL]
(MATCH_MP_TAC ( tautLib.TAUT_PROVE ``if p then x = [] /\ Conf = Conf' else q``)) `case [] of [] => x = [] /\ Conf = Conf' | v2::v3 => x = [] /\ Conf ≠ Conf'
CONV_TAC (REDEPTH_CONV (RATOR_CONV (RAND_CONV (REWR_CONV `case [] of [] => x = [] /\ Conf = Conf' | v2::v3 => x = [] /\ Conf <> Conf'`)))) []

val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn2 Conf2 t2 Conf2')) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((comptraces (MTS1 || MTS)) ⊆ (comptraces (MTS2 || MTS))) ``
  ,
 
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [] >>
IMP_RES_TAC trace_twosystem_thm
RES_TAC
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
PAT_X_ASSUM ``!Sym'' P S1'' S2 Sym'³' P' S1'³' S2'. A`` (ASSUME_TAC o (Q.SPECL [`Sym''`,`P`,`S1''`,`S2`,`Sym'''`,`P'`,`S1'''`,`S2'`]))
Induct_on `h`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
rw[]
Induct_on `x'`
REWRITE_TAC[composeMuRe_empty_event_thm]
GEN_TAC
EQ_TAC
Induct_on `h`
REWRITE_TAC[composeMuRe_empty_event_thm]
IMP_RES_TAC composeMuRe_single_event_thm
REWRITE_TAC[composeMuRe_single_event_thm]
IMP_RES_TAC composeMuRe_multi_events_thm
REWRITE_TAC[composeMuRe_multi_events_thm]
IMP_RES_TAC composeMuRe_single_event_thm
            FULL_SIMP_TAC std_ss [composeMuRe_def]
            FULL_SIMP_TAC std_ss [composeRel_def]
            ASM_REWRITE_TAC[]
listTheory.MEM
`OUTL(h) ∈ LIST_TO_SET(t2)` by PROVE_TAC []
` MEM x t2` by PROVE_TAC []

ASM_CASES_TAC ``(h:('event1 + 'eventS) + 'event2 + 'eventS)``
cases_tac `h`
FULL_SIMP_TAC std_ss [traces_def]
FULL_SIMP_TAC std_ss [SUBSET_DEF]
IMP_RES_TAC traces_def
        Induct_on `t'`
Cases_on `OUTL(h) ∈ LIST_TO_SET(t1)`
Cases_on `h ∈ IMAGE INL (LIST_TO_SET(t1))`
Cases_on `(h = INR (INL E)) ∧ t = [INL E]`
METIS_TAC[]
ISR INR
RES_TAC
ARB_TAC
CONJUNCTS_TAC o SPEC_ALL
  Cases_on `OUTL(x') ∈ LIST_TO_SET(x)`
  Cases_on `(IMAGE OUTL (LIST_TO_SET(x'))) = LIST_TO_SET(x)`
  IMAGE OUTL      
Q.EXISTS_TAC `Sym` >> Q.EXISTS_TAC `P` >>
            Q.EXISTS_TAC `S1` >> Q.EXISTS_TAC `S2` >>
            Q.EXISTS_TAC `Sym'` >> Q.EXISTS_TAC `P'` >>
            Q.EXISTS_TAC `S1'` >> Q.EXISTS_TAC `S2'` >>
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `P'''` >>
            Q.EXISTS_TAC `S1'''`
           
      IMP_RES_TAC(composeMuRe_def)
      SRW_TAC[][]
      `OUTL(h) ∈ LIST_TO_SET(t2)` by PROVE_TAC []
METIS_TAC [composeMuRe_def,composeRel_def] 
Cases_on `x = x`
          Q.SPECL [`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]
Q.EXISTS_TAC `x'` 
PAT_X_ASSUM ``!t' Conf Conf'. A`` (ASSUME_TAC o (Q.SPECL [`t'`,`Conf`,`Conf'`]))>>
PAT_X_ASSUM ``!Conf Conf' e ev. A`` (ASSUME_TAC o (Q.SPECL [`Conf`,`Conf'`,`e`,`ev`]))>>
          !Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys).
                 ((MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2'))
) ==> (( ((MTrn1,Ded1) || (MTrn2,Ded2))) = ( ((MTrn2,Ded2) || (MTrn1,Ded1))))
IN_DEF
ASM_REWRITE_TAC[]
Q.EXISTS_TAC `rel1`
Q.EXISTS_TAC `rel2`
IMP_RES_TAC assume_ch_thm
Induct_on `e`
  REWRITE_TAC [composeMultiOperation_def]>>
REWRITE_TAC [comptraces_def]>>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
REPEAT STRIP_TAC >>
       REPEAT EQ_TAC >>
       REPEAT STRIP_TAC >>
IMP_RES_TAC AND_INTRO_THM
Cases_on `t1 = t2`

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
                 ((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn2 Conf2 t2 Conf2')) ∧
                (Conf1 = (Sym1,P1,S1)) ∧ (Conf1' = (Sym1',P1',S1')) ∧
                (Conf2 = (Sym2,P2,S2)) ∧ (Conf2' = (Sym2',P2',S2')) ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((composeMultiOperation MTrn1 Conf1 t1 Conf1' MTrn2 Conf t Conf') = (composeMultiOperation MTrn1 Conf2 t2 Conf2' MTrn2 Conf t Conf'))


  !Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn1 Conf2 t2 Conf2')) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn1,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn1 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((comptraces (MTS1 || MTS)) ⊆ (comptraces (MTS2 || MTS))) 


  !Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTrn1 Conf1 t1 Conf1') = (traces MTrn2 Conf2 t2 Conf2')) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((comptraces (composeMultiOperation MTrn1 (Sym,P1,S1) t1 (Sym',P1',S1') MTrn (Sym,P,S) t (Sym',P',S'))) = (comptraces (composeMultiOperation MTrn2 (Sym,P2,S2) t2 (Sym',P2',S2') MTrn (Sym,P,S) t (Sym',P',S'))))



!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn2 Conf2 t2 Conf2')) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf2 t2 Conf2') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> (comptraces
       ( MTrn1 MTrn (Sym ∪ Sym,P1 ⊔ P,S1,S)
          (SET_TO_LIST (set t1 ⊔ set t)) (Sym' ∪ Sym',P1' ⊔ P',S1',S')) ⊆
     comptraces
       ( MTrn2 MTrn (Sym ∪ Sym,P2 ⊔ P,S2,S)
          (SET_TO_LIST (set t2 ⊔ set t)) (Sym' ∪ Sym',P2' ⊔ P',S2',S')))

Cases_on `MTrn2 (Sym'', IMAGE OUTL P'', S1'') [INL E] (Sym'³', IMAGE OUTL P'''', S1'³') ∧ IMAGE OUTL P'³' ≠ IMAGE OUTL P'''' `
      
   !Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' MTrn MTrn1 MTrn2 Ded Ded1 Ded2 t1 t2 t (MTS1:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS2:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys) (MTS: ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys).
                 (((traces MTrn1 Conf1 t1 Conf1') ⊆ (traces MTrn2 Conf1 t2 Conf1')) ∧ (MTS1 = (MTrn1,Ded1)) ∧ (MTS2 = (MTrn2,Ded2)) ∧ (MTS = (MTrn,Ded)) ∧
                 (MTrn1 Conf1 t1 Conf1') ∧ (Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                 (MTrn2 Conf1 t2 Conf1') ∧ (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                 (MTrn Conf t Conf') ∧ (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
) ==> ((comptraces (MTS1 || MTS)) ⊆ (comptraces (MTS2 || MTS)))

    !Sym  Sym0  P0 P  S0  S  Sym1' Sym2' Sym' P1' P2' P' S1' S2' S' (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) t1 t2 t.
                 (((traces MTrn1 (Sym0,P0,S0) t1) ⊆ (traces MTrn2 (Sym0,P0,S0) t2)) ∧
                 (MTrn1 (Sym0,P0,S0) t1 = (Sym1',P1',S1')) ∧ (MTrn2 (Sym0,P0,S0) t2 = (Sym2',P2',S2')) ∧ (MTrn (Sym,P,S) t = (Sym',P',S'))
) ==> ((comptraces (composeMultiOperation MTrn1 (Sym0,P0,S0) t1 MTrn (Sym,P,S) t)) ⊆ (comptraces (composeMultiOperation MTrn2 (Sym0,P0,S0) t2 MTrn (Sym,P,S) t)))

FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [disjUNION_def,UNION_DEF]
REWRITE_TAC[disjUNION_def]
IMP_RES_TAC disjUNION_def
ASM_REWRITE_TAC[]
REWRITE_TAC[UNION_DEF]
REWRITE_TAC[MAP]
REWRITE_TAC[IMAGE_DEF]
IMP_RES_TAC IMAGE_DEF
REWRITE_TAC[MAP,OUTR,OUTL,INL,INR]
SRW_TAC [] [SET_TO_LIST_THM]
REWRITE_TAC [SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,IN_DIFF]

 REWRITE_TAC(Defn.eqns_of SET_TO_LIST_defn)
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
DB.find "MAP_DEF"
REPEAT GEN_TAC
STRIP_TAC
 Induct_on `t1`
 Induct_on `t`
 PAT_X_ASSUM ``!CMTrn Sym' P' S1' S2. A`` (ASSUME_TAC o (Q.SPECL [`CMTrn`,`Sym'`,`P'`,`S1'`,`S2`]))
rw[]
REWRITE_TAC[CONJ_ASSOC]
 REWRITE_TAC[SET_TO_LIST_SING]
REWRITE_TAC[INJ_INR]
REWRITE_TAC[LEFT_AND_OVER_OR]
REWRITE_TAC[LEFT_OR_OVER_AND]
REWRITE_TAC[LEFT_EXISTS_AND_THM]
REWRITE_TAC[RIGHT_OR_OVER_AND]
REWRITE_TAC[RIGHT_AND_OVER_OR]
REWRITE_TAC[BIGUNION]
REWRITE_TAC[combinelists_def]
IMP_RES_TAC combinelists_def
Cases_on `MTrn1 = MTrn2`
REWRITE_TAC [composeMultiOperation_def]>>
REWRITE_TAC [comptraces_def] >>
REWRITE_TAC [traces_def] >>
REPEAT GEN_TAC>>
Cases_on `x = MAP INL t1` >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
ASM_REWRITE_TAC [SUBSET_DEF]>>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>          
REPEAT STRIP_TAC>>
PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]))>>
PAT_X_ASSUM ``∀x. A`` (ASSUME_TAC o (Q.SPECL [`x`]))>>
PAT_X_ASSUM ``!Sym P S Sym' P' S'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S`,`Sym'`,`P'`,`S'`]))>>      
Induct_on `h`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [comptraces_def,combinelists_def,composeMuRe_def]
 FULL_SIMP_TAC std_ss [composeMuRe_def]
 REWRITE_TAC [FIRST_def,SECOND_def,THIRD_def]
 METIS_TAC[comptraces_def,combinelists_def,composeMuRe_def,FIRST_def,SECOND_def,THIRD_def]
 METIS_TAC[IMAGE_DEF,OUTR,OUTL,INL,INR]
 REWRITE_TAC [same_events_thm]
 IMP_RES_TAC same_events_thm
REWRITE_TAC [BOTH_EXISTS_AND_THM]
REWRITE_TAC [UNWIND_THM2,UNWIND_THM1]
 !Sym  Sym0  P0 P  S0  S  Sym1' Sym2' Sym' P1' P2' P' S1' S2' S' Sym1 P1 S1 Sym2 P2 S2 (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) t1 t2 t.
                 (((traces MTrn1 (Sym1,P1,S1) t1) ⊆ (traces MTrn2 (Sym2,P2,S2) t2)) ∧
                 (MTrn1 (Sym1,P1,S1) t1 = (Sym1',P1',S1')) ∧ (MTrn1 (Sym2,P2,S2) t2 = (Sym2',P2',S2')) ∧ (MTrn (Sym,P,S) t = (Sym',P',S'))
) ==> ((comptraces (composeMultiOperation MTrn1 (Sym1,P1,S1) t1 MTrn (Sym,P,S) t)) ⊆ (comptraces (composeMultiOperation MTrn1 (Sym2,P2,S2) t2 MTrn (Sym,P,S) t)))









 ∀Ded Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 ((traces (MTrn1,Ded1)) ⊆ (traces (MTrn2,Ded2))) 
 ==> ((comptraces ((MTrn1,Ded1) || (MTrn,Ded))) ⊆ (comptraces ((MTrn2,Ded2) || (MTrn,Ded))))             


REWRITE_TAC[SUBSET_DEF,composeMultiOperation_def,traces_def,comptraces_def,IN_DEF]>>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
REPEAT GEN_TAC>>
STRIP_TAC>>
GEN_TAC>>
Induct_on `ct`
REWRITE_TAC[composeMuRe_empty_event_thm]
REPEAT STRIP_TAC>>
PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]))>>
Cases_on `h`
Cases_on `x`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `S1'''` >> Q.EXISTS_TAC `P1` >> Q.EXISTS_TAC `P1'` >> Q.EXISTS_TAC `P2'`
PAT_X_ASSUM ``∀t. A`` (ASSUME_TAC o (Q.SPECL [`t`]))
ASM_REWRITE_TAC[]
Cases_on `x = [INL x'']`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []        
rw[]


IMP_RES_TAC AND_INTRO_THM
RES_TAC
REWRITE_TAC[AND_INTRO_THM]
REWRITE_TAC[disjUNION_def]
IMP_RES_TAC disjUNION_def
ASM_REWRITE_TAC[]
REWRITE_TAC[UNION_DEF]
REWRITE_TAC[MAP]
REWRITE_TAC[IMAGE_DEF]
IMP_RES_TAC IMAGE_DEF
REWRITE_TAC[IMAGE_DEF,MAP,OUTR,OUTL,INL,INR]
SRW_TAC [] [SET_TO_LIST_THM]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [IMAGE_DEF,MAP,OUTR,OUTL,INL,INR]

∀Ded Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 (∀t. (t ∈ (traces (MTrn1,Ded1))) ⇒ (t ∈ (traces (MTrn2,Ded2)))) 
 ==> (∀ct. (ct ∈ (comptraces ((MTrn1,Ded1) || (MTrn,Ded)))) ⇒ (ct ∈ (comptraces ((MTrn2,Ded2) || (MTrn,Ded)))))             
REWRITE_TAC[SUBSET_DEF,composeMultiOperation_def,traces_def,comptraces_def,IN_DEF]>>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
REPEAT GEN_TAC>>
STRIP_TAC>>
GEN_TAC>>
Induct_on `ct`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]>>
GEN_TAC>>
Cases_on `h`>>
Cases_on `x`>>
RES_TAC
rw[] >>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `S1'''` >> Q.EXISTS_TAC `P1` >> Q.EXISTS_TAC `P1'` >> Q.EXISTS_TAC `P2'`
ASM_REWRITE_TAC[]
Cases_on `t = [INL x']`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []        
rw[]              

Cases_on `P = P1 ⊔ P2`
Cases_on `P = P1 ⊔ P2`
Q.EXISTS_TAC `S2` >> Q.EXISTS_TAC `Sym'` >> Q.EXISTS_TAC `P'` >> Q.EXISTS_TAC `S1'` >> Q.EXISTS_TAC `S2'`>>
Q.EXISTS_TAC `Sym` >> Q.EXISTS_TAC `S1` >> Q.EXISTS_TAC `P1` >> Q.EXISTS_TAC `P2`

             PAT_X_ASSUM ``!Sym P S Sym' P' S'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S`,`Sym'`,`P'`,`S'`]))

CCONTR_TAC

        Q.EXISTS_TAC `S2` >> Q.EXISTS_TAC `Sym'` >> Q.EXISTS_TAC `P'` >> Q.EXISTS_TAC `S1'` >> Q.EXISTS_TAC `S2'`>>
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `S1'''` >> Q.EXISTS_TAC `P1'` >> Q.EXISTS_TAC `P2'`
RES_TAC
Q.EXISTS_TAC `S2` >> Q.EXISTS_TAC `Sym'` >> Q.EXISTS_TAC `P'` >> Q.EXISTS_TAC `S1'` >> Q.EXISTS_TAC `S2'`>>
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `S1'''` >> Q.EXISTS_TAC `P1'` >> Q.EXISTS_TAC `P2'`

Q.EXISTS_TAC `Sym` >> Q.EXISTS_TAC `P` >> Q.EXISTS_TAC `S1` >> Q.EXISTS_TAC `S2` >> 
Q.EXISTS_TAC `Sym'` >> Q.EXISTS_TAC `P'` >> Q.EXISTS_TAC `S1'` >> Q.EXISTS_TAC `S2'` >>
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `P'''` >> Q.EXISTS_TAC `S1'''` 
   ASM_REWRITE_TAC[]
   PAT_X_ASSUM ``∀Sym' Sym S2' S2 S1' S1 P' P. A`` (ASSUME_TAC o (Q.SPECL [`Sym'`,`Sym`,`S2'`,`S2`,`S1'`,`S1`,`P'`,`P`]))>>      Q.EXISTS_TAC `S2''` >> Q.EXISTS_TAC `Sym''''` >> Q.EXISTS_TAC `P'''` >> Q.EXISTS_TAC `S1''''` >> Q.EXISTS_TAC `S2'''`>>
Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `S1'''` >> Q.EXISTS_TAC `P1'` >> Q.EXISTS_TAC `P2'`



Q.EXISTS_TAC `Sym'''` >> Q.EXISTS_TAC `P'''` >> Q.EXISTS_TAC `S1'''`


∀Ded Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 (∀t. (t ∈ (traces (MTrn1,Ded1))) ∧ (t ∈ (traces (MTrn2,Ded2)))) 
 ==> (∀ct. (ct ∈ (comptraces ((MTrn1,Ded1) || (MTrn,Ded)))) ⇒ (ct ∈ (comptraces ((MTrn2,Ded2) || (MTrn,Ded)))))      


PAT_X_ASSUM ``∀Sym' Sym S'' S' P' P. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`Sym'`,`S''`,`S'`,`P'`,`P`]))>>




∀Ded Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 ((traces (MTrn1,Ded1)) ⊆ (traces (MTrn2,Ded2)))
 ==> ((comptraces ((MTrn1,Ded1) || (MTrn,Ded))) ⊆ (comptraces ((MTrn2,Ded2) || (MTrn,Ded)))) 


REPEAT GEN_TAC
REWRITE_TAC[SUBSET_DEF]
STRIP_TAC>>
GEN_TAC
Induct_on `x`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMultiOperation_def,traces_def,comptraces_def,composeMuRe_def]
PAT_X_ASSUM ``∀x. A`` (ASSUME_TAC o (Q.SPECL [`x'::ev`]))
GEN_TAC
Cases_on `h`>>
Cases_on `x'`>>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [comptraces_def]

FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [traces_def]

IMP_RES_TAC AND_INTRO_THM
RES_TAC
REWRITE_TAC[AND_INTRO_THM]
asm_rewrite_tac[]



PAT_X_ASSUM ``∀x Sym' Sym S'' S' P' P. A`` (ASSUME_TAC o (Q.SPECL [`x`,`Sym'`,`Sym`,`S''`,`S'`,`P`,`P'`]))>>   
PAT_X_ASSUM ``∀Sym' Sym S'' S' P' P. A`` (ASSUME_TAC o (Q.SPECL [`Sym'`,`Sym`,`S''`,`S'`,`P'`,`P`]))>> 

rw[]



∀Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) z zv.  ∃x xv y yv. ((z::zv) ∈(comptraces ((MTrn1,Ded1) || (MTrn2,Ded2)))) ∧ ((x::xv) ∈ (traces (MTrn1,Ded1))) ∧ ((y::yv)  ∈ (traces (MTrn2,Ded2)))
⇒ ((z = (INR y)) ∨ (z = (INL x)))

REPEAT GEN_TAC
Q.EXISTS_TAC `x` >> Q.EXISTS_TAC `xv` >> Q.EXISTS_TAC `y` >> Q.EXISTS_TAC `yv`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMultiOperation_def,traces_def,comptraces_def,composeMuRe_def]
REPEAT STRIP_TAC
Cases_on `z`
rw[]
Cases_on `x = x'::ev`
Induct_on `(x :('event1 + 'eventS) list)`
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMultiOperation_def,composeMuRe_def]

              Cases_on `x'`

rewrite_tac[comptraces_def]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [traces_def]
rewrite_tac[composeMuRe_def]
              
DB.find "INL"
INJ
  METIS_TAC[]
  rw[]  
*)
