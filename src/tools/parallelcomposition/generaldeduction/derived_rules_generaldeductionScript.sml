open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavinggeneraldeductionTheory;
open parallelcompositiongeneraldeductionTheory;

val _ = new_theory "derived_rules_generaldeduction";

val traces_def =
Define`
      traces ((MTrn:('event, 'pred, 'state, 'symb) mtrel),(ded:('pred) tded)) ((Sym:'symb set),(P: 'pred set),(S: 'state)) ((Sym':'symb set),(P': 'pred set),(S': 'state)) = {t| (MTrn (Sym,P,S) t (Sym',P',S'))}
                                                                                                                                                                             `;
val comptraces_def =
Define`
      comptraces ((MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel),(Ded1:('pred1) tded)) ((MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel),(Ded2:('pred2) tded)) (ded3:('pred1 + 'pred2) tded) ((Sym:'symb set),(P: ('pred1 + 'pred2) set),(S1: 'state1),(S2: 'state2)) ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) =
{(t: ((('event1 + 'eventS) + 'event2 + 'eventS) option list))|  
 (symbolicParlComp (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
}
`;

val binterleave_trace_comp_to_decomp_generaldeduction_thm = store_thm(
  "binterleave_trace_comp_to_decomp_generaldeduction",
  ``∀t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded).
       (TransEnable ded3 (MTrn1,ded1) (MTrn2,ded2)) ⇒
       ((symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2'))
     ⇒
     (∃t1 t2.
        (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧
        (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧
        (binterl t1 t2 t)))``,
                          GEN_TAC >>
     Induct_on `t` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def]>>     
      rpt strip_tac >>
      Q.EXISTS_TAC `[]` >>
      Q.EXISTS_TAC `[]` >>
      metis_tac[binterl_nil]) >>
     gen_tac >>
     Cases_on `h` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >>
      rpt strip_tac >>
      PAT_X_ASSUM ``!phi. A`` (ASSUME_TAC o (Q.SPECL [`phi`])) >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P''`,`S1'`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`]))>>
      RES_TAC >>
      Q.EXISTS_TAC `t1` >>
      Q.EXISTS_TAC `t2` >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[]>>
      metis_tac[TransEnable_def,binterl_combinenone] 
      )   >>
     Cases_on `x` >-(
      Cases_on `x'` >-(
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
        rpt strip_tac >>
        PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
        RES_TAC >>
        Q.EXISTS_TAC `(SOME (INL x))::t1` >>
        Q.EXISTS_TAC `t2` >>
        metis_tac[TranRelNil,TranRelSnoc,TranRelConfigEq,binterl_left]
        ) >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
      rpt strip_tac >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'''`,`MTrn1`,`MTrn2`])) >>
      RES_TAC >>
      Q.EXISTS_TAC `(SOME (INR y))::t1` >>
      Q.EXISTS_TAC `(SOME (INR y))::t2` >>
      rw[binterl_syncL] >- (metis_tac[TranRelSnoc])  >>
      metis_tac[TranRelSnoc]
      ) >>
     Cases_on `y` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
      rpt strip_tac >>
      PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'`,`S2'''`,`MTrn1`,`MTrn2`])) >>
      RES_TAC >>
      Q.EXISTS_TAC `t1` >>
      Q.EXISTS_TAC `(SOME (INL x))::t2` >>
      metis_tac[binterl_right,TranRelNil,TranRelSnoc,TranRelConfigEq])>>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
     rpt strip_tac >>
     PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'''`,`MTrn1`,`MTrn2`])) >>
     RES_TAC >>
     Q.EXISTS_TAC `(SOME (INR y'))::t1` >>
     Q.EXISTS_TAC `(SOME (INR y'))::t2` >>
     metis_tac[binterl_syncR,TranRelSnoc]
  );


val binterleave_composition_generaldeduction_subseteq_thm = store_thm(
  "binterleave_composition_generaldeduction_subseteq",
  ``∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded).
         (TransEnable ded3 (MTrn1,Ded1) (MTrn2,Ded2)) ⇒
         ((comptraces (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) (Sym',P',S1',S2'))                           
      ⊆ (binterleave_ts (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2'))))
       ``,
       rpt gen_tac >>      
     rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[binterleave_trace_comp_to_decomp_generaldeduction_thm]   
  );

  
val binterleave_trace_decomp_to_comp_generaldeduction_thm = store_thm(
  "binterleave_trace_decomp_to_comp_generaldeduction",
  ``∀t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded). 
       TransDisable ded3 (MTrn1,ded1) (MTrn2,ded2) ⇒
       ((∃t1 t2. (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (binterl t1 t2 t))
     ⇒
     (symbolicParlComp (MTrn1,ded1) (MTrn2,ded2) ded3 (Sym,P,S1,S2) t (Sym',P',S1',S2')))
     ``,
     GEN_TAC >>
     Induct_on `t` >-
      (rpt strip_tac >>
       IMP_RES_TAC binterl_Empty >>
       rw[]>>
       FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
       metis_tac[TranRelConfigEq,IMAGEOUT]) >>
     gen_tac >>
     reverse(Cases_on `h`) >-
      (Cases_on `x` >- (
        Cases_on `x'` >- 
         (FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
          rpt strip_tac >>
          IMP_RES_TAC binterl_moveAL >>
          rw[] >>
          IMP_RES_TAC TranRelSnocRevAsyncL >>
          Q.EXISTS_TAC `Sym''` >>
          Q.EXISTS_TAC `P''` >>
          Q.EXISTS_TAC `S1''` >>
          rw[]
          >- (metis_tac[TranRelConfigEq,IMAGEOUT]) >>
          PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1''`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
          IMP_RES_TAC binterl_movesL >>
          RES_TAC) >>
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
        rpt strip_tac >>
        IMP_RES_TAC binterl_moveSL >>
        rw[] >>
        IMP_RES_TAC TranRelSnocRevSync >>
        Q.EXISTS_TAC `Sym''`
        >>
        Q.EXISTS_TAC `P''` >>
        Q.EXISTS_TAC `S1''` >>
        Q.EXISTS_TAC `S2''` >>
        rw[] >>
        PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1''`,`S2''`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
        IMP_RES_TAC binterl_movesSL >>
        RES_TAC)
       >>
       Cases_on `y` >- (
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
        rpt strip_tac >>
        IMP_RES_TAC binterl_moveAR >>
        rw[] >>
        IMP_RES_TAC TranRelSnocRevAsyncR >>
        Q.EXISTS_TAC `Sym''`
        >>
        Q.EXISTS_TAC `P''` >>
        Q.EXISTS_TAC `S2''` >>
        rw[]
        >- ( metis_tac[TranRelConfigEq,IMAGEOUT]) >>
        PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1'`,`S2''`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
        IMP_RES_TAC binterl_movesR >>
        RES_TAC) >>
       FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
       rpt strip_tac >>
       IMP_RES_TAC binterl_moveSR >>
       rw[] >>
       IMP_RES_TAC TranRelSnocRevSync >>
       Q.EXISTS_TAC `Sym''` >>
       Q.EXISTS_TAC `P''` >>
       Q.EXISTS_TAC `S1''` >>
       Q.EXISTS_TAC `S2''` >>
       rw[] >>
       PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym''`,`P''`,`S1''`,`S2''`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
       IMP_RES_TAC binterl_movesSR >>
       RES_TAC) >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >>
     rpt strip_tac >>
     IMP_RES_TAC TranRelSnocRevNone>>
     IMP_RES_TAC binterl_movecombinenone >>
     PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2 ded3. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P''`,`S1'`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`,`ded3`])) >>
     RES_TAC >>
     Q.EXISTS_TAC `P''` >>
     PAT_X_ASSUM ``!Ded1 Ded2 Ded3. A`` (ASSUME_TAC o (Q.SPECL [`ded1`,`ded2`,`ded3`]))  >>
     PAT_X_ASSUM ``!Ded1 Ded2 Ded3. A`` (ASSUME_TAC o (Q.SPECL [`ded1`,`ded2`,`ded3`]))  >>
     rw[TransDisable_def] 
  );


val binterleave_composition_generaldeduction_supseteq_thm = store_thm(
  "binterleave_composition_generaldeduction_supseteq",
  ``∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded2:('pred2) tded) (ded3:('pred1 + 'pred2) tded).
         TransDisable ded3 (MTrn1,Ded1) (MTrn2,Ded2) ⇒
         ((binterleave_ts (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2'))) ⊆
         (comptraces (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) (Sym',P',S1',S2')))
       ``,
         rpt gen_tac >>      
     rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[binterleave_trace_decomp_to_comp_generaldeduction_thm]     
  );
  
 

val compose_vs_modules_generaldeduction_enable_disable_thm = store_thm(
  "compose_vs_modules_generaldeduction_enable_disable_thm",
  ``!Sym Sym' Sym'' Sym''' P P' P'' P''' S1 S1' S1'' S1''' S2 S2' S2'' S2''' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn1':('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (MTrn2':('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (Ded1:('pred1) tded) (Ded1':('pred1) tded) (Ded2:('pred2) tded) (Ded2':('pred2) tded) (ded3:('pred1 + 'pred2) tded).
     (((traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) ⊆ (traces (MTrn1',Ded1') (Sym'',(IMAGE OUTL P''),S1'') (Sym''',(IMAGE OUTL P'''),S1'''))) ∧
      ((traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2')) ⊆ (traces (MTrn2',Ded2') (Sym'',(IMAGE OUTR P''),S2'') (Sym''',(IMAGE OUTR P'''),S2'''))) ∧
      (TransEnable ded3 (MTrn1,Ded1) (MTrn2,Ded2)) ∧
      (TransDisable ded3 (MTrn1',Ded1') (MTrn2',Ded2'))
 ) ==> ((comptraces (MTrn1,Ded1) (MTrn2,Ded2) ded3 (Sym,P,S1,S2) (Sym',P',S1',S2')) ⊆ (comptraces (MTrn1',Ded1') (MTrn2',Ded2') ded3 (Sym'',P'',S1'',S2'') (Sym''',P''',S1''',S2'''))) ``
  ,
rpt gen_tac >>      
rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
rw[] >>
IMP_RES_TAC binterleave_trace_comp_to_decomp_generaldeduction_thm >>
PAT_X_ASSUM ``!t2. A`` (ASSUME_TAC o (Q.SPECL [`t2`])) >>
PAT_X_ASSUM ``!t1. A`` (ASSUME_TAC o (Q.SPECL [`t1`])) >>
RES_TAC >>
metis_tac[binterleave_trace_decomp_to_comp_generaldeduction_thm]
  );  



val _ = export_theory();
