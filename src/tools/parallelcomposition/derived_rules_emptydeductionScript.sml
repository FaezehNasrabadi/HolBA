open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavingemptyTheory;
open parallelcompositionemptydeductionTheory;
val _ = new_theory "derived_rules_emptydeduction";

val traces_def =
Define`
      traces ((MTrn:('event, 'pred, 'state, 'symb) mtrel),(ded:('pred) tded)) ((Sym:'symb set),(P: 'pred set),(S: 'state)) ((Sym':'symb set),(P': 'pred set),(S': 'state)) = {t| (MTrn (Sym,P,S) t (Sym',P',S'))}
                                                                                                                                                                        `;
 val comptraces_def =
Define`
      comptraces ((CMTrn:((('event1+'eventS) + ('event2 +'eventS)), ('pred1 + 'pred2), 'state1#'state2, 'symb) mtrel),(CDed:('pred1 + 'pred2)tded)) ((Sym:'symb set),(P: ('pred1 + 'pred2) set),(S1: 'state1),(S2: 'state2)) ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) = {t| (CMTrn (Sym,P,S1,S2) t (Sym',P',S1',S2'))}
`;

val binterleave_trace_comp_to_decomp_emptydeduction_thm = store_thm(
  "binterleave_trace_comp_to_decomp_emptydeduction",
  ``∀t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) (ded1:('pred1) tded) (ded2:('pred2) tded).
       (((MTrn1,ded1) || (MTrn2,ded2)) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
     ⇒
     (∃t1 t2.
        (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧
        (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧
        (binterl t1 t2 t))``,
                          GEN_TAC >>
     Induct_on `t` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def]>>
      rpt strip_tac >> Q.EXISTS_TAC `[]` >> Q.EXISTS_TAC `[]` >> metis_tac[binterl_nil]) >>
     gen_tac >> Cases_on `h` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss)[symbolicParlComp_def] >> rpt strip_tac >>
      PAT_X_ASSUM ``!phi. A`` (ASSUME_TAC o (Q.SPECL [`phi`])) >>
      RES_TAC >> Q.EXISTS_TAC `t1` >> Q.EXISTS_TAC `t2` >> metis_tac[binterl_none]) >>             
     Cases_on `x` >-(
      Cases_on `x'` >-(
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >> rpt strip_tac >> PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2 ded1 ded2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'`,`MTrn1`,`MTrn2`,`ded1`,`ded2`])) >> RES_TAC >> Q.EXISTS_TAC `(SOME (INL x))::t1` >> Q.EXISTS_TAC `t2` >> metis_tac[TranRelNil,TranRelSnoc,TranRelConfigEq,binterl_left]
        ) >>
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >> rpt strip_tac >> PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'''`,`MTrn1`,`MTrn2`])) >> RES_TAC >> Q.EXISTS_TAC `(SOME (INR y))::t1` >> Q.EXISTS_TAC `(SOME (INR y))::t2` >> rw[binterl_syncL] >- (metis_tac[TranRelSnoc])  >> metis_tac[TranRelSnoc]
      ) >> Cases_on `y` >- (
      FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >> rpt strip_tac >> PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'`,`S2'''`,`MTrn1`,`MTrn2`])) >> RES_TAC >> Q.EXISTS_TAC `t1` >> Q.EXISTS_TAC `(SOME (INL x))::t2` >> metis_tac[binterl_right,TranRelNil,TranRelSnoc,TranRelConfigEq])
     >> FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [symbolicParlComp_def] >> rpt strip_tac >> PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'''`,`MTrn1`,`MTrn2`])) >> RES_TAC >> Q.EXISTS_TAC `(SOME (INR y'))::t1` >> Q.EXISTS_TAC `(SOME (INR y'))::t2` >> metis_tac[binterl_syncR,TranRelSnoc]
  );





















val _ = export_theory();
