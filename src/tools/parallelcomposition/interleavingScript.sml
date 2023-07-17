open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open listTheory;
open parallelcompositionsimpleTheory;
open pairTheory wordsTheory set_sepTheory;
open quantHeuristicsTheory;
open propertyTheory;
val _ = new_theory "interleaving";

val TranRelNil = new_axiom ("TranRelNil",
                            ``∀(MTrn:('event, 'pred, 'state , 'symb ) mtrel) v p s. MTrn (v,p,s) [] (v,p,s)``);
val TranRelSnoc = new_axiom ("TranRelSnoc",
                            ``∀(MTrn:('event, 'pred, 'state , 'symb ) mtrel) v p s v' p' s' v'' p'' s'' t e. ((MTrn (v,p,s) t (v',p',s')) ∧ (MTrn (v',p',s') [e] (v'',p'',s''))) ⇒ (MTrn (v,p,s) (e::t) (v'',p'',s''))``);    
(*
Inductive MTrn1:
[~nil:]
  (MTrn1 ((v:'symb),(p:'pred1),(s:'state1)) ([]:('event1+'eventS) list) (v,p,s)) /\
[~snoc:]
  ((( MTrn1 (v,p,s) t (v',p',s')) /\ ( MTrn1 (v',p',s') [e] (v'',p'',s''))) ==> ( MTrn1 (v,p,s) (e::t) (v'',p'',s'')))
End

Inductive MTrn2:
[~nil:]
  (MTrn2 ((v:'symb),(p:'pred2),(s:'state2)) ([]:('event2+'eventS) list) (v,p,s)) /\
[~snoc:]
  ((( MTrn2 (v,p,s) t (v',p',s')) /\ ( MTrn2 (v',p',s') [e] (v'',p'',s''))) ==> ( MTrn2 (v,p,s) (e::t) (v'',p'',s'')))
End        
    
Inductive comptrace:
[~nil:]
  (comptrace (MTrn:( (('event1+'evenS)+('event2+'eventS)), ('pred1+'pred2), 'state1#'state2 , 'symb ) mtrel) (v,p,s1,s2) [] (v,p,s1,s2)) /\
[~snoc:]
  (((comptrace MTrn (v,p,s1,s2) t (v',p',s1',s2')) /\ (comptrace MTrn (v',p',s1',s2') [e] (v'',p'',s1'',s2''))) ==> (comptrace MTrn (v,p,s1,s2) (e::t) (v'',p'',s1'',s2'')))
End
*)
                    
(* Binary interleaving of traces *)
Inductive binterl:
[~nil:]
  (binterl [] [] []) /\
[~left:]
  (((binterl (t1:('event1 + 'eventS) list) (t2:('event2 + 'eventS) list) t) /\ (t1' = ((INL e1)::t1)) /\ (t' = ((INL (INL e1))::t))) ==> (binterl t1' t2 t')) /\
[~right:]                                                                        
  (((binterl (t1:('event1 + 'eventS) list) (t2:('event2 + 'eventS) list) t) /\ (t2' = ((INL e2)::t2)) /\ (t' = ((INR (INL e2))::t))) ==> (binterl t1 t2' t')) /\
[~sync:]                                                                        
  (((binterl (t1:('event1 + 'eventS) list) (t2:('event2 + 'eventS) list) t) /\ (t1' = ((INR e)::t1)) /\ (t2' = ((INR e)::t2)) /\ (t' = ((INR (INR e))::t))) ==> (binterl t1' t2' t'))
End

(*
Definition binterl:
  binterl t1 t2 t =
                   (case t of
                      [] => ((t1 = []) ∧ (t2 = []))
                    | ((INL e1)::ev) => ((HD t1 = e1) ∧ (binterl (TL t1) t2 ev))
                    | ((INR e2)::ev) => ((HD t2 = e2) ∧ (binterl t1 (TL t2) ev))
                   )
   
End
*)   

Definition binterleave_ts:
  binterleave_ts ts1 ts2 = {t| ∃t1 t2. (t1 ∈ ts1) ∧ (t2 ∈ ts2) ∧ (binterl t1 t2 t)}
End

val binterleave_trace_decomp_thm = store_thm(
  "binterleave_trace_decomp", ``
∀t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) Ded1 Ded2. 
((FST ((MTrn1,Ded1) || (MTrn2,Ded2))) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
⇒
  (∃t1 t2. (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (binterl t1 t2 t))
  ``,
  GEN_TAC >> rewrite_tac[composeMultiOperation_def] >>
                                                    Induct_on `t` >- (
                              rpt strip_tac >> FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def] >> Q.EXISTS_TAC `[]` >> Q.EXISTS_TAC `[]` >> rw[binterl_nil]) >>
                                                                     gen_tac >> Cases_on `h` >| [
      Cases_on `x` >|
      [
        FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def] >> rpt strip_tac >> PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'`,`MTrn1`,`MTrn2`])) >> RES_TAC >> Q.EXISTS_TAC `(INL x')::t1` >> Q.EXISTS_TAC `t2` >> rw[binterl_left]  >- (
        metis_tac[TranRelSnoc]
                ) >> cheat] >> cheat ] >>  cheat);

val binterleave_composition_thm = store_thm(
  "binterleave_composition_thm",
  ``∀Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
         (binterleave_ts (traces (MTrn1,Ded1)) (traces (MTrn2,Ded2))) = (comptraces ((MTrn1,Ded1) || (MTrn2,Ded2)))      
``,
REPEAT GEN_TAC>> rewrite_tac[binterleave_ts,composeMultiOperation_def,comptraces_def,traces_def]>>                           FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [EXTENSION]  >>       gen_tac >> eq_tac >> cheat
                                          
  );
(*
val binterleave_composition_one_thm = store_thm(
  "binterleave_composition_one_thm",
  ``∀Ded1 Ded2 t1 t2 t Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
          ((trace MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (trace MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (comptrace (FST ((MTrn1,Ded1) || (MTrn2,Ded2))) (Sym,P,S1,S2) t (Sym',P',S1',S2'))) ⇔ binterl t1 t2 t``,
                                                                                                                          REPEAT GEN_TAC>> EQ_TAC
     rewrite_tac[composeMultiOperation_def]>> cheat
                                          
  );  
  

∀Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
                 (binterleave_ts (traces (MTrn1,Ded1)) (traces (MTrn2,Ded2))) = (comptraces ((MTrn1,Ded1) || (MTrn2,Ded2)))
REPEAT GEN_TAC>>
rewrite_tac[binterleave_ts]
rewrite_tac[composeMultiOperation_def]
rewrite_tac[comptraces_def]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [EXTENSION]
gen_tac
rewrite_tac[traces_def]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [IN_DEF]
eq_tac
Q.EXISTS_TAC `Sym''''` >> Q.EXISTS_TAC `P''''` >> Q.EXISTS_TAC `S'` >> Q.EXISTS_TAC `S'''` >> 
Q.EXISTS_TAC `Sym'''''` >> Q.EXISTS_TAC `P'''''` >> Q.EXISTS_TAC `S''` >> Q.EXISTS_TAC `S''''` >>
Induct_on `x`

asm_rewrite_tac[composeMuRe_def]

METIS_TAC[binterl_rules]
rewrite_tac[binterl]
        
                
∀t Sym P S1 S2 Sym' P' S1' S2' Ded1 Ded2. 
((FST ((MTrn1,Ded1) || (MTrn2,Ded2))) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
⇔
    (∃t1 t2. (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (binterl t1 t2 t))

CCONTR_TAC
REPEAT GEN_TAC>>
    EQ_TAC>>
    rewrite_tac[composeMultiOperation_def]>>
    rpt strip_tac>>
     Q.EXISTS_TAC `t1` >> Q.EXISTS_TAC `t2`
     Induct_on `t`
    Induct_on `t1`
    Induct_on `t2`
rewrite_tac[binterl_nil]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_nil]
rw[]
asm_rewrite_tac[]
asm_rewrite_tac[]
Cases_on `t2 = []`
METIS_TAC[MTrn1_cases,MTrn1_rules,MTrn1_ind,MTrn1_nil,MTrn1_snoc]
asm_rewrite_tac[MTrn1_cases,MTrn1_rules,MTrn1_ind,MTrn1_nil,MTrn1_snoc]
        gen_tac
strip_tac
Cases_on `h`
Cases_on `x`
Cases_on `t1 = []`
Q.EXISTS_TAC `[]` >> Q.EXISTS_TAC `[]`
        Q.ID_SPEC_TAC `b`
MP_TAC (Q.SPECL [`n1`, `NONE`, `(T, \_. T)`, `p`, `state0`] 
     Induct_on `t`
    Induct_on `t1`
    Induct_on `t2`
    rewrite_tac[binterl_left]
    
        RES_TAC
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [BOTH_EXISTS_AND_THM]
    METIS_TAC[composeMuRe_nil]
rpt strip_tac
rw[]
MP_TAC (Q.SPECL [`t1`] binterl_rules)
rename1 `[]`
Q.EXISTS_TAC `[INL x']` >> Q.EXISTS_TAC `t2`
PAT_X_ASSUM ``∀t1 t2. A`` (ASSUME_TAC o (Q.SPECL [`[]`,`[]`]))
        REPEAT GEN_TAC>>
    EQ_TAC>>
    rewrite_tac[composeMultiOperation_def]>>
    rpt strip_tac>>
    Induct_on `t`>>
    strip_tac
     Q.EXISTS_TAC `[]` >> Q.EXISTS_TAC `[]`
rewrite_tac[bin]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [MTrn1_nil]
rw[]
  PAT_X_ASSUM ``∃t1 t2.B`` (IMP_RES_TAC)
 PAT_X_ASSUM ``A = BType_Imm Bit1`` (ASSUME_TAC)
  IMP_RES_TAC AND_INTRO_THM
  FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [IMAGE_DEF,MAP,OUTR,OUTL,INL,INR]
  rewrite_tac[AND_INTRO_THM]
   FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []

   REPEAT GEN_TAC>> EQ_TAC>> rewrite_tac[composeMultiOperation_def]>> rpt strip_tac>>
                              Induct_on `t` >>  FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def] >> strip_tac >> Q.EXISTS_TAC `[]` >> Q.EXISTS_TAC `[]` >>
                              rw[binterl_nil] >> gen_tac >>  Cases_on `h` >> Cases_on `x` >>   FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def] >> rpt strip_tac
                                                                                                             PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2' MTrn1 MTrn2. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'''`,`P'''`,`S1'''`,`S2'`,`MTrn1`,`MTrn2`]))>>
                              FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [TranRelSnoc]
                                            RES_TAC
                                            Q.EXISTS_TAC `(INL x')::t1` >> Q.EXISTS_TAC `t2`
                                                                            rw[binterl_left]
                                                                            asm_rewrite_tac[]
                                                                                rw[TranRelSnoc]
                                                                                 metis_tac[TranRelSnoc]
*)


val _ = export_theory();

