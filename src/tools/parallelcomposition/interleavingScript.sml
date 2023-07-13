open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open listTheory;
open parallelcompositionsimpleTheory;
open pairTheory wordsTheory set_sepTheory;
open quantHeuristicsTheory;
open propertyTheory;
val _ = new_theory "interleaving";
    
(* Trace *)
val _ = Parse.type_abbrev("trc", ``:'event list``);  

(* Binary interleaving of traces *)
Inductive binterl:
[~nil:]
  (binterl [] [] []) /\
[~left:]
  (((binterl t1 t2 t) /\ (t1' = (e1::t1)) /\ (t' = ((INL e1)::t))) ==> (binterl t1' t2 t')) /\
[~right:]                                                                        
  (((binterl t1 t2 t) /\ (t2' = (e2::t2)) /\ (t' = ((INR e2)::t))) ==> (binterl t1 t2' t'))
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
∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) CMTrn CDed Ded1 Ded2 t. 
((FST ((MTrn1,Ded1) || (MTrn2,Ded2))) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
  ⇔
    (∃t1 t2. (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (binterl t1 t2 t))``,
REPEAT GEN_TAC>> EQ_TAC>> rewrite_tac[composeMultiOperation_def]>> rpt strip_tac>>
cheat);

val binterleave_composition_thm = store_thm(
  "binterleave_composition_thm",
  ``∀Ded1 Ded2 (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel).
               (binterleave_ts (traces (MTrn1,Ded1)) (traces (MTrn2,Ded2))) = (comptraces ((MTrn1,Ded1) || (MTrn2,Ded2)))
``,
REPEAT GEN_TAC>> rewrite_tac[binterleave_ts,composeMultiOperation_def,comptraces_def,traces_def]>>                           FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [EXTENSION]  >>       gen_tac >> eq_tac >> cheat
                                          
  );  
(*
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
rewrite_tac[binterl_rules]
        
                
∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, 'pred1, 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, 'pred2, 'state2, 'symb) mtrel) CMTrn CDed Ded1 Ded2 t. 
((FST ((MTrn1,Ded1) || (MTrn2,Ded2))) (Sym,P,S1,S2) t (Sym',P',S1',S2'))
  ⇔
    (∃t1 t2. (MTrn1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1')) ∧ (MTrn2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2')) ∧ (binterl t1 t2 t))


REPEAT GEN_TAC>>
    EQ_TAC>>
    rewrite_tac[composeMultiOperation_def]>>
    rpt strip_tac>>
     Q.EXISTS_TAC `t1` >> Q.EXISTS_TAC `t2`
     Induct_on `t`
    Induct_on `t1`
    Induct_on `t2`
rewrite_tac[binterl_nil]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]
rw[]
asm_rewrite_tac[]
asm_rewrite_tac[]

        gen_tac
strip_tac
Cases_on `h`
Q.EXISTS_TAC `x::t1` >> Q.EXISTS_TAC `t2`
        
     Induct_on `t`
    Induct_on `t1`
    Induct_on `t2`
    rewrite_tac[binterl_left]
    
        RES_TAC
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]
    FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [BOTH_EXISTS_AND_THM]
    METIS_TAC[binterl_rules]
rpt strip_tac
rw[]




        REPEAT GEN_TAC>>
    EQ_TAC>>
    rewrite_tac[composeMultiOperation_def]>>
    rpt strip_tac>>
    Induct_on `t`>>
    strip_tac
     Q.EXISTS_TAC `[]` >> Q.EXISTS_TAC `[]`
rewrite_tac[binterl_nil]
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [composeMuRe_def]
rw[]
*)
    
val _ = export_theory();

