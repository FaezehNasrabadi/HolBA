open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
(*
open interleavingemptyTheory;
open parallelcompositionemptydeductionTheory;
open derived_rules_emptydeductionTheory;
*)
open parallelcompositionsimpleTheory;     
val _ = new_theory "derived_rules_DYlib";


val _ = Datatype `names =
Name string 
     `;

val _ = Datatype `equalities =
Equal string string
      `;

val _ = Datatype `funcsymbols =
FAPP  (string # int) (string list)
      `;

(*
val same_function_signature_thm = store_thm(
  "same_function_signature_thm", ``
                           !Sym Sym' P P' S1 S1' S2 S2' (MTrn:(('event + 'eventS), 'pred, 'state, 'symb) mtrel) (Ded:('pred) tded).
                             (comptraces (MTrn,Ded) (MTrn,Ded) (Sym,P,S1,S2) (Sym',P',S1',S2'))                           
  = (binterleave_ts (traces (MTrn,Ded) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn,Ded) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2')))
``,
rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >> rw[] >> rewrite_tac[binterleave_trace_emptydeduction]
  ); 
  

val same_function_signature_thm = store_thm(
  "same_function_signature_thm", ``
                           !t Sym Sym' P P' S S' (MTrn:(('event + 'eventS), 'pred, 'state, 'symb) mtrel) (Ded:('pred) tded).
                             (((MTrn,ded) || (MTrn,ded)) (Sym,((IMAGE INL P)<+>(IMAGE INR P)),S,S) t (Sym',((IMAGE INL P')<+>(IMAGE INR P')),S',S')) = 
     (MTrn (Sym,P,S) t (Sym',P',S'))
``,
rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >> rw[] >> rewrite_tac[binterleave_trace_emptydeduction]
  ); 


val same_function_signature_thm = store_thm(
  "same_function_signature_thm", ``
                           !(MTrn:(('event + 'eventS), 'pred, 'state, 'symb) mtrel) (Ded:('pred) tded).
                             ((MTrn,Ded) || (MTrn,Ded)) = (MTrn,Ded)
``,
rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >> rw[] >> rewrite_tac[binterleave_trace_emptydeduction]
  ); 



*)









val _ = export_theory();
