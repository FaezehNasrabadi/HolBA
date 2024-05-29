open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavinggeneraldeductionTheory;
open parallelcompositiongeneraldeductionTheory;
open derived_rules_generaldeductionTheory;

val _ = new_theory "derived_rules_DYlib";

(*DY library with same function signature *)

val _ = Datatype `term =
Name 'symb
| FAPP  (string # int) (term list)
        `;

val _ = Datatype `pred =
Equal ('symb term) ('symb term)
      `;

(* Sharing equalities *)        
val composeDedEquSame_def =
Define`
      (composeDedEquSame (P3:((('symb) pred) + (('symb) pred)) set) ((INL ((Equal x y):(('symb) pred))):((('symb) pred) + (('symb) pred))) = (((Equal x y):(('symb) pred)) ∈ (IMAGE OUTR P3))) ∧
(composeDedEquSame (P3:((('symb) pred) + (('symb) pred)) set) (INR ((Equal x y):(('symb) pred))) = (((Equal x y):(('symb) pred)) ∈ (IMAGE OUTL P3)))
`;

val same_function_signature_thm = store_thm(
  "same_function_signature_thm",
  ``!Sym Sym' P P' S1 S1' S2 S2' (MTrn1:(('event + 'eventS), ('symb pred), 'state, 'symb) mtrel) (Ded1:('symb pred) tded) (MTrn2:(('event + 'eventS), ('symb pred), 'state, 'symb) mtrel) (Ded2:('symb pred) tded).
     (comptraces (MTrn1,Ded1) (MTrn2,Ded2) composeDedEquSame (Sym,P,S1,S2) (Sym',P',S1',S2'))                           
  = (binterleave_ts (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2')))
    ``,
  rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
  rw[] >>
  rewrite_tac[binterleave_trace_generaldeduction]
  ); 



(*DY library with distinct function signature *)
     
(* DY Lib One *)     
val _ = Datatype `termOne =
NameOne 'symb
| FAPPOne  (string # int) (termOne list)
           `;

val _ = Datatype `predOne =
EqualOne ('symb termOne) ('symb termOne)
         `;

(* DY Lib Two *) 
val _ = Datatype `termTwo =
NameTwo 'symb
| FAPPTwo  (string # int) (termTwo list)
           `;

val _ = Datatype `predTwo =
EqualTwo ('symb termTwo) ('symb termTwo)
         `;

(* Sharing equalities *)
val composeDedEquDistinct_def =
Define`
      (composeDedEquDistinct (P3:((('symb) predOne) + (('symb) predTwo)) set) ((INL ((EqualOne (NameOne x) (NameOne y)):(('symb) predOne))):((('symb) predOne) + (('symb) predTwo))) = (((EqualTwo (NameTwo x) (NameTwo y)):(('symb) predTwo)) ∈ (IMAGE OUTR P3))) ∧
(composeDedEquDistinct (P3:((('symb) predOne) + (('symb) predTwo)) set) (INR ((EqualTwo (NameTwo x) (NameTwo y)):(('symb) predTwo))) = (((EqualOne (NameOne x) (NameOne y)):(('symb) predOne)) ∈ (IMAGE OUTL P3)))
`;



val distinct_function_signatures_thm = store_thm(
  "distinct_function_signatures_thm",
  ``∀Sym P S1 S2 Sym' P' S1' S2' (MTrn1:('event1 + 'eventS, ('symb predOne), 'state1, 'symb) mtrel) (MTrn2:('event2 + 'eventS, ('symb predTwo), 'state2, 'symb) mtrel) (Ded1:('symb predOne) tded) (Ded2:('symb predTwo) tded).
         (comptraces (MTrn1,Ded1) (MTrn2,Ded2) composeDedEquDistinct (Sym,P,S1,S2) (Sym',P',S1',S2'))                           
     = (binterleave_ts (traces (MTrn1,Ded1) (Sym,(IMAGE OUTL P),S1) (Sym',(IMAGE OUTL P'),S1')) (traces (MTrn2,Ded2) (Sym,(IMAGE OUTR P),S2) (Sym',(IMAGE OUTR P'),S2')))
       ``,
     rewrite_tac[binterleave_ts,traces_def,comptraces_def,EXTENSION] >>
     rw[] >>
     rewrite_tac[binterleave_trace_generaldeduction]   
  ); 




val _ = export_theory();
