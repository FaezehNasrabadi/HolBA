open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

val _ = new_theory "parallelcompositioncombinededuction";

    
(* transition relation *)
val _ = Parse.type_abbrev("trel", ``:(('symb set) # ('pred set) # 'state) -> ('event option) -> (('symb set) # ('pred set) # 'state) -> bool``);    

    
(* deduction relation *)    
val _ = Parse.type_abbrev("tded", ``:('pred set) -> 'pred -> bool``);

 (*   
(* equality pred1 *)    
val _ = Parse.type_abbrev("equalityOne", ``:'symb -> 'symb -> 'pred1``);


(* equality pred2 *)    
val _ = Parse.type_abbrev("equalityTwo", ``:'symb -> 'symb -> 'pred2``);


val _ = overload_on ("apply_equalityTwo", ``equalityTwo``);

(* knowledge pred2 *)    
val _ = Parse.type_abbrev("knowledge", ``:'symb -> 'pred2``);

(* constant pred1 *)    
val _ = Parse.type_abbrev("const", ``:'symb -> 'pred1``);

(* operation pred1 *)    
val _ = Parse.type_abbrev("operation", ``:'symb -> 'symb -> 'pred1``);


(* symbols of a symbol*)    
val _ = Parse.type_abbrev("symbols", ``:'symb -> ('symb set)``);
 *)
 
val _ = Datatype `pred2 =
K 'symb 
| EquTwo 'symb 'symb 
         `;

val _ = Datatype `pred1 =
Const string 
| Op 'symb string
| EquOne 'symb 'symb
| EquOp 'symb pred1
         `;
         
val symbols_def =
Define`
      symbols (x:'symb) = {x}
`;

val _ = Parse.type_abbrev("ctded", ``:('pred1) tded -> ('pred2) tded -> ('pred1 + 'pred2) tded``);

val composeDed_def =
Define`
      (composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INL (F1:'pred1)) = (ded1 (IMAGE OUTL P3) F1)) ∧
(composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INR (F2:'pred2)) = (ded2 (IMAGE OUTR P3) F2))
`;

val composeDedEqu_def =
Define`
      (composeDedEqu (P3:(('symb pred1) + ('symb pred2)) set) ((INL ((EquOne (x:'symb) (z:'symb)):('symb pred1))):('symb pred1) + ('symb pred2)) = (∃(y: 'symb). (((EquOne (x:'symb) (y:'symb)):('symb pred1)) ∈ (IMAGE OUTL (P3:(('symb pred1) + ('symb pred2)) set))) ∧ (((EquTwo (y:'symb) (z:'symb)):('symb pred2)) ∈ (IMAGE OUTR (P3:(('symb pred1) + ('symb pred2)) set))))) ∧
(composeDedEqu (P3:(('symb pred1) + ('symb pred2)) set) (INR ((EquTwo (x:'symb) (z:'symb)):('symb pred2))) = (∃(y: 'symb). (((EquOne (x:'symb) (y:'symb)):('symb pred1)) ∈ (IMAGE OUTL (P3:(('symb pred1) + ('symb pred2)) set))) ∧ (((EquTwo (y:'symb) (z:'symb)):('symb pred2)) ∈ (IMAGE OUTR (P3:(('symb pred1) + ('symb pred2)) set)))))
`;

val composeDedOverApprox_def =
Define`
      composeDedOverApprox (P3:(('symb pred1) + ('symb pred2)) set) ((INR ((K (z:'symb)):('symb pred2))):('symb pred1) + ('symb pred2)) = (∃(x:'symb) (y: 'symb). (((K (x:'symb)):('symb pred2)) ∈ (IMAGE OUTR (P3:(('symb pred1) + ('symb pred2)) set))) ∧ (((EquOne (x:'symb) (y:'symb)):('symb pred1)) ∈ (IMAGE OUTL (P3:(('symb pred1) + ('symb pred2)) set))) ∧ (z ∈ (symbols y)))
`;

val composeDedBit_def =
Define`
      composeDedBit (P3:(('symb pred1) + ('symb pred2)) set) ((INR ((K (y:'symb)):('symb pred2))):('symb pred1) + ('symb pred2)) = (∃(x:'symb) (c: string). (((K (x:'symb)):('symb pred2)) ∈ (IMAGE OUTR (P3:(('symb pred1) + ('symb pred2)) set))) ∧ (((EquOp (y:'symb) (Op x c)):('symb pred1)) ∈ (IMAGE OUTL (P3:(('symb pred1) + ('symb pred2)) set))) ∧ ((Const c) ∈ (IMAGE OUTL (P3:(('symb pred1) + ('symb pred2)) set))))
`;

        
(*        

Inductive composeDed:
[~left:]
  (((ded1:('pred1) tded) (IMAGE OUTL (P3:('pred1 + 'pred2) set)) (F1:'pred1)) ==> (composeDed ded1 (ded2:('pred2) tded) P3 (INL F1))) /\
[~right:]                                                                        
  (((ded2:('pred2) tded) (IMAGE OUTR (P3:('pred1 + 'pred2) set)) (F2:'pred2)) ==> (composeDed (ded1:('pred1) tded) ded2 P3 (INR F2))) /\
[~eqOne:]
  (((((equalityOne (x:'symb) (y:'symb)):'pred1) ∈ (IMAGE OUTL (P3:('pred1 + 'pred2) set))) ∧ (((equalityTwo (y:'symb) (z:'symb)):'pred2) ∈ (IMAGE OUTR (P3:('pred1 + 'pred2) set)))) ==> (composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) P3 (INL (equalityOne (x:'symb) (z:'symb)))))                 
End
(* compose deduction relation *)
Inductive composeDed:

[~eqOne:]
  (((((equalityOne (x:'symb) (y:'symb)):'pred1) ∈ (IMAGE OUTL (P3:('pred1 + 'pred2) set))) ∧ (((equalityTwo (y:'symb) (z:'symb)):'pred2) ∈ (IMAGE OUTR (P3:('pred1 + 'pred2) set)))) ==> (composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) P3 (INL (equalityOne (x:'symb) (z:'symb)))))                 
End
*)

        
(* compose deduction relation *)
val combineAllDed_def =
Define `
       (combineAllDed (P3:(('symb pred1) + ('symb pred2)) set) (F3:('symb pred1) + ('symb pred2)) = (
         (∃(ded1:('symb pred1) tded) (ded2:('symb pred2) tded). composeDed ded1 ded2 P3 F3) ∨
         (composeDedEqu P3 F3) ∨
         (composeDedOverApprox P3 F3) ∨
         (composeDedBit P3 F3)  
         ))`;
       
(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:(('symb set) # ('pred set) # 'state) -> (('event option) list) -> (('symb set) # ('pred set) # 'state) -> bool``);

(* multi transitions system *)    
val _ = Parse.type_abbrev("multransys", ``:(( 'symb, 'pred, 'state, 'event ) mtrel # ('pred) tded)``);


(* compose multi transition relation *)
val _ = Parse.type_abbrev("cmtrel", ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) mtrel ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) mtrel -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) mtrel``);
  


val symbolicParlComp_def =
Define  `
((symbolicParlComp ((Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
 (((Sym,P,S1,S2) = (Sym',P',S1',S2'))∧
  (Re1 (Sym,(IMAGE OUTL P),S1) [] (Sym,(IMAGE OUTL P),S1))∧
  (Re2 (Sym,(IMAGE OUTR P),S2) [] (Sym,(IMAGE OUTR P),S2))))  ∧
((symbolicParlComp ((Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) (Sym,P,S1,S2) (NONE::ev) (Sym',P',S1',S2')) =
(∃P''.
   (∀phi. ((composeDed ded1 ded2) P'' phi) ∧ P'=P''∪{phi}) ∧
   (Re1 (Sym',(IMAGE OUTL P''),S1') [NONE] (Sym',(IMAGE OUTL P'),S1'))∧
  (Re2 (Sym',(IMAGE OUTR P''),S2') [NONE] (Sym',(IMAGE OUTR P'),S2')) ∧
  (symbolicParlComp (Re1,ded1) (Re2,ded2) (Sym,P,S1,S2) ev (Sym',P'',S1',S2'))))  ∧
((symbolicParlComp ((Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) (Sym,P,S1,S2) (SOME(INL (INL (E:'event1)))::ev) (Sym'',P'',S1'',S2')) =
 (∃Sym' P' S1'. (Re1 (Sym',(IMAGE OUTL P'),S1') [SOME(INL E)] (Sym'',(IMAGE OUTL P''),S1''))∧
                ((IMAGE OUTR P') = (IMAGE OUTR P''))∧
                (Re2 (Sym',(IMAGE OUTR P'),S2') [] (Sym'',(IMAGE OUTR P''),S2')) ∧
                (symbolicParlComp (Re1,ded1) (Re2,ded2) (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((symbolicParlComp ((Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) (Sym,P,S1,S2) (SOME(INR (INL (E:'event2)))::ev) (Sym'',P'',S1',S2'')) =
 (∃Sym' P' S2'. (Re2 (Sym',(IMAGE OUTR P'),S2') [SOME(INL E)] (Sym'',(IMAGE OUTR P''),S2''))∧
                ((IMAGE OUTL P') = (IMAGE OUTL P''))∧
                (Re1 (Sym',(IMAGE OUTL P'),S1') [] (Sym'',(IMAGE OUTL P''),S1')) ∧
                (symbolicParlComp (Re1,ded1) (Re2,ded2) (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((symbolicParlComp ((Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) (Sym,P,S1,S2) (SOME(INR (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2'. (Re1 (Sym',(IMAGE OUTL P'),S1') [SOME(INR E)] (Sym'',(IMAGE OUTL P''),S1''))∧
                    (Re2 (Sym',(IMAGE OUTR P'),S2') [SOME(INR E)] (Sym'',(IMAGE OUTR P''),S2'')) ∧
                    (symbolicParlComp (Re1,ded1) (Re2,ded2) (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((symbolicParlComp ((Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) (Sym,P,S1,S2) (SOME(INL (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2'. (Re1 (Sym',(IMAGE OUTL P'),S1') [SOME(INR E)] (Sym'',(IMAGE OUTL P''),S1''))∧
                    (Re2 (Sym',(IMAGE OUTR P'),S2') [SOME(INR E)] (Sym'',(IMAGE OUTR P''),S2''))∧
                    (symbolicParlComp (Re1,ded1) (Re2,ded2) (Sym,P,S1,S2) ev (Sym',P',S1',S2'))))
`;


val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_symbolicParlComp",
                            tok = "||" };

val _ = overload_on ("apply_symbolicParlComp", ``symbolicParlComp``);


val _ = export_theory();

