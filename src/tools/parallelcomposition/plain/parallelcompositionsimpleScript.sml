open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

val _ = new_theory "parallelcompositionsimple";

    
(* transition relation *)
val _ = Parse.type_abbrev("trel", ``:(('symb set) # ('pred set) # 'state) -> 'event -> (('symb set) # ('pred set) # 'state) -> bool``);    

    
(* deduction relation *)    
val _ = Parse.type_abbrev("tded", ``:('pred set) -> 'pred -> bool``);
   
    
(* transition system *)    
val _ = Parse.type_abbrev("transitionsystem", ``:(( 'symb, 'pred, 'state, 'event ) trel # ('pred) tded)``);


val _ = Parse.type_abbrev("ComOpr", 
  ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) transitionsystem ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) transitionsystem -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) transitionsystem``);


(* compose deduction relation *)
val _ = Parse.type_abbrev("ctded", ``:('pred1) tded -> ('pred2) tded -> ('pred1 + 'pred2) tded``);

val composeDed_def =
Define`
      (composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INL (F1:'pred1)) = (ded1 (IMAGE OUTL P3) F1)) ∧
(composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INR (F2:'pred2)) = (ded2 (IMAGE OUTR P3) F2))
`;

(*

val composeDed_def =
Define`
      composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) = (λP3 F3. 
       (case F3 of
          (INL (F1:'pred1)) => (ded1 (IMAGE OUTL P3) F1)
        | (INR (F2:'pred2)) => (ded2 (IMAGE OUTR P3) F2)
       )):('pred1 + 'pred2) tded`;
               
val composeRelations_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
  "composeRelations"
  ‘composeRelations C t C'  =
     if t = [] then
        C = C'
     else C ≠ C'’;    *)              
(* compose transition relation *)(*
val composeRel_def =
Define`
      (composeRel (rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel) (rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel) = (λ((Sym:'symb set),(P:('pred1 + 'pred2) set),(S1:'state1),(S2:'state2)) (e:(('event1 + 'eventS) + ('event2 + 'eventS))) ((Sym':'symb set),(P':('pred1 + 'pred2) set),(S1':'state1),(S2':'state2)).
       ( case e of 
           (INL (INL (E:'event1))) =>
             ((rel1 (Sym,(IMAGE OUTL P),S1) (INL E) (Sym',(IMAGE OUTL P'),S1'))∧(S2 = S2')∧((IMAGE OUTR P) = (IMAGE OUTR P')))
         |   (INR (INL (E:'event2))) =>
               ((rel2 (Sym,(IMAGE OUTR P),S2) (INL E) (Sym',(IMAGE OUTR P'),S2'))∧(S1 = S1')∧((IMAGE OUTL P) = (IMAGE OUTL P')))
         |   (INR (INR (E:'eventS))) =>
               (∃Sym1' Sym2'.
                  (rel1 (Sym,(IMAGE OUTL P),S1) (INR E) (Sym1',(IMAGE OUTL P'),S1'))∧(rel2 (Sym,(IMAGE OUTR P),S2) (INR E) (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2'))
       )))`;

       
(* compose transition system *)
val composeOperation_def =
Define`
      (composeOperation ((rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel),(ded1:('pred1) tded)) ((rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel),(ded2:('pred2) tded)) = (composeRel rel1 rel2, composeDed ded1 ded2): ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) transitionsystem)
`;
*)

(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:(('symb set) # ('pred set) # 'state) -> ('event list) -> (('symb set) # ('pred set) # 'state) -> bool``);

(* multi transitions system *)    
val _ = Parse.type_abbrev("multransys", ``:(( 'symb, 'pred, 'state, 'event ) mtrel # ('pred) tded)``);


(* compose multi transition relation *)
val _ = Parse.type_abbrev("cmtrel", ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) mtrel ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) mtrel -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) mtrel``);

(*
val composeMuRe_def =
Define  `
        ((composeMuRe Re1 Re2 (Sym,P,S1,S2) [] (Sym',P',S1',S2')) = ((Sym,P,S1,S2) = (Sym',P',S1',S2')))  ∧
        ((composeMuRe Re1 Re2 (Sym,P,S1,S2) [e] (Sym',P',S1',S2')) = (∃rel1 rel2. (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧ (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL [e]) (Sym',(IMAGE OUTL P'),S1')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR [e]) (Sym',(IMAGE OUTR P'),S2'))))  ∧
((composeMuRe Re1 Re2 (Sym,P,S1,S2) (e::ev) (Sym'',P'',S1'',S2'')) = 
 (∃Sym' P' S1' S2' rel1 rel2 Re1' Re2'. (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧ (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL (e::ev)) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR (e::ev)) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re2' (Sym',(IMAGE OUTR P'),S2') (MAP OUTR ev) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re1' (Sym',(IMAGE OUTL P'),S1') (MAP OUTL ev) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (composeMuRe Re1' Re2' (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))
`;


val composeMuRe_def =
Define  `
        ((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
         ((Sym,P,S1,S2) = (Sym',P',S1',S2')))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [(INL (INL (E:'event1)))] (Sym',P',S1',S2')) =
 ((Re1 (Sym,(IMAGE OUTL P),S1) [INL E] (Sym',(IMAGE OUTL P'),S1'))∧(S2 = S2')∧((IMAGE OUTR P) = (IMAGE OUTR P')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [(INR (INL (E:'event2)))] (Sym',P',S1',S2')) =
 ((Re2 (Sym,(IMAGE OUTR P),S2) [INL E] (Sym',(IMAGE OUTR P'),S2'))∧(S1 = S1')∧((IMAGE OUTL P) = (IMAGE OUTL P')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [(INR (INR (E:'eventS)))] (Sym',P',S1',S2')) =
 (∃Sym1' Sym2'. (Re1 (Sym,(IMAGE OUTL P),S1) [INR E] (Sym1',(IMAGE OUTL P'),S1'))∧(Re2 (Sym,(IMAGE OUTR P),S2) [INR E] (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2'))) ∧
((composeMuRe Re1 Re2 (Sym,P,S1,S2) (e::ev) (Sym'',P'',S1'',S2'')) = 
 (∃Sym' P' S1' S2'. (composeMuRe Re1 Re2 (Sym,P,S1,S2) [e] (Sym',P',S1',S2')) ∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))
`;  

*)
val FIRST_def =
Define  `
        ((FIRST (a,b,c)) = a)
        `;
val SECOND_def =
Define  `
        ((SECOND (a,b,c)) = b)
        `;
val THIRD_def =
Define  `
        ((THIRD (a,b,c)) = c)
        `;

val triple_same_thm = store_thm(
  "triple_same_thm", ``
∀a b c.
((FIRST (a,b,c)),(SECOND (a,b,c)),(THIRD (a,b,c))) = (a,b,c)
                                       ``,
 FULL_SIMP_TAC std_ss [FIRST_def,SECOND_def,THIRD_def]  
  );

val triple_to_quadruple_thm = store_thm(
  "triple_to_quadruple_thm", ``
∀a b c a' b' c'.
((FIRST (a,b,c))∪(FIRST (a',b',c')),(SECOND (a,b,c))⊔(SECOND (a',b',c')),(THIRD (a,b,c)),(THIRD (a',b',c'))) = (a∪a',b⊔b',c,c')
                                       ``,
 FULL_SIMP_TAC std_ss [FIRST_def,SECOND_def,THIRD_def]  
  );
   
 (*       
val composeMuRe_def =
Define  `
        ((composeMuRe Re1 Re2 (Sym,P,S1,S2) [] (Sym',P',S1',S2')) = ((Sym,P,S1,S2) = (Sym',P',S1',S2')))  ∧
        ((composeMuRe Re1 Re2 (Sym,P,S1,S2) [e] (Sym',P',S1',S2')) = ( case e of 
           (INL (INL (E:'event1))) =>
             ((Re1 (Sym,(IMAGE OUTL P),S1) [INL E] (Sym',(IMAGE OUTL P'),S1'))∧(S2 = S2')∧((IMAGE OUTR P) = (IMAGE OUTR P')))
         |   (INR (INL (E:'event2))) =>
               ((Re2 (Sym,(IMAGE OUTR P),S2) [INL E] (Sym',(IMAGE OUTR P'),S2'))∧(S1 = S1')∧((IMAGE OUTL P) = (IMAGE OUTL P')))
         |   (INR (INR (E:'eventS))) =>
               (∃Sym1' Sym2'.
                  (Re1 (Sym,(IMAGE OUTL P),S1) [INR E] (Sym1',(IMAGE OUTL P'),S1'))∧(Re2 (Sym,(IMAGE OUTR P),S2) [INR E] (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2')))) ∧
        ((composeMuRe Re1 Re2 (Sym,P,S1,S2) (e::ev) (Sym'',P'',S1'',S2'')) = 
         (∃Sym' P' S1' S2'. (composeMuRe Re1 Re2 (Sym,P,S1,S2) [e] (Sym',P',S1',S2')) ∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))
        `;

val composeMuRe_def =
Define  `
        ((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
         ((Sym,P,S1,S2) = (Sym',P',S1',S2')))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INL (E:'event1)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' P1 P1' P2 P2'. (P = P1<+>P2)∧(P' = P1'<+>P2')∧(Re1 (Sym,P1,S1) [INL E] (Sym',P1',S1'))∧(P2 = P2')∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2) ev (Sym'',P'',S1'',S2'')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INL (E:'event2)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S2' P1 P1' P2 P2'. (P = P1<+>P2)∧(P' = P1'<+>P2')∧(Re2 (Sym,P2,S2) [INL E] (Sym',P2',S2'))∧(P1 = P1')∧ (composeMuRe Re1 Re2 (Sym',P',S1,S2') ev (Sym'',P'',S1'',S2'')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym1' Sym2' Sym' P' S1' S2' P1 P1' P2 P2'. (P = P1<+>P2)∧(P' = P1'<+>P2')∧(Re1 (Sym,P1,S1) [INR E] (Sym1',P1',S1'))∧(Re2 (Sym,P2,S2) [INR E] (Sym2',P2',S2'))∧(Sym' = Sym1'∪Sym2') ∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))
`;      *)

(*
Inductive composeMuRe:
[~nil:]
  (composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym,P,S1,S2)) /\
[~left:]
  (((composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')) /\ (Re1 (Sym',(IMAGE OUTL P'),S1') [INL e1] (Sym'',(IMAGE OUTL P''),S1'')) /\ ((IMAGE OUTR P') = (IMAGE OUTR P'')))
                 ==> (composeMuRe Re1 Re2 (Sym,P,S1,S2) ((INL (INL e1))::ev) (Sym'',P'',S1'',S2'))) /\
[~right:]                                                                        
  (((composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')) /\ (Re2 (Sym',(IMAGE OUTR P'),S2') [INL e2] (Sym'',(IMAGE OUTR P''),S2'')) /\ ((IMAGE OUTL P') = (IMAGE OUTL P'')))
                 ==> (composeMuRe Re1 Re2 (Sym,P,S1,S2) ((INR (INL e2))::ev) (Sym'',P'',S1',S2''))) /\
[~sync:]                                                                        
  (((composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')) /\ (Re1 (Sym',(IMAGE OUTL P'),S1') [INR es] (Sym1'',(IMAGE OUTL P''),S1'')) /\
                 (Re2 (Sym',(IMAGE OUTR P'),S2') [INR es] (Sym2'',(IMAGE OUTR P''),S2'')) /\ (Sym''' = (Sym1'' ∪ Sym2'')))
                 ==> (composeMuRe Re1 Re2 (Sym,P,S1,S2) ((INR (INR es))::ev) (Sym'',P'',S1',S2'')))
End

Definition composeMuRe:
[~nil:]
  (composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym,P,S1,S2)) /\
[~left:]
  (((composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')) /\ (Re1 (Sym',(IMAGE OUTL P'),S1') [INL e1] (Sym'',(IMAGE OUTL P''),S1'')) /\ ((IMAGE OUTR P') = (IMAGE OUTR P'')))
                 ==> (composeMuRe Re1 Re2 (Sym,P,S1,S2) ((INL (INL e1))::ev) (Sym'',P'',S1'',S2'))) /\
[~right:]                                                                        
  (((composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')) /\ (Re2 (Sym',(IMAGE OUTR P'),S2') [INL e2] (Sym'',(IMAGE OUTR P''),S2'')) /\ ((IMAGE OUTL P') = (IMAGE OUTL P'')))
                 ==> (composeMuRe Re1 Re2 (Sym,P,S1,S2) ((INR (INL e2))::ev) (Sym'',P'',S1',S2''))) /\
[~sync:]                                                                        
  (((composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')) /\ (Re1 (Sym',(IMAGE OUTL P'),S1') [INR es] (Sym1'',(IMAGE OUTL P''),S1'')) /\
                 (Re2 (Sym',(IMAGE OUTR P'),S2') [INR es] (Sym2'',(IMAGE OUTR P''),S2'')) /\ (Sym''' = (Sym1'' ∪ Sym2'')))
                 ==> (composeMuRe Re1 Re2 (Sym,P,S1,S2) ((INR (INR es))::ev) (Sym'',P'',S1',S2'')))
End   *)

      

val composeMuRe_def =
Define  `
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
         (((Sym,P,S1,S2) = (Sym',P',S1',S2'))∧(Re1 (Sym,(IMAGE OUTL P),S1) [] (Sym,(IMAGE OUTL P),S1))∧(Re2 (Sym,(IMAGE OUTR P),S2) [] (Sym,(IMAGE OUTR P),S2))))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INL (E:'event1)))::ev) (Sym'',P'',S1'',S2')) =
 (∃Sym' P' S1'. (Re1 (Sym',(IMAGE OUTL P'),S1') [INL E] (Sym'',(IMAGE OUTL P''),S1''))∧((IMAGE OUTR P') = (IMAGE OUTR P''))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [] (Sym'',(IMAGE OUTR P''),S2')) ∧(composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INL (E:'event2)))::ev) (Sym'',P'',S1',S2'')) =
 (∃Sym' P' S2'. (Re2 (Sym',(IMAGE OUTR P'),S2') [INL E] (Sym'',(IMAGE OUTR P''),S2''))∧((IMAGE OUTL P') = (IMAGE OUTL P''))∧(Re1 (Sym',(IMAGE OUTL P'),S1') [] (Sym'',(IMAGE OUTL P''),S1')) ∧(composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2'. (Re1 (Sym',(IMAGE OUTL P'),S1') [INR E] (Sym'',(IMAGE OUTL P''),S1''))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [INR E] (Sym'',(IMAGE OUTR P''),S2'')) ∧ (composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2'. (Re1 (Sym',(IMAGE OUTL P'),S1') [INR E] (Sym'',(IMAGE OUTL P''),S1''))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [INR E] (Sym'',(IMAGE OUTR P''),S2''))∧ (composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2'))))
`;


(*after changing composeMuRe definition
val composeMuRe_def =
Define  `
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
         (∃t1 t2. (t1 = [])∧(t2 = [])∧((Sym,P,S1,S2) = (Sym',P',S1',S2'))∧(Re1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1'))∧(Re2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2'))))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INL (E:'event1)))::ev) (Sym'',P'',S1'',S2')) =
 (∃Sym' P' S1' t1 t2. (Re1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1'))∧(Re1 (Sym',(IMAGE OUTL P'),S1') [INL E] (Sym'',(IMAGE OUTL P''),S1''))∧((IMAGE OUTR P') = (IMAGE OUTR P''))∧(Re2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2'))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [] (Sym'',(IMAGE OUTR P''),S2')) ∧(composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INL (E:'event2)))::ev) (Sym'',P'',S1',S2'')) =
 (∃Sym' P' S2' t1 t2. (Re2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2'))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [INL E] (Sym'',(IMAGE OUTR P''),S2''))∧((IMAGE OUTL P') = (IMAGE OUTL P''))∧(Re1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1'))∧(Re1 (Sym',(IMAGE OUTL P'),S1') [] (Sym'',(IMAGE OUTL P''),S1')) ∧(composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2' t1 t2. (Re1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1'))∧(Re1 (Sym',(IMAGE OUTL P'),S1') [INR E] (Sym'',(IMAGE OUTL P''),S1''))∧(Re2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2'))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [INR E] (Sym'',(IMAGE OUTR P''),S2'')) ∧ (composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2' t1 t2. (Re1 (Sym,(IMAGE OUTL P),S1) t1 (Sym',(IMAGE OUTL P'),S1'))∧(Re1 (Sym',(IMAGE OUTL P'),S1') [INR E] (Sym'',(IMAGE OUTL P''),S1''))∧(Re2 (Sym,(IMAGE OUTR P),S2) t2 (Sym',(IMAGE OUTR P'),S2'))∧(Re2 (Sym',(IMAGE OUTR P'),S2') [INR E] (Sym'',(IMAGE OUTR P''),S2''))∧ (composeMuRe Re1 Re2 (Sym,P,S1,S2) ev (Sym',P',S1',S2'))))
`;
  *)    
(*
val composeMuRe_def =
Define  `
        ((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
         (((Sym,P,S1,S2) = (Sym',P',S1',S2'))∧(Re1 (Sym,(IMAGE OUTL P),S1) [] (Sym,(IMAGE OUTL P),S1))∧(Re2 (Sym,(IMAGE OUTR P),S2) [] (Sym,(IMAGE OUTR P),S2))))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INL (E:'event1)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1'. (Re1 (Sym,(IMAGE OUTL P),S1) [INL E] (Sym',(IMAGE OUTL P'),S1'))∧((IMAGE OUTR P) = (IMAGE OUTR P'))∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2) ev (Sym'',P'',S1'',S2'')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INL (E:'event2)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S2'. (Re2 (Sym,(IMAGE OUTR P),S2) [INL E] (Sym',(IMAGE OUTR P'),S2'))∧((IMAGE OUTL P) = (IMAGE OUTL P'))∧ (composeMuRe Re1 Re2 (Sym',P',S1,S2') ev (Sym'',P'',S1'',S2'')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INR (E:'eventS)))::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym1' Sym2' Sym' P' S1' S2'. (Re1 (Sym,(IMAGE OUTL P),S1) [INR E] (Sym1',(IMAGE OUTL P'),S1'))∧(Re2 (Sym,(IMAGE OUTR P),S2) [INR E] (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2') ∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))
`;*)

(*
val composeMuRe_def =
Define  `
        ((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [] (Sym',P',S1',S2')) =
         ((Sym,P,S1,S2) = (Sym',P',S1',S2')))  ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [(INL (INL (E:'event1)))] (Sym',P',S1',S2')) =
 ((Re1 (Sym,(IMAGE OUTL P),S1) [INL E] (Sym',(IMAGE OUTL P'),S1'))∧((IMAGE OUTR P) = (IMAGE OUTR P')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [(INR (INL (E:'event2)))] (Sym',P',S1',S2')) =
 ((Re2 (Sym,(IMAGE OUTR P),S2) [INL E] (Sym',(IMAGE OUTR P'),S2'))∧((IMAGE OUTL P) = (IMAGE OUTL P')))) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) [(INR (INR (E:'eventS)))] (Sym',P',S1',S2')) =
 (∃Sym1' Sym2'. (Re1 (Sym,(IMAGE OUTL P),S1) [INR E] (Sym1',(IMAGE OUTL P'),S1'))∧(Re2 (Sym,(IMAGE OUTR P),S2) [INR E] (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2')))∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) (e::ev) (Sym'',P'',S1'',S2'')) =
 (∃Sym' P' S1' S2'.  (composeMuRe Re1 Re2  (Sym,P,S1,S2) [e] (Sym',P',S1',S2')) ∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))
`; 
*)
        
(*
val composeMuRe_def =
Define  `
        ((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) []) = (Sym,P,S1,S2)) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INL (INL (E:'event1)))::ev))
 = composeMuRe Re1 Re2 ((FIRST(Re1 (Sym,(IMAGE OUTL P),S1) [INL E]),((SECOND(Re1 (Sym,(IMAGE OUTL P),S1) [INL E]))<+>(IMAGE OUTR P)),THIRD(Re1 (Sym,(IMAGE OUTL P),S1) [INL E]),S2)) ev)   ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INL (E:'event2)))::ev))
 = composeMuRe Re1 Re2 ((FIRST(Re2 (Sym,(IMAGE OUTR P),S2) [INL E]),((IMAGE OUTL P)<+>(SECOND(Re2 (Sym,(IMAGE OUTR P),S2) [INL E]))),S1,THIRD(Re2 (Sym,(IMAGE OUTR P),S2) [INL E]))) ev) ∧
((composeMuRe (Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym,P,S1,S2) ((INR (INR (E:'eventS)))::ev))
 = composeMuRe Re1 Re2 (((FIRST(Re1 (Sym,(IMAGE OUTL P),S1) [INR E]))∪(FIRST(Re2 (Sym,(IMAGE OUTR P),S2) [INR E])),((SECOND(Re1 (Sym,(IMAGE OUTL P),S1) [INR E]))<+>(SECOND(Re2 (Sym,(IMAGE OUTR P),S2) [INR E]))),THIRD(Re1 (Sym,(IMAGE OUTL P),S1) [INR E]),THIRD(Re2 (Sym,(IMAGE OUTR P),S2) [INR E]))) ev)
`;
val composeMuRe_empty_event_thm = store_thm(
  "composeMuRe_empty_event_thm", ``
∀Re1 Re2 Sym P S1 S2 Sym' P' S1' S2'.
(composeMuRe Re1 Re2 (Sym,P,S1,S2) [] (Sym',P',S1',S2')) = ((Sym,P,S1,S2) = (Sym',P',S1',S2'))
                                       ``,
 FULL_SIMP_TAC std_ss [composeMuRe_def]  
  );
  
val composeMuRe_single_event_thm = store_thm(
  "composeMuRe_single_event_thm", ``
∀Re1 Re2 Sym P S1 S2 e Sym' P' S1' S2'.
(composeMuRe Re1 Re2 (Sym,P,S1,S2) [e] (Sym',P',S1',S2')) ⇒ (∃rel1 rel2. (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym',P',S1',S2')))
                                      ``,
                                      FULL_SIMP_TAC std_ss [composeMuRe_def]>> REPEAT GEN_TAC >> REPEAT STRIP_TAC >>
                                      Q.EXISTS_TAC `rel1` >> Q.EXISTS_TAC `rel2` >> ASM_REWRITE_TAC[]
                                          
  );

val composeMuRe_multi_events_thm = store_thm(
  "composeMuRe_multi_events_thm", ``
                                  ∀Re1 Re2 Sym P S1 S2 e e1 e2 Sym'' P'' S1'' S2''.
                                    (composeMuRe Re1 Re2 (Sym,P,S1,S2) (e::e1::e2) (Sym'',P'',S1'',S2'')) ⇒
                                    (∃Sym'³' P'³' S1'³' S2'³' rel1 rel2 Re1' Re2'. (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym'³',P'³',S1'³',S2'³')) ∧ (composeMuRe Re1' Re2' (Sym'³',P'³',S1'³',S2'³') (e1::e2) (Sym'',P'',S1'',S2'')))
                                    ``,
                                    FULL_SIMP_TAC std_ss [composeMuRe_def]>> REPEAT GEN_TAC >> REPEAT STRIP_TAC >> Q.EXISTS_TAC `Sym'³'` >> Q.EXISTS_TAC `P'³'` >>
                                  Q.EXISTS_TAC `S1'³'` >> Q.EXISTS_TAC `S2'³'` >> Q.EXISTS_TAC `rel1` >> Q.EXISTS_TAC `rel2` >>
                                  Q.EXISTS_TAC `Re1'` >> Q.EXISTS_TAC `Re2'` >> REPEAT STRIP_TAC >> ASM_REWRITE_TAC[] >> ASM_REWRITE_TAC[]
                                                                                                                                        
  );

val composeMuRe_StatetoConfig_thm = store_thm(
  "composeMuRe_StatetoConfig_thm", ``
∀Re1 Re2 Sym P S1 S2 E Sym' P' S1' S2'.
(composeMuRe Re1 Re2 (Sym,P,S1,S2) E (Sym',P',S1',S2')) ==> (∃Conf Conf'. (composeMuRe Re1 Re2 Conf E Conf') ∧ (Conf = (Sym,P,S1,S2)) ∧ (Conf' = (Sym',P',S1',S2')))
                                       ``,
 FULL_SIMP_TAC std_ss [composeMuRe_def]  
  );*)


(*
val composeMuRe_def =
Define  `

composeMuRe Re1 Re2 = 
 (λ(Sym,P,S1,S2) E (Sym'',P'',S1'',S2'').
( case E of
             [] => ((Sym,P,S1,S2) = (Sym',P',S1',S2'))
           | ((INL (INL (E:'event1)))::ev) => (∃Sym' P' S1' P1 P1' P2 P2'. (P = P1<+>P2)∧(P' = P1'<+>P2')∧(Re1 (Sym,P1,S1) [INL E] (Sym',P1',S1'))∧(P2 = P2')∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2) ev (Sym'',P'',S1'',S2'')))
           | ((INR (INL (E:'event2)))::ev) => (∃Sym' P' S2' P1 P1' P2 P2'. (P = P1<+>P2)∧(P' = P1'<+>P2')∧(Re2 (Sym,P2,S2) [INL E] (Sym',P2',S2'))∧(P1 = P1')∧ (composeMuRe Re1 Re2 (Sym',P',S1,S2') ev (Sym'',P'',S1'',S2'')))
           | ((INR (INR (E:'eventS)))::ev) => (∃Sym1' Sym2' Sym' P' S1' S2' P1 P1' P2 P2'. (P = P1<+>P2)∧(P' = P1'<+>P2')∧(Re1 (Sym,P1,S1) [INR E] (Sym1',P1',S1'))∧(Re2 (Sym,P2,S2) [INR E] (Sym2',P2',S2'))∧(Sym' = Sym1'∪Sym2') ∧ (composeMuRe Re1 Re2 (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2'')))
         )
   ) 
`;

val composeMuRe_def =
Define  `
        ((composeMuRe Re1 Re2) =
         (λ(Sym,P,S1,S2) E (Sym',P',S1',S2'). ∃rel1, rel2 e.
                                                  (E = [e]) ∧ (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧
                                                  (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL [e]) (Sym',(IMAGE OUTL P'),S1')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧
                                                  (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR [e]) (Sym',(IMAGE OUTR P'),S2')))) ∧
((composeMuRe Re1 Re2) = 
 (λ (Sym,P,S1,S2) E (Sym'',P'',S1'',S2''). ∃Sym',P',S1',S2', rel1, rel2, Re1', Re2' e ev.
                                                   (E = (e::ev)) ∧ (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧
                                                   (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL (e::ev)) (Sym'',(IMAGE OUTL P''),S1'')) ∧
                                                   (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR (e::ev)) (Sym'',(IMAGE OUTR P''),S2'')) ∧
                                                   (Re2' (Sym',(IMAGE OUTR P'),S2') (MAP OUTR ev) (Sym'',(IMAGE OUTR P''),S2'')) ∧
                                                   (Re1' (Sym',(IMAGE OUTL P'),S1') (MAP OUTL ev) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (composeMuRe Re1' Re2' (Sym',P',S1',S2') ev (Sym'',P'',S1'',S2''))))     
`;

val composeMuRe_def =
Define  `
        (composeMuRe Re1 Re2 (Sym,P,S1,S2) E (Sym',P',S1',S2') =
         ( case E of
             [] => ((Sym,P,S1,S2) = (Sym',P',S1',S2'))
           | [e] => (∃rel1, rel2 e. ((composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧
                                     (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL [e]) (Sym',(IMAGE OUTL P'),S1')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧
                                     (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR [e]) (Sym',(IMAGE OUTR P'),S2'))))  
           | (e::ev) => (∃Sym'',P'',S1'',S2'', rel1, rel2, Re1', Re2' e ev.
                           (composeRel rel1 rel2 (Sym,P,S1,S2) e (Sym'',P'',S1'',S2'')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym'',(IMAGE OUTL P''),S1'')) ∧
                           (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL (e::ev)) (Sym',(IMAGE OUTL P'),S1')) ∧
                           (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR (e::ev)) (Sym',(IMAGE OUTR P'),S2')) ∧
                           (Re2' (Sym'',(IMAGE OUTR P''),S2'') (MAP OUTR ev) (Sym',(IMAGE OUTR P'),S2')) ∧
                           (Re1' (Sym'',(IMAGE OUTL P''),S1'') (MAP OUTL ev) (Sym',(IMAGE OUTL P'),S1')) ∧ (composeMuRe Re1' Re2' (Sym'',P'',S1'',S2'') ev (Sym',P',S1',S2')))
         ))`;  

val (composeMuRe_rules, composeMuRe_ind, composeMuRe_cases)
= Hol_reln
  `(∀(Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Conf:(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (e:(('event1 + 'eventS) + ('event2 + 'eventS))) (rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel) (rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel) (Conf':(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Sym:'symb set) (P:('pred1 + 'pred2) set) (S1:'state1) (S2:'state2) (Sym':'symb set) (P':('pred1 + 'pred2) set) (S1':'state1) (S2':'state2).
      ((composeRel rel1 rel2 Conf e Conf') ∧ (Conf = (Sym,P,S1,S2)) ∧ (Conf' = (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧ (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL [e]) (Sym',(IMAGE OUTL P'),S1')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR [e]) (Sym',(IMAGE OUTR P'),S2'))) ==> (composeMuRe Re1 Re2 Conf [e] Conf')) ∧
(∀(Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Conf:(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (e:(('event1 + 'eventS) + ('event2 + 'eventS))) (rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel) (rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel) (Conf':(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Sym:'symb set) (P:('pred1 + 'pred2) set) (S1:'state1) (S2:'state2) (Sym':'symb set) (P':('pred1 + 'pred2) set) (S1':'state1) (S2':'state2) (Re1':(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2':(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (ev:(('event1 + 'eventS) + ('event2 + 'eventS)) list) (Evs:(('event1 + 'eventS) + ('event2 + 'eventS)) list) (Conf'':(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Sym'':'symb set) (P'':('pred1 + 'pred2) set) (S1'':'state1) (S2'':'state2).
   ((Evs = (e::ev)) ∧ (composeRel rel1 rel2 Conf e Conf') ∧ (Conf = (Sym,P,S1,S2)) ∧ (Conf' = (Sym',P',S1',S2')) ∧ (Conf'' = (Sym'',P'',S1'',S2'')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧ (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL Evs) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR Evs) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re2' (Sym',(IMAGE OUTR P'),S2') (MAP OUTR ev) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re1' (Sym',(IMAGE OUTL P'),S1') (MAP OUTL ev) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (composeMuRe Re1' Re2' Conf' ev Conf'')) ==> (composeMuRe Re1 Re2 Conf Evs Conf''))     
`; 
*)
(* compose multi transition system *)
val _ = Parse.type_abbrev("MulComOpr", 
  ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) multransys ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) multransys -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) multransys``);

val composeMultiOperation_def =
Define`
      (composeMultiOperation ((rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) = (composeMuRe rel1 rel2, composeDed ded1 ded2): ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) multransys)
      `;   

val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_composeMultiOperation",
                            tok = "||" };

val _ = overload_on ("apply_composeMultiOperation", ``composeMultiOperation``);
(*

val composeMultiOperation_def =
Define`
      composeMultiOperation ((rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) =

(λ(Sym,P,S1,S2) E (Sym',P',S1',S2'). ((composeMuRe rel1 rel2 (Sym,P,S1,S2) E (Sym',P',S1',S2')),
                                                   (∀y. (y ∈ (P' DIFF P)) ⇒ (composeDed ded1 ded2 P y))))
      `; 
        
 val composeMultiOperation_def =
Define`
      (composeMultiOperation ((rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) =
                             ((λ(Sym,P,S1,S2) E (Sym',P',S1',S2'). composeMuRe rel1 rel2 (Sym,P,S1,S2) E (Sym',P',S1',S2')), composeDed ded1 ded2): ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) multransys)
      `;
      val combinelists_def =
Define`
      (combinelists ([]:α list) ([]:β list) = (APPEND [] [])) ∧
(combinelists ([]:α list) ((e2::ev2):β list) = APPEND (APPEND [] [INR e2]) (combinelists [] ev2))  ∧
(combinelists ((e1::ev1):α list) ([]:β list) = APPEND (APPEND [INL e1] []) (combinelists ev1 [])) ∧
(combinelists ((e1::ev1):α list) (E2:β list) = APPEND [INL e1] (combinelists ev1 E2)) ∧
(combinelists (E1:α list) ((e2::ev2):β list) = APPEND [INR e2] (combinelists E1 ev2))
`; 
*)
val combinelists_def =
Define`
      (combinelists ([]:α list) ([]:β list) = (APPEND [] [])) ∧
      (combinelists ([]:α list) ((e2::ev2):β list) = APPEND (APPEND [] [INR e2]) (combinelists [] ev2))  ∧
(combinelists ((e1::ev1):α list) ([]:β list) = APPEND (APPEND [INL e1] []) (combinelists ev1 [])) ∧
(combinelists ((e1::ev1):α list) ((e2::ev2):β list) = APPEND (APPEND [INL e1] [INR e2]) (combinelists ev1 ev2))
`;      
(*
 val composeMultiOperation_def =
Define`
      composeMultiOperation Re1 (Sym1,P1,S1) E1 Re2 (Sym2,P2,S2) E2 = (composeMuRe Re1 Re2 ((Sym1∪Sym2),(P1<+>P2),S1,S2) (combinelists E1 E2))
      `;*)
val _ = export_theory();

