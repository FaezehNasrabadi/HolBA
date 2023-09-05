open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

val _ = new_theory "parallelcompositionemptydeduction";

    
(* transition relation *)
val _ = Parse.type_abbrev("trel", ``:(('symb set) # ('pred set) # 'state) -> 'event -> (('symb set) # ('pred set) # 'state) -> bool``);    

    
(* deduction relation *)    
val _ = Parse.type_abbrev("tded", ``:('pred set) -> 'pred -> bool``);


(* Symbolic LTS *)
                                                                                                                            val symbolicLTS_def =
Define`
      symbolicLTS ((Sym:('symb set)),(P:('pred set)),(S:'state),(E:'event),(Trn:('event, 'pred, 'state , 'symb ) trel),(Ded:('pred) tded)) =
((∃(Sym':('symb set)) (P':('pred set)) (S':'state). (Trn (Sym,P,S) E (Sym',P',S'))) ∧
               (∀phi empty. (Ded P phi) ⇒ (Trn (Sym,P,S) empty (Sym,(P∪{phi}),S))))                                                                                                                    
`;

(*
 val symbolicLTS_def =
Define`
      symbolicLTS (((Sym:('symb set)),(P:('pred set)),(S:'state)),(E:'event),(Trn:('event, 'pred, 'state , 'symb ) trel)) = (∃(Sym':('symb set)) (P':('pred set)) (S':'state). (Trn (Sym,P,S) E (Sym',P',S')) ∧ (∃(Ded:('pred) tded). ∀phi. (phi ∈ (P' DIFF P)) ⇒ (Ded P phi)))`;
                                                                                                                                                                                                                                                                                
(* Establishes the relation between the deduction relation and the current predicate set*)    
val ConnectDed = new_axiom ("ConnectDed",
                            ``∀(Trn:('event, 'pred, 'state , 'symb ) trel) (Ded:('pred) tded) v p s phi (empty:'event). (Ded p phi) ⇒ (Trn (v,p,s) empty (v,(p ∪ {phi}),s))``);
*)                                  

(* compose deduction relation *)
val _ = Parse.type_abbrev("ctded", ``:('pred1) tded -> ('pred2) tded -> ('pred1 + 'pred2) tded``);

val composeDed_def =
Define`
      (composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INL (F1:'pred1)) = (ded1 (IMAGE OUTL P3) F1)) ∧
(composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INR (F2:'pred2)) = (ded2 (IMAGE OUTR P3) F2))
`;

(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:(('symb set) # ('pred set) # 'state) -> ('event list) -> (('symb set) # ('pred set) # 'state) -> bool``);

(* Symbolic LTS *)
 val symbolicMLTS_def =
Define`
      symbolicMLTS ((Sym:('symb set)),(P:('pred set)),(S:'state),(E:'event list),(MTrn:('event, 'pred, 'state , 'symb ) mtrel),(Ded:('pred) tded)) =
((∃(Sym':('symb set)) (P':('pred set)) (S':'state). (MTrn (Sym,P,S) E (Sym',P',S'))) ∧
               (∀phi empty. (Ded P phi) ⇒ (MTrn (Sym,P,S) [empty] (Sym,(P∪{phi}),S))))
`;    
    
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

val combinelists_def =
Define`
      (combinelists ([]:α list) ([]:β list) = (APPEND [] [])) ∧
      (combinelists ([]:α list) ((e2::ev2):β list) = APPEND (APPEND [] [INR e2]) (combinelists [] ev2))  ∧
(combinelists ((e1::ev1):α list) ([]:β list) = APPEND (APPEND [INL e1] []) (combinelists ev1 [])) ∧
(combinelists ((e1::ev1):α list) ((e2::ev2):β list) = APPEND (APPEND [INL e1] [INR e2]) (combinelists ev1 ev2))
`;

(* Symbolic Parallel Composition *)
val symbolicParallelComposition_def =
Define`
      symbolicParallelComposition ((Sym1:('symb set)),(P1:('pred1 set)),(S1:'state1),(E1:('event1 + 'eventS) list),(MTrn1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel),(ded1:('pred1) tded)) ((Sym2:('symb set)),(P2:('pred2 set)),(S2:'state2),(E2:('event2 + 'eventS) list),(MTrn2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel),(ded2:('pred2) tded)) =
(symbolicMLTS ((Sym1 ∪ Sym2),(P1<+>P2),(S1,S2),(combinelists E1 E2),(composeMuRe MTrn1 MTrn2),(composeDed ded1 ded2)))
`;   

val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_symbolicParallelComposition",
                            tok = "||" };

val _ = overload_on ("apply_symbolicParallelComposition", ``symbolicParallelComposition``);

val _ = export_theory();

