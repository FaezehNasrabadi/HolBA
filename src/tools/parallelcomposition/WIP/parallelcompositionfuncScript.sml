open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

val _ = new_theory "parallelcompositionfunc";

    
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
(*
val composeDed_def =
Define`
      (composeDed (P3:('pred1 + 'pred2) set) (F3:('pred1 + 'pred2)) =
       (case F3 of
          (INL (F1:'pred1)) => (∃(ded1:('pred1)tded). ded1 (IMAGE OUTL P3) F1)
        | (INR (F2:'pred2)) => (∃(ded2:('pred2)tded). ded2 (IMAGE OUTR P3) F2)
       ))
      `;*)
      
val composeDed_def =
Define`
      (composeDed (ded1:('pred1)tded) (ded2:('pred2)tded) = λ(ded3:('pred1 + 'pred2)tded). ∃P3 F3. (ded3 P3 F3) ∧
       (case F3 of
          (INL (F1:'pred1)) => (ded1 (IMAGE OUTL P3) F1)
        | (INR (F2:'pred2)) => (ded2 (IMAGE OUTR P3) F2)
       ))
      `;
(* compose config *)
val composeCon_def =
Define`
      (composeCon (Sym1,P1,S1) (Sym2,P2,S2)
       = ((Sym1 ∪ Sym2),(P1 <+> P2),S1,S2)
      )`;

(* compose transition *)
val composeTrn_def =
Define`
      composeTrn ((Sym,P,S1,S2):(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (e:(('event1+'eventS) + ('event2 +'eventS))) = 
       ( case e of 
           (INL (INL (E:'event1))) =>
                (λ(Sym',P',S1',S2'). ∃(rel1:('event1 + 'eventS, 'pred1, 'state1, 'symb) trel). (rel1 (Sym,(IMAGE OUTL P),S1) (INL E) (Sym',(IMAGE OUTL P'),S1'))∧(S2 = S2')∧((IMAGE OUTR P) = (IMAGE OUTR P')))
         |   (INR (INL (E:'event2))) =>
               (λ(Sym',P',S1',S2'). ∃(rel2:('event2 + 'eventS, 'pred2, 'state2, 'symb) trel). (rel2 (Sym,(IMAGE OUTR P),S2) (INL E) (Sym',(IMAGE OUTR P'),S2'))∧(S1 = S1')∧((IMAGE OUTL P) = (IMAGE OUTL P')))
         |   (INR (INR (E:'eventS))) =>
               (λ(Sym',P',S1',S2'). ∃(rel1:('event1 + 'eventS, 'pred1, 'state1, 'symb) trel) (rel2:('event2 + 'eventS, 'pred2, 'state2, 'symb) trel) Sym1' Sym2'.
                  (rel1 (Sym,(IMAGE OUTL P),S1) (INR E) (Sym1',(IMAGE OUTL P'),S1'))∧(rel2 (Sym,(IMAGE OUTR P),S2) (INR E) (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2'))
)`;

(*  DB.find_in "BIGSUM" (DB.find "SET"); *)
(* DB.find "MAP"; *)
(* compose transition system *)
val composeOperation_def =
Define`
      (composeOperation ((Sym1,P1,S1),(ded1:('pred1) tded)) ((Sym2,P2,S2),(ded2:('pred2) tded)) = (composeCon (Sym1,P1,S1) (Sym2,P2,S2), composeDed ded1 ded2))
`;


(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:(('symb set) # ('pred set) # 'state) -> ('event list) -> (('symb set) # ('pred set) # 'state) -> bool``);

(* multi transitions system *)    
val _ = Parse.type_abbrev("multransys", ``:(( 'symb, 'pred, 'state, 'event ) mtrel # ('pred) tded)``);


(* compose multi transition relation *)
val _ = Parse.type_abbrev("cmtrel", ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) mtrel ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) mtrel -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) mtrel``);


val composeMuRe_def =
Define  `
        (composeMuRe ((Sym,P,S1,S2):(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Ev:(('event1+'eventS) + ('event2 +'eventS)) list) ((Sym',P',S1',S2'):(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) =
         (case Ev of
            [] => ((Sym,P,S1,S2) = (Sym',P',S1',S2'))  
          | [e] => (composeTrn (Sym,P,S1,S2) e (Sym',P',S1',S2'))
          | (e::ev) => (∃(Sym'', P'', S1'', S2''). 
                          composeMuRe (Sym,P,S1,S2) [e] (Sym'', P'', S1'', S2'') ∧
                          composeMuRe (Sym',P',S1',S2') ev (Sym', P', S1', S2')
                       )
         ))
        `;




val composesystems_def =
Define`
      composesystems (C1,e1,C1') (C2,e2,C2') =
(λ(C,Ev,C'). (C = composeCon C1 C2) ∧
            (case Ev of
               (INL (INL (E:'event1))) => (C' = composeCon C1' C2) ∧ (C2 = C2') ∧ (INL E = e1)
             | (INR (INL (E:'event2))) => (C' = composeCon C1 C2') ∧ (C1 = C1') ∧ (INL E = e2)
             | (INR (INR (E:'eventS))) => (C' = composeCon C1' C2') ∧ (INR E = e1) ∧ (INR E = e2) 
             | (INL (INR (E:'eventS))) => (C' = composeCon C1' C2') ∧ (INR E = e1) ∧ (INR E = e2) 
            ))`;     

val composemultitransystems_def =
Define`
      composemultitransystems (C1,E1,C1') (C2,E2,C2') (C,E,C') =
            (case E of
               []  => (C = C') ∧ (C1 = C1') ∧ (C2 = C2') ∧ (E1 = []) ∧ (E2 = [])        
             | [e] => (∃e1 e2. (composesystems (C1,e1,C1') (C2,e2,C2') (C,e,C')) ∧ (E1 = [e1]) ∧ (E2 = [e2]))
             | (e::ev) => (∃e1 e2 ev1 ev2 C1'' C2'' C''.  (composesystems (C1,e1,C1'') (C2,e2,C2'') (C,e,C'')) ∧ (E1 = e1::ev1) ∧ (E2 = e2::ev2) ∧ (composemultitransystems (C1'',ev1,C1') (C2'',ev2,C2') (C'',ev,C')))
            )`;


(*
val evtrace_def =
Define
`
(evtrace (Conf : α) t (Conf' : α) t' = (case t of
                                          ([]) => ((t' = []) ∧ (Conf = Conf'))
                                        | _ => ((t' = t) ∧ (Conf ≠ Conf'))
                                       ))`;
                                 

val trevtraces_def =
Define`
trevtrace MTrn t' = (∀t Conf Conf'. (evtrace Conf t Conf' t') ∧ (MTrn Conf t Conf'))
                    `;
                    
(* Traces *)
val tracestwo_def =
Define`
      tracestwo (((Sym,P,S1,S2):(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)),(Ev:(('event1+'eventS) + ('event2 +'eventS)) list),((Sym',P',S1',S2'):(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2))) =
(case Ev of
   [] => {}
 | _ => {Ev}
 )`;

                                                                                                                                                                                                                 val tracesone_def =
Define`
      tracesone (((Sym,P1,S1):(('symb set) # ('pred set) # 'state)),(t:'event list),((Sym',P1',S1'):(('symb set) # ('pred set) # 'state))) = {t}
                                                                                                                                             `;

val trace_def =
Define`
      traces (((Sym1,P1,S1):(('symb set) # ('pred1 set) # 'state1)),(t1:'ev1 list),((Sym1',P1',S1'):(('symb set) # ('pred1 set) # 'state1))) (((Sym2,P2,S2):(('symb set) # ('pred set) # 'state)),(t2:'ev2 list),((Sym2',P2',S2'):(('symb set) # ('pred2 set) # 'state2))) = {t}
`;                       
                                                                                                                                                   
                
val compose_vs_module_thm = store_thm(
"compose_vs_module_thm", ``
!Sym Sym' P1 P1' P2 P2' P P' S1 S1' S2 S2' S S' Conf1 Conf1' Conf2 Conf2' Conf Conf' t1 t2 t.
                 ((Conf1 = (Sym,P1,S1)) ∧ (Conf1' = (Sym',P1',S1')) ∧
                (Conf2 = (Sym,P2,S2)) ∧ (Conf2' = (Sym',P2',S2')) ∧
                (Conf = (Sym,P,S)) ∧ (Conf' = (Sym',P',S'))
                 ) ==> ((tracestwo (composemultitransystems (Conf1,t1,Conf1') (Conf,t,Conf'))) ⊆ (tracestwo ((Conf2,t2,Conf2') (Conf,t,Conf')))) ``


*)

                              
val _ = export_theory();

