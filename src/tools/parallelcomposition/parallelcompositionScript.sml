open HolKernel Parse boolLib bossLib;
open sumTheory;

val _ = new_theory "parallelcomposition";

    
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
val composeDed_def =
Define`
      (composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INL (F1:'pred1)) = (ded1 (IMAGE OUTL P3) F1)) ∧
(composeDed (ded1:('pred1) tded) (ded2:('pred2) tded) (P3:('pred1 + 'pred2) set) (INR (F2:'pred2)) = (ded2 (IMAGE OUTR P3) F2))
`;


        
(* compose transition relation *)
val composeRel_def =
Define`
      (composeRel (rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel) (rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel) ((Sym:'symb set),(P:('pred1 + 'pred2) set),(S1:'state1),(S2:'state2)) (e:(('event1 + 'eventS) + ('event2 + 'eventS))) ((Sym':'symb set),(P':('pred1 + 'pred2) set),(S1':'state1),(S2':'state2))
       = 
       ( case e of 
           (INL (INL (E:'event1))) =>
             ((rel1 (Sym,(IMAGE OUTL P),S1) (INL E) (Sym',(IMAGE OUTL P'),S1'))∧(S2 = S2')∧((IMAGE OUTR P) = (IMAGE OUTR P')))
         |   (INR (INL (E:'event2))) =>
               ((rel2 (Sym,(IMAGE OUTR P),S2) (INL E) (Sym',(IMAGE OUTR P'),S2'))∧(S1 = S1')∧((IMAGE OUTL P) = (IMAGE OUTL P')))
         |   (INR (INR (E:'eventS))) =>
               (∃Sym1' Sym2'.
                  (rel1 (Sym,(IMAGE OUTL P),S1) (INR E) (Sym1',(IMAGE OUTL P'),S1'))∧(rel2 (Sym,(IMAGE OUTR P),S2) (INR E) (Sym2',(IMAGE OUTR P'),S2'))∧(Sym' = Sym1'∪Sym2'))
       ))`;


       
(* compose transition system *)
val composeOperation_def =
Define`
      (composeOperation ((rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel),(ded1:('pred1) tded)) ((rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel),(ded2:('pred2) tded)) = (composeRel rel1 rel2, composeDed ded1 ded2): ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) transitionsystem)
`;





(* Reach a state *)
val (Reach_rules, Reach_ind, Reach_cases)
= Hol_reln
  `(∀(TrnSys:( 'symb, 'pred, 'state, 'event ) transitionsystem) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Ded: ('pred) tded) (st: 'state) (Ev: 'event) (Conf':(('symb set) # ('pred set) # 'state)).
      ((TrnSys = (Trn,Ded)) ∧ (Conf = ({},{},st)) ∧ (Trn Conf Ev Conf')) ==> (Reach TrnSys Conf)) /\
  (∀(TrnSys:( 'symb, 'pred, 'state, 'event ) transitionsystem) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Ded: ('pred) tded) (Conf:(('symb set) # ('pred set) # 'state)) (Ev: 'event) (Conf':(('symb set) # ('pred set) # 'state)).
     ((TrnSys = (Trn,Ded)) ∧ (Trn Conf Ev Conf') ∧ (Reach TrnSys Conf)) ==> (Reach TrnSys Conf'))
  `;



(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:(('symb set) # ('pred set) # 'state) -> ('event list) -> (('symb set) # ('pred set) # 'state) -> bool``);

(* multi transitions system *)    
val _ = Parse.type_abbrev("multransys", ``:(( 'symb, 'pred, 'state, 'event ) mtrel # ('pred) tded)``);

(* Trace *)
val _ = Parse.type_abbrev("trc", ``:'event list``);  

val (trace_rules, trace_ind, trace_cases)
= Hol_reln
  `(∀(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (Conf:(('symb set) # ('pred set) # 'state)).
      ((MTS = (MTrn,Ded)) ∧ (MTrn Conf [] Conf)) ==> (trace MTS [])) ∧
(∀(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (Conf:(('symb set) # ('pred set) # 'state)) (Evs: 'event list) (Conf':(('symb set) # ('pred set) # 'state)).
   ((MTS = (MTrn,Ded)) ∧ (MTrn Conf Evs Conf')) ==> (trace MTS Evs)) ∧
(∀(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (Conf1:(('symb set) # ('pred set) # 'state)) (Evs: 'event list) (Conf2:(('symb set) # ('pred set) # 'state)) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Conf3:(('symb set) # ('pred set) # 'state)) (Ev: 'event) (MTS':( 'symb, 'pred, 'state, 'event ) multransys) (MTrn':( 'event, 'pred, 'state, 'symb ) mtrel).
   ((MTS = (MTrn,Ded)) ∧ (MTrn Conf1 Evs Conf2) ∧ (Trn Conf2 Ev Conf3) ∧ (MTS' = (MTrn',Ded)) ∧ (MTrn' Conf1 (Ev::Evs) Conf3)) ==> (trace MTS' (Ev::Evs)))
`;


(* Traces *)
val traces_def =
Define`
traces (MTS:( 'symb, 'pred, 'state, 'event ) multransys) = {t| (trace MTS t)}
`;


(* Trace property *)
val traceProperty_def =
Define`
traceProperty (MTS:( 'symb, 'pred, 'state, 'event ) multransys) (Phi:( 'event trc set)) = ((traces MTS) ⊆ Phi)
                                                           `;
val _ = set_mapped_fixity { fixity = Infixl 90,
                            term_name = "apply_traceProperty",
                            tok = "⊨" };

val _ = overload_on ("apply_traceProperty", ``traceProperty``);


(* Trace refinement *)
val traceRefinement_def =
Define`
traceRefinement (MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys) = ((traces MTS1) ⊆ (traces MTS2))
                                                           `;
val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_traceRefinement",
                            tok = "⊑" };

val _ = overload_on ("apply_traceRefinement", ``traceRefinement``);



(* Coinductive simulation *)
val (simulation_rules, simulation_coind, simulation_cases) =
Hol_coreln`
          (∀(MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn1:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded1: ('pred) tded) (Evs: 'event list) (Conf1':(('symb set) # ('pred set) # 'state)) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn2:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded2: ('pred) tded).
             (((MTS1 = (MTrn1,Ded1)) ∧ (MTrn1 Conf1 Evs Conf1')) ⇒ (∃(Conf2':(('symb set) # ('pred set) # 'state)). (MTS2 = (MTrn2,Ded2)) ∧ (MTrn2 Conf2 Evs Conf2') ∧ (simulation (MTS1,Conf1') (MTS2,Conf2')))) ==> (simulation (MTS1,Conf1) (MTS2,Conf2)))  
          `;

val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_simulation",
                            tok = "≲" };

val _ = overload_on ("apply_simulation", ``simulation``);








val _ = export_theory();

(* DB.find_in "SET" (DB.find "SUM_MAP"); *)
(* DB.find "SUM_MAP"; *)
