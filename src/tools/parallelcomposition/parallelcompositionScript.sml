open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

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
val _ = Parse.type_abbrev("ctded", ``:('pred1) tded -> ('pred2) tded -> ('pred1 + 'pred2) tded``);

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
  `(∀(TrnSys:( 'symb, 'pred, 'state, 'event ) transitionsystem) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Ded: ('pred) tded) (st0: 'state) (Ev: 'event) (Conf':(('symb set) # ('pred set) # 'state)).
      ((TrnSys = (Trn,Ded)) ∧ (Conf = ({},{},st0)) ∧ (Trn Conf Ev Conf')) ==> (Reach TrnSys Conf)) /\
  (∀(TrnSys:( 'symb, 'pred, 'state, 'event ) transitionsystem) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Ded: ('pred) tded) (Conf:(('symb set) # ('pred set) # 'state)) (Ev: 'event) (Conf':(('symb set) # ('pred set) # 'state)).
     ((TrnSys = (Trn,Ded)) ∧ (Trn Conf Ev Conf') ∧ (Reach TrnSys Conf)) ==> (Reach TrnSys Conf'))
  `;



(* multi transitions relation *)
val _ = Parse.type_abbrev("mtrel", ``:(('symb set) # ('pred set) # 'state) -> ('event list) -> (('symb set) # ('pred set) # 'state) -> bool``);

(* multi transitions system *)    
val _ = Parse.type_abbrev("multransys", ``:(( 'symb, 'pred, 'state, 'event ) mtrel # ('pred) tded)``);


(* compose multi transition relation *)
val _ = Parse.type_abbrev("cmtrel", ``:('symb, 'pred1, 'state1, 'event1 + 'eventS) mtrel ->
  ('symb, 'pred2, 'state2, 'event2 + 'eventS) mtrel -> 
  ('symb, 'pred1 + 'pred2, 'state1 # 'state2, (('event1+'eventS) + ('event2 +'eventS))) mtrel``);

val (composeMuRe_rules, composeMuRe_ind, composeMuRe_cases)
= Hol_reln
  `(∀(Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Conf:(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (e:(('event1 + 'eventS) + ('event2 + 'eventS))) (rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel) (rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel) (Conf':(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Sym:'symb set) (P:('pred1 + 'pred2) set) (S1:'state1) (S2:'state2) (Sym':'symb set) (P':('pred1 + 'pred2) set) (S1':'state1) (S2':'state2).
      ((composeRel rel1 rel2 Conf e Conf') ∧ (Conf = (Sym,P,S1,S2)) ∧ (Conf' = (Sym',P',S1',S2')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧ (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL [e]) (Sym',(IMAGE OUTL P'),S1')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR [e]) (Sym',(IMAGE OUTR P'),S2'))) ==> (composeMuRe Re1 Re2 Conf [e] Conf')) ∧
(∀(Re1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (Conf:(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (e:(('event1 + 'eventS) + ('event2 + 'eventS))) (rel1:(('event1 + 'eventS), 'pred1, 'state1, 'symb) trel) (rel2:(('event2 + 'eventS), 'pred2, 'state2, 'symb) trel) (Conf':(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Sym:'symb set) (P:('pred1 + 'pred2) set) (S1:'state1) (S2:'state2) (Sym':'symb set) (P':('pred1 + 'pred2) set) (S1':'state1) (S2':'state2) (Re1':(('event1 + 'eventS), 'pred1, 'state1, 'symb) mtrel) (Re2':(('event2 + 'eventS), 'pred2, 'state2, 'symb) mtrel) (ev:(('event1 + 'eventS) + ('event2 + 'eventS)) list) (Evs:(('event1 + 'eventS) + ('event2 + 'eventS)) list) (Conf'':(('symb set) # (('pred1 + 'pred2) set) # 'state1 # 'state2)) (Sym'':'symb set) (P'':('pred1 + 'pred2) set) (S1'':'state1) (S2'':'state2).
   ((Evs = (e::ev)) ∧ (composeRel rel1 rel2 Conf e Conf') ∧ (Conf = (Sym,P,S1,S2)) ∧ (Conf' = (Sym',P',S1',S2')) ∧ (Conf'' = (Sym'',P'',S1'',S2'')) ∧ (rel1 (Sym,(IMAGE OUTL P),S1) (OUTL e) (Sym',(IMAGE OUTL P'),S1')) ∧ (Re1 (Sym,(IMAGE OUTL P),S1) (MAP OUTL Evs) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (rel2 (Sym,(IMAGE OUTR P),S2) (OUTR e) (Sym',(IMAGE OUTR P'),S2')) ∧ (Re2 (Sym,(IMAGE OUTR P),S2) (MAP OUTR Evs) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re2' (Sym',(IMAGE OUTR P'),S2') (MAP OUTR ev) (Sym'',(IMAGE OUTR P''),S2'')) ∧ (Re1' (Sym',(IMAGE OUTL P'),S1') (MAP OUTL ev) (Sym'',(IMAGE OUTL P''),S1'')) ∧ (composeMuRe Re1' Re2' Conf' ev Conf'')) ==> (composeMuRe Re1 Re2 Conf Evs Conf''))     
`; 

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

    
(* Trace *)
val _ = Parse.type_abbrev("trc", ``:'event list``);  

val (trace_rules, trace_ind, trace_cases)
= Hol_reln
  `(∀(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (st0: 'state).
      ((MTS = (MTrn,Ded)) ∧ (MTrn ({},{},st0) [] ({},{},st0))) ==> (trace MTS [])) ∧
(∀(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (st0: 'state) (Evs: 'event list) (Conf:(('symb set) # ('pred set) # 'state)).
   ((MTS = (MTrn,Ded)) ∧ (MTrn ({},{},st0) Evs Conf)) ==> (trace MTS Evs)) ∧
(∀(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (st0: 'state) (Evs: 'event list) (Conf:(('symb set) # ('pred set) # 'state)) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Conf':(('symb set) # ('pred set) # 'state)) (Ev: 'event) (MTS':( 'symb, 'pred, 'state, 'event ) multransys) (MTrn':( 'event, 'pred, 'state, 'symb ) mtrel) (Ded': ('pred) tded).
   ((MTS = (MTrn,Ded)) ∧ (MTrn ({},{},st0) Evs Conf) ∧ (Trn Conf Ev Conf') ∧ (MTS' = (MTrn',Ded')) ∧ (MTrn' ({},{},st0) (Ev::Evs) Conf')) ==> (trace MTS' (Ev::Evs)))
`;


(* Trace property NOT*)
val tracePropertyNot_def =
Define`
tracePropertyNot (Phi:( 'event trc set)) = {t|(t ∉ Phi) ∧ (TL(t) ∈ Phi)}
                                                           `;

val _ = overload_on ("¬", ``tracePropertyNot``);

(* Traces *)
val traces_def =
Define`
traces (MTS:( 'symb, 'pred, 'state, 'event ) multransys) (Phi:( 'event trc set)) = {t| (trace MTS t) ∧ (t ∈ (tracePropertyNot Phi))}
`;


(* Satisfy Trace property *)
val satisfyTraceProperty_def =
Define`
satisfyTraceProperty (MTS:( 'symb, 'pred, 'state, 'event ) multransys) (Phi:( 'event trc set)) = ((traces MTS Phi) ⊆ Phi)
                                                           `;
val _ = set_mapped_fixity { fixity = Infixl 90,
                            term_name = "apply_satisfyTraceProperty",
                            tok = "⊨" };

val _ = overload_on ("apply_satisfyTraceProperty", ``satisfyTraceProperty``);    


(* Trace refinement *)
val traceRefinement_def =
Define`
      traceRefinement (MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys) = (∀(Phi:( 'event trc set)). ((traces MTS1 Phi) ⊆ (traces MTS2 Phi)))
                                                                                                                              `;
val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_traceRefinement",
                            tok = "≼" };

val _ = overload_on ("apply_traceRefinement", ``traceRefinement``);


(* Compose Trace *)  

val (composeTrace_rules, composeTrace_ind, composeTrace_cases)
= Hol_reln
  `(∀(MTS:( 'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) MulComOpr) (MTrn:( 'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) cmtrel) (Ded: ('pred) tded) (st0: 'state).
      ((MTS = (MTrn,Ded)) ∧ (MTrn ({},{},st0) [] ({},{},st0))) ==> (composeTrace MTS [])) ∧
(∀(MTS:( 'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) MulComOpr) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (st0: 'state) (Evs: 'event list) (Conf:(('symb set) # ('pred set) # 'state)).
   ((MTS = (MTrn,Ded)) ∧ (MTrn ({},{},st0) Evs Conf)) ==> (composeTrace MTS Evs)) ∧
(∀(MTS:( 'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) MulComOpr) (MTrn:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded: ('pred) tded) (st0: 'state) (Evs: 'event list) (Conf:(('symb set) # ('pred set) # 'state)) (Trn:( 'event, 'pred, 'state, 'symb ) trel) (Conf':(('symb set) # ('pred set) # 'state)) (Ev: 'event) (MTS':( 'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) MulComOpr) (MTrn':( 'event, 'pred, 'state, 'symb ) mtrel) (Ded': ('pred) tded).
   ((MTS = (MTrn,Ded)) ∧ (MTrn ({},{},st0) Evs Conf) ∧ (Trn Conf Ev Conf') ∧ (MTS' = (MTrn',Ded')) ∧ (MTrn' ({},{},st0) (Ev::Evs) Conf')) ==> (composeTrace MTS' (Ev::Evs)))
`;
    
(* Compose Trace refinement *)
val composeTraceRefinement_def =
Define`
      composeTraceRefinement (CMTS1:( 'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) MulComOpr) (CMTS2:(  'symb, 'pred1, 'pred2, 'state1, 'state2, 'event1, 'event2, 'eventS) MulComOpr) = (∀(Phi:((('event1+'eventS) + ('event2 +'eventS)) trc set)). ((traces CMTS1 Phi) ⊆ (traces CMTS2 Phi)))
                                                                                                                              `;
val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_composeTraceRefinement",
                            tok = "⊑" };

val _ = overload_on ("apply_composeTraceRefinement", ``composeTraceRefinement``);

(* Inductive state simulation *)
val (stateSimulation_rules, stateSimulation_ind, stateSimulation_cases) =
Hol_reln`
          (∀(MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn1:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded1: ('pred) tded) (Evs: 'event list) (Conf1:(('symb set) # ('pred set) # 'state)) (Conf1':(('symb set) # ('pred set) # 'state)) (Conf2:(('symb set) # ('pred set) # 'state)) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn2:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded2: ('pred) tded).
             (((MTS1 = (MTrn1,Ded1)) ∧ (MTrn1 Conf1 Evs Conf1')) ⇒ (∃(Conf2':(('symb set) # ('pred set) # 'state)). (MTS2 = (MTrn2,Ded2)) ∧ (MTrn2 Conf2 Evs Conf2') ∧ (stateSimulation (MTS1,Conf1) (MTS2,Conf2)))) ==> (stateSimulation (MTS1,Conf1') (MTS2,Conf2'))) ∧
              (∀(MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn1:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded1: ('pred) tded) (Evs: 'event list) (Conf1:(('symb set) # ('pred set) # 'state)) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys) (MTrn2:( 'event, 'pred, 'state, 'symb ) mtrel) (Ded2: ('pred) tded) (st01: 'state) (st02: 'state).
             (((MTS1 = (MTrn1,Ded1)) ∧ (MTrn1 ({},{},st01) Evs Conf1)) ⇒ (∃(Conf2:(('symb set) # ('pred set) # 'state)). (MTS2 = (MTrn2,Ded2)) ∧ (MTrn2 ({},{},st02) Evs Conf2) ∧ (stateSimulation (MTS1,({},{},st01)) (MTS2,({},{},st02))))) ==> (stateSimulation (MTS1,Conf1) (MTS2,Conf2))) 
          `;

(* val _ = set_mapped_fixity { fixity = Infixl 95, *)
(*                             term_name = "apply_stateSimulation", *)
(*                             tok = "" }; *)

(* val _ = overload_on ("apply_stateSimulation", ``stateSimulation``); *)


(* Simulation *)
val (simulation_rules, simulation_ind, simulation_cases) =
Hol_reln`
          (∀(MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys) (st01: 'state) (st02: 'state).
             (stateSimulation (MTS1,({},{},st01)) (MTS2,({},{},st02))) ==> (simulation MTS1 MTS2))  
          `;
    
val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_simulation",
                            tok = "≲" };

val _ = overload_on ("apply_simulation", ``simulation``);




val comp_vs_mts_thm = store_thm(
  "comp_vs_mts_thm", ``
                    !(MTS:( 'symb, 'pred, 'state, 'event ) multransys) (MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys).
                      (MTS1 ≼ MTS2) ==>
                      ((MTS1 || MTS) ⊑ (MTS2 || MTS)) ``
  ,
  
  REPEAT GEN_TAC >>        
  REWRITE_TAC [simulation_cases]>>
  STRIP_TAC >>
  REWRITE_TAC [traceRefinement_def,traces_def,trace_cases]>>
  Cases_on `MTS1 = MTS2`  >| [
      ALL_TAC
      ,
      ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    ] >>
  METIS_TAC [stateSimulation_rules, stateSimulation_ind, stateSimulation_cases]
  );




(*
val sim_vs_ref_thm = store_thm(
  "sim_vs_ref_thm", ``
                    !(MTS1:( 'symb, 'pred, 'state, 'event ) multransys) (MTS2:( 'symb, 'pred, 'state, 'event ) multransys).
                      (MTS1 ≲ MTS2) ==>
                      (MTS1 ≼ MTS2) ``
  ,
  
  REPEAT GEN_TAC >>        
  REWRITE_TAC [simulation_cases]>>
  STRIP_TAC >>
  REWRITE_TAC [traceRefinement_def,traces_def,trace_cases]>>
  Cases_on `MTS1 = MTS2`  >| [
      ALL_TAC
      ,
      ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    ] >>
  METIS_TAC [stateSimulation_rules, stateSimulation_ind, stateSimulation_cases]
  );
 WIP on the proof-no cheat but METIS_TAC could not find proof *)
  
val _ = export_theory();

(* DB.find_in "SET" (DB.find "SUM_MAP"); *)
(* DB.find "SET_CASES_TAC"; *)
