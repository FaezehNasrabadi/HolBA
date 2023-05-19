open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

val _ = new_theory "property";
    
(* Trace *)
val _ = Parse.type_abbrev("trc", ``:'event list``);  

val (trace_rules, trace_ind, trace_cases)
= Hol_reln
  `(((MTS = (MTrn,Ded)) ∧ (MTrn Conf [] Conf)) ==> (trace MTS [])) ∧
(((MTS = (MTrn,Ded)) ∧ (MTrn Conf Evs Conf')) ==> (trace MTS Evs)) ∧
(((MTS = (MTrn,Ded)) ∧ (MTrn Conf Evs Conf') ∧ (Trn Conf' Ev Conf'') ∧ (MTS' = (MTrn',Ded')) ∧ (MTrn' Conf (Ev::Evs) Conf'')) ==> (trace MTS' (Ev::Evs)))
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
traces MTS Phi = {t| (trace MTS t) ∧ (t ∈ (tracePropertyNot Phi))}
`;


(* Satisfy Trace property *)
val satisfyTraceProperty_def =
Define`
satisfyTraceProperty MTS Phi = ((traces MTS Phi) ⊆ Phi)
                                                           `;
val _ = set_mapped_fixity { fixity = Infixl 90,
                            term_name = "apply_satisfyTraceProperty",
                            tok = "⊨" };

val _ = overload_on ("apply_satisfyTraceProperty", ``satisfyTraceProperty``);    


(* Trace refinement *)
val traceRefinement_def =
Define`
      traceRefinement MTS1 MTS2 = (∀Phi. ((traces MTS1 Phi) ⊆ (traces MTS2 Phi)))
                                                                                                                              `;
val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_traceRefinement",
                            tok = "⊑" };

val _ = overload_on ("apply_traceRefinement", ``traceRefinement``);


(* Inductive state simulation *)
val (stateSimulation_rules, stateSimulation_ind, stateSimulation_cases) =
Hol_reln`
        ((((MTS1 = (MTrn1,Ded1)) ∧ (MTrn1 Conf1 Evs Conf1')) ⇒ (∃(Conf2':(('symb set) # ('pred set) # 'state)). (MTS2 = (MTrn2,Ded2)) ∧ (MTrn2 Conf2 Evs Conf2') ∧ (stateSimulation (MTS1,Conf1) (MTS2,Conf2)))) ==> (stateSimulation (MTS1,Conf1') (MTS2,Conf2'))) ∧
((((MTS1 = (MTrn1,Ded1)) ∧ (MTrn1 ({},{},st01) Evs Conf1)) ⇒ (∃(Conf2:(('symb set) # ('pred set) # 'state)). (MTS2 = (MTrn2,Ded2)) ∧ (MTrn2 ({},{},st02) Evs Conf2) ∧ (stateSimulation (MTS1,({},{},st01)) (MTS2,({},{},st02))))) ==> (stateSimulation (MTS1,Conf1) (MTS2,Conf2))) 
`;

val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_stateSimulation",
                            tok = "≼" };

val _ = overload_on ("apply_stateSimulation", ``stateSimulation``);


(* Simulation *)
val (simulation_rules, simulation_ind, simulation_cases) =
Hol_reln`
          ((stateSimulation (MTS1,({},{},st01)) (MTS2,({},{},st02))) ==> (simulation MTS1 MTS2))  
          `;
    
val _ = set_mapped_fixity { fixity = Infixl 95,
                            term_name = "apply_simulation",
                            tok = "≲" };

val _ = overload_on ("apply_simulation", ``simulation``);



(* Reach a state *)
val (Reach_rules, Reach_ind, Reach_cases)
= Hol_reln
  `(((TrnSys = (Trn,Ded)) ∧ (Conf = ({},{},st0)) ∧ (Trn Conf Ev Conf')) ==> (Reach TrnSys Conf)) ∧
(((TrnSys = (Trn,Ded)) ∧ (Trn Conf Ev Conf') ∧ (Reach TrnSys Conf)) ==> (Reach TrnSys Conf'))
`;

 (*
val sim_vs_ref_thm = store_thm(
  "sim_vs_ref_thm", ``!(MTS1:((α -> bool) # (β -> bool) # γ ->
                              δ list -> (α -> bool) # (β -> bool) # γ -> bool) # ε) (MTS2:((α -> bool) # (β -> bool) # γ ->
                                                                                           δ list -> (α -> bool) # (β -> bool) # γ -> bool) # ε).
                       (MTS1 ≲ MTS2) ==> (MTS1 ⊑ MTS2) ``
  ,
  
  REPEAT GEN_TAC >>        
  REWRITE_TAC [simulation_cases]>>
  STRIP_TAC >>
  REWRITE_TAC [traceRefinement_def,traces_def,trace_cases]>>
  STRIP_TAC >>          
  Cases_on `MTS1 = MTS2`  >| [
  ALL_TAC
  ,
      ASM_SIMP_TAC (std_ss++pred_setSimps.PRED_SET_ss) []
    ] >>
  REWRITE_TAC [tracePropertyNot_def]>>
  METIS_TAC [Reach_rules, Reach_ind, Reach_cases,stateSimulation_rules, stateSimulation_ind, stateSimulation_cases]
  );
WIP on the proof-no cheat but METIS_TAC could not find proof *)
  
val _ = export_theory();

