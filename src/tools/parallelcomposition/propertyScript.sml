open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open listTheory;
open parallelcompositionsimpleTheory;
open pairTheory wordsTheory set_sepTheory;
open quantHeuristicsTheory;
val _ = new_theory "property";
    
(* Trace *)
val _ = Parse.type_abbrev("trc", ``:'event list``);  

(* Trace property*)
val traceProperty_def =
Define`
traceProperty (Phi:( 'event trc set)) = {∀t i. ∃j. (t ∈ Phi) ∧ ((TAKE i t) ∈ Phi) ∧ (j < i) ∧ ((TAKE j t) ∈ Phi)}
                                           `;

(* Trace property NOT*)
val tracePropertyNot_def =
Define`
tracePropertyNot (Phi:( 'event trc set)) = {∀t i. ∃j. (t ∉ Phi) ∧ ((TAKE i t) ∉ Phi) ∧ (j < i) ∧ ((TAKE j t) ∈ Phi)}
                                                           `;

val _ = overload_on ("¬", ``tracePropertyNot``);


val evtrace_def =
Define
`
(evtrace (Conf : α) (t:β list) (Conf' : α) (t':β list) = (if (t = []) then ((t' = []) ∧ Conf = Conf') else ((t' = t) ∧ Conf ≠ Conf')))`;
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
      trevtrace MTrn t' = (∀t Conf Conf'. (evtrace Conf t Conf' t') ==> (MTrn Conf t Conf'))
                          `;
val traces_def =
Define`
      traces (MTrn,Ded) =  {t | trevtrace MTrn t}
                           `;

val traces_def =
Define`
      traces (MTrn,_) =  {t | ∀(Conf:β) (Conf':β) e ev. ((MTrn Conf [] Conf') ==> ((t = []) ∧ (Conf = Conf'))) ∧ ((MTrn Conf (e::ev) Conf') ==> ((t = (e::ev)) ∧ (Conf ≠ Conf')))}
                         `;

val traces_def =
Define`
      traces (MTrn,_) =  {t | ∀(Conf:β) (Conf':β) e ev. ((t = []) ==> ((MTrn Conf [] Conf) ∧ ((MTrn Conf [] Conf) = F))) ∧ ((t = (e::ev)) ==> ((MTrn Conf (e::ev) Conf') ∧ ((MTrn Conf (e::ev) Conf') = T))) }
                           `;     

val traces_def =
Define`
      traces (MTrn,_) =  {t | ∀(Conf:β) (Conf':β) e ev. ((t = []) ==> (MTrn Conf [] Conf)) ∧ ((t = (e::ev)) ==> (MTrn Conf (e::ev) Conf')) }
                         `;

                                
val tracesone_def =
Define`
      tracesone Tr C t C' =  {t}
                             `;
                             

                                 val tracestwo_def =
Define`
      tracestwo Re1 Re2 C E C' =  {E}
                             `;




             
val evtrace_def =
Define
`
(evtrace (Conf : α) [e] (Conf' : α) = [e]) ∧
(evtrace Conf (v::Ev) Conf' = (v::(evtrace Conf Ev Conf')))`;

Define
`(trace Conf [e] Conf' = [e]) ∧
(trace Conf (v::Ev) Conf' = (APPEND (trace Conf [v] Conf') (trace Conf Ev Conf')))`;

       
val trace_def =
Define
  `((trace (MTrn,Ded) []) = (∃Conf. (MTrn Conf [] Conf))) ∧
   ((trace (MTrn,Ded) [e]) = (∃Conf Conf'. (MTrn Conf [e] Conf'))) ∧
   ((trace (MTrn',Ded') (Ev::Evs)) = (∃MTrn Mded Trn Ded Conf Conf' Conf''. (trace (Trn,Ded) [Ev]) ∧ (trace (MTrn,Mded) Evs) ∧ (MTrn Conf Evs Conf') ∧ (Trn Conf' [Ev] Conf'') ∧ (MTrn' Conf (Ev::Evs) Conf'')))
`;
        
   
val (trace_rules, trace_ind, trace_cases)
= Hol_reln
  `(((MTS = (MTrn,Ded)) ∧ (MTrn Conf [] Conf)) ==> (trace MTS [])) ∧
(((MTS = (MTrn,Ded)) ∧ (MTrn Conf Evs Conf')) ==> (trace MTS Evs)) ∧
(((MTS = (MTrn,Ded)) ∧ (MTrn Conf Evs Conf') ∧ (Trn Conf' Ev Conf'') ∧ (MTS' = (MTrn',Ded')) ∧ (MTrn' Conf (Ev::Evs) Conf'')) ==> (trace MTS' (Ev::Evs)))
`;
val trevtraces_def =
Define`
trevtrace MTrn t' = (∀t Conf Conf'. (evtrace Conf t Conf' t') ∧ (MTrn Conf t Conf'))
                    `;
val traces_def =
Define`
traces (MTrn,Ded) =  {t | trevtrace MTrn t}
`;

val trevtraces_def =
Define`
trevtrace MTrn t' = (∀t Conf Conf'. (evtrace Conf t Conf' t') ∧ (MTrn Conf t Conf'))
                    `;

                    traces (MTrn,Ded) = {t| ∀(Sym:α) (P: β) (S: γ) (Sym':α) (P': β) (S': γ). (MTrn (Sym,P,S) t (Sym',P',S'))}


val traces_def =
Define`
      traces (MTrn,Ded) = {t| ∀(Sym:α) (P: β) (S: γ) (Sym':α) (P': β) (S': γ). (MTrn (Sym,P,S) t (Sym',P',S'))}
`;
val comptraces_def =
Define`
      comptraces (CMTrn,CDed) = {t| ∀(Sym:α) (P: β) (S1: γ) (S2: δ) (Sym':α) (P': β) (S1': γ) (S2': δ). (CMTrn (Sym,P,S1,S2) t (Sym',P',S1',S2'))}
`;

        val traces_def =
Define`
      traces MTrn (Sym,P,S) t (Sym',P',S') = {t}
`;
              
(* Traces of a system *)
val traces_def =
Define`
      traces (MTrn:('event, 'pred, 'state, 'symb) mtrel) ((Sym:'symb set),(P: 'pred set),(S: 'state)) (t:'event list) ((Sym':'symb set),(P': 'pred set),(S': 'state)) = {t}
                                                                                                                                                                        `;
(* Traces of 2 systems *)
val comptraces_def =
Define`
      comptraces (CMTrn,CDed) = {t| ∀(Sym:α) (P: β) (S1: γ) (S2: δ) (Sym':α) (P': β) (S1': γ) (S2': δ). (CMTrn (Sym,P,S1,S2) t (Sym',P',S1',S2'))}
`;
val traces_def =
Define`
      traces (MTrn,Ded) = {t| ∀Sym P S  Sym' P' S'. (MTrn (Sym,P,S) t (Sym',P',S'))}
                          `;
*)
val traces_def =
Define`
      traces (MTrn:('event, 'pred, 'state, 'symb) mtrel) ((Sym:'symb set),(P: 'pred set),(S: 'state)) ((Sym':'symb set),(P': 'pred set),(S': 'state)) = {t| (MTrn (Sym,P,S) t (Sym',P',S'))}
                                                                                                                                                                        `;
 val comptraces_def =
Define`
      comptraces (CMTrn:((('event1+'eventS) + ('event2 +'eventS)), ('pred1 + 'pred2), 'state1#'state2, 'symb) mtrel) ((Sym:'symb set),(P: ('pred1 + 'pred2) set),(S1: 'state1),(S2: 'state2)) ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) = {t| (CMTrn (Sym,P,S1,S2) t (Sym',P',S1',S2'))}
`;                                                                                                                          (*                                               
val comptraces_def =
Define`
      comptraces (CMTrn,CDed) = {t| ∀Sym P S1 S2 Sym' P' S1' S2'. (CMTrn (Sym,P,S1,S2) t (Sym',P',S1',S2'))}
`;                                                                                                                                                                                

val add_event_to_trace_thm = store_thm(
  "add_event_to_trace_thm", ``
∀MTrn1 Ded1 MTrn2 Ded2 x.
  (∀x. x ∈ traces (MTrn1,Ded1) ⇒ x ∈ traces (MTrn2,Ded2)) ⇒ ∀h. ((h::x) ∈ traces (MTrn1,Ded1) ⇒ (h::x) ∈ traces (MTrn2,Ded2))
  ``,
                                                                                                                             REPEAT GEN_TAC >> strip_tac >> gen_tac >>
  PAT_X_ASSUM ``∀x. A`` (ASSUME_TAC o (Q.SPECL [`h::x`]))>>rw[]
  );
*)

(*

val traces_def =
Define`
      traces (MTrn,Ded) = ∀Sym P S  Sym' P' S'. {t|  (MTrn (Sym,P,S) t (Sym',P',S'))}
`;        
val comptraces_def =
Define`
      comptraces (CMTrn:((('event1+'eventS) + ('event2 +'eventS)), ('pred1 + 'pred2), 'state1#'state2, 'symb) mtrel) ((Sym:'symb set),(P: ('pred1 + 'pred2) set),(S1: 'state1),(S2: 'state2)) (t:(('event1+'eventS) + ('event2 +'eventS)) list)  ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) = {t}
`;
        
val trace_twosystem_thm = store_thm(
  "trace_twosystem_thm", ``
                                ∀MTrn1 Ded1 MTrn2 Ded2.
(traces (MTrn1,Ded1) ⊆ traces (MTrn2,Ded2)) ⇒ (∀x. (x ∈ (traces (MTrn1,Ded1)))⇒(∃y. (y ∈ (traces (MTrn2,Ded2)))∧(x = y)))
                                       ``,
                         REWRITE_TAC [traces_def,SUBSET_DEF]>>
                         ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
  );

val trace_twosystem_thm = store_thm(
  "trace_twosystem_thm", ``
                                ∀MTrn1 Ded1 MTrn2 Ded2.
(traces (MTrn1,Ded1) ⊆ traces (MTrn2,Ded2)) ⇒ (∀(Sym:α) (P: β) (S: γ) (Sym':α) (P': β) (S': γ). ∃t. (MTrn1 (Sym,P,S) t (Sym',P',S')) ⇒ (MTrn2 (Sym,P,S) t (Sym',P',S')))
                                       ``,
                         REWRITE_TAC [traces_def,SUBSET_DEF]>>
                         ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
                                                                                                                               REPEAT GEN_TAC >>
                         REPEAT STRIP_TAC >>
                         Q.EXISTS_TAC `t`
                          PAT_X_ASSUM ``∀x. A`` (ASSUME_TAC o (Q.SPECL [`x`]))>>
                                            Cases_on `MTrn1 = MTrn2` >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
                                            FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
rw[]  );

val comptraces_def =
Define`
 comptraces ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) = {(t:'event list)| ∀(CMTrn:('event, 'pred1 + 'pred2, 'state1 # 'state2, 'symb) mtrel) (Sym:'symb set) (P: ('pred1 + 'pred2) set) (S1: 'state1) (S2: 'state2). (CMTrn (Sym,P,S1,S2) t = (Sym',P',S1',S2'))}
                                                                                           `;

Define`
comptraces ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) =
{(y:'eventS)|
 ∀(MTrn1:(('event1+'eventS), 'pred1, 'state1, 'symb) mtrel) (MTrn2:(('event2+'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym1:'symb set) (P1: 'pred1 set) (S1: 'state1) (Sym2:'symb set) (P2: 'pred2 set) (S2: 'state2).
   (Sym' = FIRST (MTrn1 (Sym1,P1,S1) [INR y]) ∪ FIRST (MTrn2 (Sym2,P2,S2) [INR y])) ∧ (P' = SECOND (MTrn1 (Sym1,P1,S1) [INR y]) ⊔ SECOND (MTrn2 (Sym2,P2,S2) [INR y])) ∧ 
    (S1' =THIRD (MTrn1 (Sym1,P1,S1) [INR y])) ∧ (S2' = THIRD (MTrn2 (Sym2,P2,S2) [INR y]))
}
                                                                                           `;
*)

 (*
val comptraces_def =
Define`
 comptraces ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) = {(t:'event list)| ∀(CMTrn:('event, 'pred1 + 'pred2, 'state1 # 'state2, 'symb) mtrel) (Sym:'symb set) (P: ('pred1 + 'pred2) set) (S1: 'state1) (S2: 'state2). (CMTrn (Sym,P,S1,S2) t = (Sym',P',S1',S2'))}
                                                                                           `;

val same_events_thm = store_thm(
  "same_events_thm", ``
 ∀(y :'eventS) (MTrn1:(('event1+'eventS), 'pred1, 'state1, 'symb) mtrel) (MTrn2:(('event2+'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym1:'symb set) (P1: 'pred1 set) (S1: 'state1) (Sym2:'symb set) (P2: 'pred2 set) (S2: 'state2).                       
comptraces
          (FIRST (MTrn1 (Sym1,P1,S1) [INR y]) ∪
           FIRST (MTrn2 (Sym2,P2,S2) [INR y]),
           SECOND (MTrn1 (Sym1,P1,S1) [INR y]) ⊔
           SECOND (MTrn2 (Sym2,P2,S2) [INR y]),
           THIRD (MTrn1 (Sym1,P1,S1) [INR y]),
           THIRD (MTrn2 (Sym2,P2,S2) [INR y])) = {[y]}``, cheat);
                                                                        
                               
                                val comptraces_def =
Define`
 comptraces ((Sym':'symb set),(P': ('pred1 + 'pred2) set),(S1': 'state1),(S2': 'state2)) = {(t:'event list)| ∀(CMTrn:('event, 'pred1 + 'pred2, 'state1 # 'state2, 'symb) mtrel) (Sym:'symb set) (P: ('pred1 + 'pred2) set) (S1: 'state1) (S2: 'state2). (CMTrn (Sym,P,S1,S2) t = (Sym',P',S1',S2'))}
                                                                                           `;

val same_events_thm = store_thm(
  "same_events_thm", ``
 ∀(y :'eventS) (MTrn1:(('event1+'eventS), 'pred1, 'state1, 'symb) mtrel) (MTrn2:(('event2+'eventS), 'pred2, 'state2, 'symb) mtrel) (Sym1:'symb set) (P1: 'pred1 set) (S1: 'state1) (Sym2:'symb set) (P2: 'pred2 set) (S2: 'state2).                       
comptraces
          (FIRST (MTrn1 (Sym1,P1,S1) [INR y]) ∪
           FIRST (MTrn2 (Sym2,P2,S2) [INR y]),
           SECOND (MTrn1 (Sym1,P1,S1) [INR y]) ⊔
           SECOND (MTrn2 (Sym2,P2,S2) [INR y]),
           THIRD (MTrn1 (Sym1,P1,S1) [INR y]),
           THIRD (MTrn2 (Sym2,P2,S2) [INR y])) = {[y]}``, cheat);
                                                                   
val trace_twosystem_thm = store_thm(
  "trace_twosystem_thm", ``
                                ∀CMTrn1 Ded1 CMTrn2 Ded2.
(comptraces (CMTrn1,Ded1) = comptraces (CMTrn2,Ded2)) ⇒ (∀t (Sym:α) (P: β) (S1: γ) (S2: δ) (Sym':α) (P': β) (S1': γ) (S2': δ). (CMTrn1 (Sym,P,S1,S2) t = (Sym',P',S1',S2')) ∧ (CMTrn2 (Sym,P,S1,S2) t = (Sym',P',S1',S2')))
                                       ``,
                                       REWRITE_TAC [comptraces_def]>>
                                       REWRITE_TAC [SUBSET_DEF]>>
                         ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
                                                                                                                               REPEAT GEN_TAC >>
                         REPEAT STRIP_TAC >>
                         Q.EXISTS_TAC `t`
                          PAT_X_ASSUM ``∀x. A`` (ASSUME_TAC o (Q.SPECL [`x`]))>>
                                         Cases_on `x = t` >>
                                         RES_TAC
                                                EQ_TAC
                                                 PAT_X_ASSUM ``!CMTrn Sym' P' S1' S2. A`` (ASSUME_TAC o (Q.SPECL [`CMTrn`,`Sym'`,`P'`,`S1'`,`S2`]))
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
                                         FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
val SPLIT_ss = REWRITE_TAC [SPLIT_def,SUBSET_DEF,DISJOINT_DEF,DELETE_DEF,IN_INSERT,SEP_EQ_def,
                         EXTENSION,NOT_IN_EMPTY,IN_DEF,IN_UNION,IN_INTER,IN_DIFF];
val SPLIT_TAC = FULL_SIMP_TAC (pure_ss++SPLIT_ss) [] \\ METIS_TAC [];
IMP_RES_TAC EQ_IMP_THM
            IMP_RES_TAC EQ_EXPAND
            PAT_X_ASSUM ``!Sym' Sym S2' S2 S1' S1 P' P. A`` (ASSUME_TAC o (Q.SPECL [`Sym'`,`Sym`,`S2'`,`S2`,`S1'`,`S1`,`P'`,`P`]))>>
            PAT_X_ASSUM ``!Sym P S1 S2 Sym' P' S1' S2'. A`` (ASSUME_TAC o (Q.SPECL [`Sym`,`P`,`S1`,`S2`,`Sym'`,`P'`,`S1'`,`S2'`]))
ASM_REWRITE_TAC[]
               IMP_RES_TAC AND_INTRO_THM
               IMP_RES_TAC F_IMP
                           IMP_RES_TAC EXISTS_NOT_FORALL_THM
                           IMP_RES_TAC PULL_EXISTS

rw[]  );

val subset_comptraces_def =
Define`
      subset_comptraces (CMTrn1,CDed1) (CMTrn2,CDed2) =
((comptraces (CMTrn1,CDed1) = {t1| ∀(Sym1:α) (P1: β) (S11: γ) (S21: δ) (Sym1':α) (P1': β) (S11': γ) (S21': δ). (CMTrn1 (Sym1,P1,S11,S21) t1 (Sym1',P1',S11',S21'))}) ∧
             (comptraces (CMTrn2,CDed2) = {t2| ∀(Sym2:α) (P2: β) (S12: γ) (S22: δ) (Sym2':α) (P2': β) (S12': γ) (S22': δ). (CMTrn2 (Sym2,P2,S12,S22) t2 (Sym2',P2',S12',S22'))}) ∧ (t1 = t2))
                                `;                                
                

val traces_def =
Define`
traces MTS Phi = {t| (trace MTS t) ∧ (t ∈ (tracePropertyNot Phi))}
`;


(* Satisfy Trace property *)
val satisfyTraceProperty_def =
Define`
satisfyTraceProperty MTS Phi = ((traces MTS) ⊆ Phi)
                                                           `;
val _ = set_mapped_fixity { fixity = Infixl 90,
                            term_name = "apply_satisfyTraceProperty",
                            tok = "⊨" };

val _ = overload_on ("apply_satisfyTraceProperty", ``satisfyTraceProperty``);    


(* Trace refinement *)
val traceRefinement_def =
Define`
      traceRefinement MTS1 MTS2 = ((traces MTS1) ⊆ (traces MTS2))
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
  *)
val _ = export_theory();

