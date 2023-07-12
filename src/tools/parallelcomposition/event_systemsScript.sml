open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open listTheory;

val _ = new_theory "event_systems";

(* initial *)
val _ = Parse.type_abbrev("init_t", ``:(('symb set) # ('pred set) # 'state) -> bool``);      

(* transition relation *)
val _ = Parse.type_abbrev("relation_t", ``:(('symb set) # ('pred set) # 'state) -> 'event -> (('symb set) # ('pred set) # 'state) -> bool``);    

(* deduction relation *)    
val _ = Parse.type_abbrev("deduction_t", ``:('pred set) -> 'pred -> bool``);


(* transition system *)     
val _ = Datatype `transitionsystem_t = <|
  sys_init   : ( 'pred, 'state, 'symb) init_t;
  sys_trans  : ( 'event, 'pred, 'state, 'symb) relation_t;
  sys_dedu   : ('pred) deduction_t
                         |>`;

(* reach a state *)
Inductive reach:
[~init:]
  (!(ES :('event, 'pred, 'state, 'symb) transitionsystem_t) (v:'symb set) (p: 'pred set) (s: 'state).
        (ES.sys_init (v,p,s)) ==> (reach ES (v,p,s))) /\
[~trans:]
  !(ES :('event, 'pred, 'state, 'symb) transitionsystem_t) v p s e v' p' s'.
      (ES.sys_trans (v,p,s) e (v',p',s')) /\ (reach ES (v,p,s)) ==> (reach ES (v',p',s'))
End

(* invariant of an event system *)
Definition invariant:
  (invariant ES I ⇔ (∀v p s. (reach ES (v,p,s)) ==> I (v,p,s)))
End        


(* trace *)
val _ = Parse.type_abbrev("trace_t", ``:'event list``);
 (*   
Definition trace:
  ((trace ES (v,p,s) [] (v',p',s')) = ((v,p,s) = (v',p',s'))) ∧
  ((trace ES (v,p,s) (e::(t: 'event trace_t)) (v'',p'',s'')) =
         (∀v' p' s'. (trace ES (v,p,s) t (v',p',s')) ∧ (ES.sys_trans (v',p',s') e (v'',p'',s''))))
End
(*
Inductive trace:
[~nil:]
  (!(ES :('event, 'pred, 'state, 'symb) transitionsystem_t) (v:'symb set) (p: 'pred set) (s: 'state).
     (trace ES (v,p,s) [] (v,p,s))) ∧
[~snoc:]
  !(ES :('event, 'pred, 'state, 'symb) transitionsystem_t) v p s.
      (trace ES (v,p,s) (t: 'event trace_t) (v',p',s')) ∧ (ES.sys_trans (v',p',s') e (v'',p'',s'')) ==> (trace ES (v,p,s) (t ⧺ [e]) (v'',p'',s''))
End
*)    

Theorem trace_independence:
 ∀(ES :('event, 'pred, 'state, 'symb) transitionsystem_t) (FS :('event, 'pred, 'state, 'symb) transitionsystem_t) v p s t v' p' s'. (trace ES (v,p,s) t (v',p',s')) ∧ (ES.sys_trans = FS.sys_trans) ⇒ (trace FS (v,p,s) t (v',p',s'))
Proof
  rpt strip_tac >>
Induct_on `t` >>
          asm_rewrite_tac [trace] >>
          gen_tac >>
          asm_rewrite_tac [trace] >>
          rpt strip_tac >>
  PAT_X_ASSUM ``∀v''' p''' s'''. A`` (ASSUME_TAC o (Q.SPECL [`v'''`,`p'''`,`s'''`])) >>
                       METIS_TAC [trace]
              
QED
                                              
Theorem trace_single:
 ∀ES v p s e v' p' s'. (ES.sys_trans (v,p,s) e (v',p',s')) ⇒ (trace ES (v,p,s) [e] (v',p',s'))
Proof
  rpt strip_tac >>
      `[e] = ([] ⧺ [e] ` by (rewrite_tac [APPEND_EQ_SING])
      Cases_on `[e] = ([] ⧺ [e])` 
          rewrite_tac [APPEND_EQ_SING]
      asm_rewrite_tac [trace_nil,trace_snoc]
PAT_X_ASSUM ``∀v p s e v' p' s'. A`` (ASSUME_TAC o (Q.SPECL [`v`,`p`,`s`,`e`,`v'`,`p'`,`s'`]))
                 PAT_X_ASSUM ``∀v0 p0 s0. A`` (ASSUME_TAC o (Q.SPECL [`v0`,`p0`,`s0`]))
                                   rewrite_tac [invariant,reach_trans,reach_init]
                                   rpt gen_tac
                                   IMP_RES_TAC(reach_trans)
                                         IMP_RES_TAC(APPEND_EQ_SING)
                                   PAT_X_ASSUM ``∀v' p' s' e. A`` (ASSUME_TAC o (Q.SPECL [`v'`,`p'`,`s'`,`e`]))
                                                     RES_TAC

                                                     FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [trace_nil,trace_snoc]
                                                     METIS_TAC [trace]
QED*)
        
val _ = export_theory();
