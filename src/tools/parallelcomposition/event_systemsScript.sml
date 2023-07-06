open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;

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

(*
Theorem Invariant_rule:
 ∀I ES. (∀v0 p0 s0. (ES.sys_init (v0,p0,s0)) ⇒ I (v0,p0,s0)) ∧ (∀v p s e v' p' s'. (ES.sys_trans (v,p,s) e (v',p',s')) /\ (reach ES (v,p,s)) ∧ (I (v,p,s)) ⇒ I (v',p',s')) ⇒ invariant ES I
Proof
  rewrite_tac [invariant] >> rpt strip_tac >> ...
PAT_X_ASSUM ``∀v p s e v' p' s'. A`` (ASSUME_TAC o (Q.SPECL [`v`,`p`,`s`,`e`,`v'`,`p'`,`s'`]))
                 PAT_X_ASSUM ``∀v0 p0 s0. A`` (ASSUME_TAC o (Q.SPECL [`v0`,`p0`,`s0`]))
                                   rewrite_tac [invariant,reach_trans,reach_init]
                                   rpt gen_tac
                                   IMP_RES_TAC(reach_trans)
                                         IMP_RES_TAC(reach_init)
                                   PAT_X_ASSUM ``∀v' p' s' e. A`` (ASSUME_TAC o (Q.SPECL [`v'`,`p'`,`s'`,`e`]))
                                                        RES_TAC
QED
*)
        
val _ = export_theory();
