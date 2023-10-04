open HolKernel Parse boolLib bossLib;
open bagTheory;
open messagesTheory;
(*  HOL_Interactive.toggle_quietdec(); *)
(* open Option; *)
(*  HOL_Interactive.toggle_quietdec(); *)
val _ = new_theory "sapicplus";

(* Sapicplus Syntax *)
                                             
(* Facts *)
    
val _ = Datatype `FactTag_t =
	      FreshFact  
            | OutFact   
            | InFact     
            | KUFact     
            | KDFact     
            | DedFact  
            | TermFact`;

	      
val _ = Datatype `SapicFact_t = Fact FactTag_t (SapicTerm_t list)`;


val sapicFact_substname_def = Define`
                                (sapicFact_substname x y (Fact tag ts) = (Fact tag (MAP (sapic_substname x y) ts)))`;

val sapicFact_substvar_def = Define`
                                (sapicFact_substvar x y (Fact tag ts) = (Fact tag (MAP (sapic_substvar x y) ts)))`;                                        
                                        
(* Action *)
    
val _ = Datatype `SapicAction_t =
                   Rep
                 | New     Name_t
                 | ChIn    (SapicTerm_t option) SapicTerm_t
                 | ChOut   (SapicTerm_t option) SapicTerm_t
                 | Event   SapicFact_t
                 | Insert  SapicTerm_t SapicTerm_t
		 | Delete  SapicTerm_t
		 | Lock    SapicTerm_t
		 | Unlock  SapicTerm_t`;


               
val sapicAction_substname_def =
Define`
      (sapicAction_substname x y a = (case a of
                                        (Rep) => Rep
                                      | (New n) => New (messages$name_subst x y n)
                                      | (ChIn (SOME t1) t2) => ChIn (SOME (sapic_substname x y t1)) (sapic_substname x y t2)
                                      | (ChOut (SOME t1) t2) => ChOut (SOME (sapic_substname x y t1)) (sapic_substname x y t2)
                                      | (ChIn (NONE) t) => ChIn NONE (sapic_substname x y t)
                                      | (ChOut (NONE) t) => ChOut NONE (sapic_substname x y t)
                                      | (Event f) => Event (sapicFact_substname x y f)
                                      | (Insert t1 t2) => Insert (sapic_substname x y t1) (sapic_substname x y t2)
		                      | (Delete t) => Delete (sapic_substname x y t)
		                      | (Lock t) => Lock (sapic_substname x y t)
		                      | (Unlock t) => Unlock (sapic_substname x y t)
                                     ))`;
                                   
                                                                      
val sapicAction_substvar_def =
Define`
      (sapicAction_substvar x y a = (case a of
                                        (Rep) => Rep
                                      | (New n) => New n
                                      | (ChIn (SOME t1) t2) => ChIn (SOME (sapic_substvar x y t1)) (sapic_substvar x y t2)
                                      | (ChOut (SOME t1) t2) => ChOut (SOME (sapic_substvar x y t1)) (sapic_substvar x y t2)
                                      | (ChIn (NONE) t) => ChIn NONE (sapic_substvar x y t)
                                      | (ChOut (NONE) t) => ChOut NONE (sapic_substvar x y t)
                                      | (Event f) => Event (sapicFact_substvar x y f)
                                      | (Insert t1 t2) => Insert (sapic_substvar x y t1) (sapic_substvar x y t2)
		                      | (Delete t) => Delete (sapic_substvar x y t)
		                      | (Lock t) => Lock (sapic_substvar x y t)
		                      | (Unlock t) => Unlock (sapic_substvar x y t)
                                     ))`;
                                
(* Processes *)
    
val _ = Datatype `ProcessCombinator_t =
		   Parallel
		 | NDC
		 | CondEq       SapicTerm_t SapicTerm_t
                 | Cond         SapicTerm_t
		 | Lookup       SapicTerm_t Var_t
		 | Let          SapicTerm_t SapicTerm_t
		 | ProcessCall  string (SapicTerm_t list)`;



val processCombinator_substname_def =
Define`
      (processCombinator_substname x y c = (case c of
                                              Parallel           => Parallel
		                            | NDC                => NDC
		                            | (CondEq t1 t2)     => CondEq (sapic_substname x y t1) (sapic_substname x y t2)
                                            | (Cond t)           => Cond (sapic_substname x y t)
		                            | (Lookup t v)       => Lookup (sapic_substname x y t) v
		                            | (Let t1 t2)        => Let (sapic_substname x y t1) (sapic_substname x y t2)
		                            | (ProcessCall s ts) => ProcessCall s (MAP (sapic_substname x y) ts)
 ))`;

val processCombinator_substvar_def =
Define`
      (processCombinator_substvar x y c = (case c of
                                              Parallel           => Parallel
		                            | NDC                => NDC
		                            | (CondEq t1 t2)     => CondEq (sapic_substvar x y t1) (sapic_substvar x y t2)
                                            | (Cond t)           => Cond (sapic_substvar x y t)
		                            | (Lookup t v)       => Lookup (sapic_substvar x y t) (var_subst x y v)
		                            | (Let t1 t2)        => Let (sapic_substvar x y t1) (sapic_substvar x y t2)
		                            | (ProcessCall s ts) => ProcessCall s (MAP (sapic_substvar x y) ts)
                                           ))`;
                                           
        
val _ = Datatype `Process_t =
        ProcessNull
    |   ProcessComb    ProcessCombinator_t Process_t Process_t
    |   ProcessAction  SapicAction_t Process_t`;        


val process_substname_def =
Define`
      (process_substname x y p = (case p of
                                    ProcessNull           => ProcessNull
                                  |   (ProcessComb c p1 p2) => ProcessComb (processCombinator_substname x y c) (process_substname x y p1) (process_substname x y p2)
                                  |   (ProcessAction  a p')  => ProcessAction (sapicAction_substname x y a) (process_substname x y p')
                                                                              
                                 ))`;

val process_substvar_def =
Define`
      (process_substvar x y p = (case p of
                                    ProcessNull           => ProcessNull
                                  |   (ProcessComb c p1 p2) => ProcessComb (processCombinator_substvar x y c) (process_substvar x y p1) (process_substvar x y p2)
                                  |   (ProcessAction  a p')  => ProcessAction (sapicAction_substvar x y a) (process_substvar x y p')
                                                                              
                                 ))`;
                                 
(* Substitution *)
    
val _ = Datatype `sapic_substitution_t =
   Substitution (Var_t -> (SapicTerm_t option))
`;    


val sapic_substitution_dom_def = Define `
    sapic_substitution_dom (Substitution S) = {vars | S vars <> NONE}
                                         `;

val substitvn_to_term_def =
Define`
      (substitvn_to_term (Substitution S) (Con n)  = (Con n)) ∧
      (substitvn_to_term (Substitution S) (TVar v) = (if (v ∈ sapic_substitution_dom (Substitution S)) then (THE (S v)) else (TVar v)))`;


val substitfun_to_term_def =
Define`
      (substitfun_to_term (Substitution S) (FAPP n' ts) = (FAPP n' (MAP (substitvn_to_term (Substitution S)) ts)))`;

      
val substitution_to_term_def = Define`
                                (substitution_to_term (Substitution S) t = (case t of
(FAPP n ts) => substitfun_to_term (Substitution S) (FAPP n ts)
| _ =>  substitvn_to_term (Substitution S) _                                                            
))
                                `;
(*                                
val substitution_to_term_defn = Defn.Hol_defn
  "substitution_to_term"
  ‘(substitution_to_term (Substitution S) t = (case t of
                                                       (Con n) => (Con n)
| (TVar v) => (if (v ∈ sapic_substitution_dom (Substitution S)) then (THE (S v)) else (TVar v))
| (FAPP n' ts) => (FAPP n' (MAP (substitution_to_term (Substitution S)) ts))                          
                                                 ))’;

val (substitution_to_term_EQN, substitution_to_term_IND) =
 Defn.tprove (substitution_to_term_defn, cheat);
*)   
    
(* State *)
    
val _ = Datatype `sapic_state_t =
   State (SapicTerm_t -> (SapicTerm_t option))
`;       
      

(* Configuration *)
    
val _ = Datatype `sapic_configuration_t =
   Config ((Name_t set) # sapic_state_t # (Process_t multiset) # sapic_substitution_t # (SapicTerm_t set))
`;       
      


(* Labeled Transition System *)      

val _ = Datatype `sapic_lts_t =
   LTS (sapic_configuration_t -> (SapicFact_t list)  -> sapic_configuration_t -> bool)
       `;


(* Sapic Semantics*)

(* Null rule *)

val sapic_null_transition_def = Define `
                                  sapic_null_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps.
   (Pold = (BAG_UNION Ps {|ProcessNull|})) /\
   (Pnew = Ps) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;                        


(* Parallel rule *)

val sapic_parallel_transition_def = Define `
                                  sapic_parallel_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q.
   (Pold = (BAG_UNION Ps {|ProcessComb Parallel P Q|})) /\
   (Pnew = (BAG_UNION (BAG_UNION Ps {|P|}) {|Q|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;

                
(* Replication rule *)

val sapic_replication_transition_def = Define `
                                  sapic_replication_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P.
   (Pold = (BAG_UNION Ps {|ProcessAction Rep P|})) /\
   (Pnew = (BAG_UNION (BAG_UNION Ps {|P|}) {|ProcessAction Rep P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;
                
(* Event rule *)

val sapic_event_transition_def = Define `
                                  sapic_event_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Fc.
   (Pold = (BAG_UNION Ps {|ProcessAction (Event Fc) P|})) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = [Fc]) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;


val _ = Theory.new_constant("termholds", ``:SapicTerm_t -> bool``);

(* Conditional true rule *)

val sapic_conditional_true_transition_def = Define `
                                  sapic_conditional_true_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t.
   (Pold = (BAG_UNION Ps {|ProcessComb (Cond t) P Q|})) /\
   (termholds t) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;
                                

(* Conditional false rule *)

val sapic_conditional_false_transition_def = Define `
                                  sapic_conditional_false_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t.
   (Pold = (BAG_UNION Ps {|ProcessComb (Cond t) P Q|})) /\
   (¬(termholds t)) /\
   (Pnew = (BAG_UNION Ps {|Q|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`; 
                
(* Conditional eq true rule *)

val sapic_conditional_eq_true_transition_def = Define `
                                  sapic_conditional_eq_true_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessComb (CondEq t1 t2) P Q|})) /\
   (t1 = t2) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;
                                

(* Conditional eq false rule *)

val sapic_conditional_eq_false_transition_def = Define `
                                  sapic_conditional_eq_false_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessComb (CondEq t1 t2) P Q|})) /\
   (t1 ≠ t2) /\
   (Pnew = (BAG_UNION Ps {|Q|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;                                        


(* Delete rule *)

val sapic_delete_transition_def = Define `
                                  sapic_delete_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P S t.
   (Pold = (BAG_UNION Ps {|ProcessAction (Delete t) P|})) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = State S) /\
   (St' = State ((t =+ NONE) S)) /\
   (Sb = Sb') /\
   (Al = Al'))`;

                
(* Insert rule *)

val sapic_insert_transition_def = Define `
                                  sapic_insert_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P S t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessAction (Insert t1 t2) P|})) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = State S) /\
   (St' = State ((t1 =+ SOME t2) S)) /\
   (Sb = Sb') /\
   (Al = Al'))`;


(* Lock rule *)

val sapic_lock_transition_def = Define `
                                  sapic_lock_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P t.
   (Pold = (BAG_UNION Ps {|ProcessAction (Lock t) P|})) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (t NOTIN Al) /\
   (Al' = (t INSERT Al) ))`;



(* Unlock rule *)

val sapic_unlock_transition_def = Define `
                                  sapic_unlock_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∀t'.∃Ps P t.
   (Pold = (BAG_UNION Ps {|ProcessAction (Unlock t) P|})) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (t = t') ∧
   (Al' = (Al DELETE t') ))`;                                



(* Lookup false rule *)

val sapic_lookup_false_transition_def = Define `
                                  sapic_lookup_false_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∀t'.∃Ps P Q S t x.
   (Pold = (BAG_UNION Ps {|ProcessComb (Lookup t x) P Q|})) /\
   (Pnew = (BAG_UNION Ps {|Q|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = State S) ∧
   (t = t') ∧
   (S t' = NONE) ∧
   (St = St') /\
   (Sb = Sb') /\
   (Al' = Al))`;

                
(* Lookup true rule *)

val sapic_lookup_true_transition_def = Define `
                                  sapic_lookup_true_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q S t t' u x.
   (Pold = (BAG_UNION Ps {|ProcessComb (Lookup t x) P Q|})) /\
   (Pnew = (BAG_UNION Ps {|(process_substvar x u P)|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = State S) ∧
   (t = t') ∧
   (S t' = (SOME u)) ∧
   (St = St') /\
   (Sb = Sb') /\
   (Al' = Al))`;

                
(* New rule *)
val sapic_new_transition_def = Define `
                                  sapic_new_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P N N' n'.
   (Pold = (BAG_UNION Ps {|ProcessAction (New N) P|})) /\
   (Pnew = (BAG_UNION Ps {|(process_substname N (Con N') P)|})) /\
   (Ev = []) /\
   (N' = Name FreshName n') /\
   (Ns' = (N' INSERT Ns)) /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;   


(* K rule *)
val sapic_K_transition_def = Define `
                                  sapic_K_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃R t.
   (Pold = Pnew) /\
   (t = substitution_to_term Sb R) /\
   (Ev = [(Fact KUFact [t])]) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;

                
(* In rule *)
val sapic_in_transition_def = Define `
                                  sapic_in_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P t x R R'.
   (Pold = (BAG_UNION Ps {|ProcessAction (ChIn (SOME t) (TVar x)) P|})) /\
   (Pnew = (BAG_UNION Ps {|(process_substvar x (substitution_to_term Sb R') P)|})) /\
   (Ev = [(Fact InFact [R;R']);(Fact KUFact [t;(substitution_to_term Sb R')])]) /\
   (is_ground_term (substitution_to_term Sb R')) /\
   (t = (substitution_to_term Sb R)) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;   

                   
(* Out rule *)

val sapic_out_transition_def = Define `
                                      sapic_out_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P t1 t2 n R S.
   (Pold = (BAG_UNION Ps {|ProcessAction (ChOut (SOME t1) t2) P|})) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = [(Fact OutFact [R]);(Fact KUFact [t1])]) /\
   (is_ground_term t2) /\
   (t1 = (substitution_to_term Sb R)) /\
   (n = (((int_of_num o list$LENGTH o list$SET_TO_LIST o sapic_substitution_dom) Sb)+1)) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Substitution S) /\
   (Sb' = Substitution (((Var "att" n) =+ (SOME t2)) S)) /\
   (Al = Al'))`; 


(* Out-In rule *)
val sapic_out_in_transition_def = Define `
                                  sapic_out_in_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P t t1 t2 x.
   (Pold = (BAG_UNION Ps {|ProcessAction (ChOut (SOME t1) t2) (ProcessAction (ChIn (SOME t) (TVar x)) P)|})) /\
   (Pnew = (BAG_UNION Ps {|(process_substvar x t2 P)|})) /\
   (Ev = []) /\
   (is_ground_term t2) /\
   (t = t1) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;


(* Let true rule *)

val sapic_let_true_transition_def = Define `
                                  sapic_let_true_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessComb (Let t1 t2) P Q|})) /\
   (t1 = t2) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;
                                

(* Let false rule *)

val sapic_let_false_transition_def = Define `
                                  sapic_let_false_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessComb (Let t1 t2) P Q|})) /\
   (t1 ≠ t2) /\
   (Pnew = (BAG_UNION Ps {|Q|})) /\
   (Ev = []) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`; 


                 
(* Transition relation *)

val sapic_transition_def = Define `
                                  (sapic_transition C Ev C' = (
                                    (sapic_null_transition C Ev C') ∨
                                    (sapic_event_transition C Ev C') ∨
                                    (sapic_parallel_transition C Ev C') ∨
                                    (sapic_replication_transition C Ev C') ∨
                                    (sapic_conditional_true_transition C Ev C') ∨
                                    (sapic_conditional_false_transition C Ev C') ∨
                                    (sapic_conditional_eq_true_transition C Ev C') ∨
                                    (sapic_conditional_eq_false_transition C Ev C') ∨
                                    (sapic_let_true_transition C Ev C') ∨
                                    (sapic_let_false_transition C Ev C') ∨
                                    (sapic_delete_transition C Ev C') ∨
                                    (sapic_insert_transition C Ev C') ∨
                                    (sapic_lock_transition C Ev C') ∨
                                    (sapic_unlock_transition C Ev C') ∨
                                    (sapic_lookup_false_transition C Ev C') ∨
                                    (sapic_lookup_true_transition C Ev C') ∨
                                    (sapic_new_transition C Ev C') ∨
                                    (sapic_K_transition C Ev C') ∨
                                    (sapic_in_transition C Ev C') ∨
                                    (sapic_out_in_transition C Ev C') ∨
                                    (sapic_out_transition C Ev C')    
                                    ))`;
                
(* Detect a silent transition *)
   
val is_a_silent_transition_def = Define `
is_a_silent_transition (Config (Ns,St,Ps,Sb,Al)) Ev (Config (Ns',St',Ps',Sb',Al')) =
(case Ev of
   [] => T
 | _  => F)
`;



val _ = export_theory();
