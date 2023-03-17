open HolKernel Parse boolLib bossLib;
open bagTheory;

val _ = new_theory "sapicplus";

(* Sapicplus Syntax *)
    
(* Names *)
    
val _ = Datatype `NameTag_t = FreshName | PubName | NodeName`;    


val _ = Datatype `Name_t = Name NameTag_t string`;


(* Variables*)

val _ = Datatype `Var_t = Var string int`;
    
    
(* Function symbols *)


val _ = Datatype `Privacy_t = Private | Public`;

    
val _ = Datatype `Constructability_t = Constructor | Destructor`;



(* Terms *)
	      

val _ = Datatype `SapicTerm_t =
	      Con   Name_t
	    | TVar  Var_t
	    | FAPP  (string # (int # Privacy_t # Constructability_t)) (SapicTerm_t list)`;



(* Detect ground term *)
val is_ground_term_def = Define `
                                is_ground_term t =
(case t of
   (Con _) => T
 | (TVar _) => F
 | (FAPP _ _) => F)
`;


(* Subset SapicTerm *)
(*TODO*)
val sapic_subst_def = Define`
                            (sapic_subst x y t = (if x = t then y else
                                                    (case t of
                                                       (FAPP n ts) => (FAPP n (MAP (sapic_subst x y) ts))
                                                     | _ => x)
                                                 ))
                            `;       


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


(* Processes *)
    
val _ = Datatype `ProcessCombinator_t =
		   Parallel
		 | NDC
		 | CondEq       SapicTerm_t SapicTerm_t
		 | Lookup       SapicTerm_t Var_t
		 | Let          SapicTerm_t SapicTerm_t
		 | ProcessCall  string (SapicTerm_t list)`;



val _ = Datatype `Process_t =
        ProcessNull
    |   ProcessComb    ProcessCombinator_t Process_t Process_t
    |   ProcessAction  SapicAction_t Process_t`;        


(* Substitution *)
    
val _ = Datatype `sapic_substitution_t =
   Substitution (Var_t -> (SapicTerm_t option))
`;    


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
   LTS (sapic_configuration_t -> (SapicFact_t option)  -> sapic_configuration_t -> bool)
       `;

        
(* Multi Labeled Transition System *)      

val _ = Datatype `sapic_mlts_t =
   MLTS (sapic_configuration_t -> ((SapicFact_t option) list) -> sapic_configuration_t -> bool)
       `;
       


(* Sapic Semantics*)

(* Null rule *)

val sapic_null_transition_def = Define `
                                  sapic_null_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps.
   (Pold = (BAG_UNION Ps {|ProcessNull|})) /\
   (Pnew = Ps) /\
   (Ev = NONE) /\
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
   (Ev = NONE) /\
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
   (Ev = NONE) /\
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
   (Ev = SOME Fc) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;

                
(* Conditional true rule *)

val sapic_conditional_true_transition_def = Define `
                                  sapic_conditional_true_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessComb (CondEq t1 t2) P Q|})) /\
   (t1 = t2) /\
   (Pnew = (BAG_UNION Ps {|P|})) /\
   (Ev = NONE) /\
   (Ns = Ns') /\
   (St = St') /\
   (Sb = Sb') /\
   (Al = Al'))`;
                                

(* Conditional false rule *)

val sapic_conditional_false_transition_def = Define `
                                  sapic_conditional_false_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P Q t1 t2.
   (Pold = (BAG_UNION Ps {|ProcessComb (CondEq t1 t2) P Q|})) /\
   (t1 ≠ t2) /\
   (Pnew = (BAG_UNION Ps {|Q|})) /\
   (Ev = NONE) /\
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
   (Ev = NONE) /\
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
   (Ev = NONE) /\
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
   (Ev = NONE) /\
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
   (Ev = NONE) /\
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
   (Ev = NONE) /\
   (Ns = Ns') /\
   (St = State S) ∧
   (t = t') ∧
   (S t' = NONE) ∧
   (St = St') /\
   (Sb = Sb') /\
   (Al' = Al))`;


(* New rule *)
(*TODO*)
val sapic_new_transition_def = Define `
                                  sapic_new_transition (Config (Ns,St,Pold,Sb,Al)) Ev (Config (Ns',St',Pnew,Sb',Al')) =
(∃Ps P N N' n'.
   (Pold = (BAG_UNION Ps {|ProcessAction (New N) P|})) /\
   (Pnew = (BAG_UNION Ps {|subst[N |-> N'] P|})) /\
   (Ev = NONE) /\
   (N' = Name FreshName n') /\
   (Ns' = (N' INSERT Ns)) /\
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
                                    (sapic_delete_transition C Ev C') ∨
                                    (sapic_insert_transition C Ev C') ∨
                                    (sapic_lock_transition C Ev C') ∨
                                    (sapic_unlock_transition C Ev C') ∨
                                    (sapic_lookup_false_transition C Ev C')
                                    ))`;
                
(* Detect a silent transition *)
   
val is_a_silent_transition_def = Define `
is_a_silent_transition (Config (Ns,St,Ps,Sb,Al)) Ev (Config (Ns',St',Ps',Sb',Al')) =
(case Ev of
   (SOME Fc) => F
 | (NONE)    => T)
`;



val _ = export_theory();
