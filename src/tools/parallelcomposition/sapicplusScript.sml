open HolKernel Parse boolLib bossLib;


val _ = new_theory "sapicplus";

(* sapicplus syntax *)
    
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

(*
val test_def = Define `
    test = Con (Name FreshName "b") : SapicTerm_t`;
*)


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
                 | Event   SapicTerm_t
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


(* substitution function *)
    
val _ = Datatype `sapic_substitution_t =
   Substitution (Var_t -> (SapicTerm_t option))
`;    


      


val _ = export_theory();
