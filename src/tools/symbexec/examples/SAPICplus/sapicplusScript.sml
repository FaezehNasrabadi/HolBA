open HolKernel Parse boolLib bossLib;


val _ = new_theory "sapicplus";

(* sapicplus syntax *)
    
(* Names *)
    
val _ = Datatype `NameTag_t = FreshName | PubName | NodeName`;    


val _ = Datatype `Name_t = Name NameTag_t string`;


(* Variables*)

val _ = Datatype `Var_t = Var 'a int`;
    
    
(* Function symbols *)


val _ = Datatype `Privacy_t = Private | Public`;

    
val _ = Datatype `Constructability_t = Constructor | Destructor`;



(* Terms *)
	      

val _ = Datatype `SapicTerm_t =
	      Con   Name_t
	    | TVar   ('a Var_t)
	    | FAPP (string # (int # Privacy_t # Constructability_t)) (SapicTerm_t list)`;

(*
val test_def = Define `
    test = FAPP ("pair",(2,Public,Constructor)) [Var "b"] : string SapicNTerm_t`;
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

	      
val _ = Datatype `SapicFact_t = Fact FactTag_t ('a SapicTerm_t list)`;

    
(* Action *)
    
val _ = Datatype `SapicAction_t =
                   Rep
                 | New     'a
                 | ChIn    (('a SapicTerm_t) option) ('a SapicTerm_t)
                 | ChOut   (('a SapicTerm_t) option) ('a SapicTerm_t)
                 | Event   ('a SapicFact_t)
                 | Insert  ('a SapicTerm_t) ('a SapicTerm_t)
		 | Delete  ('a SapicTerm_t)
		 | Lock    ('a SapicTerm_t)
		 | Unlock  ('a SapicTerm_t)`;


(* Processes *)
    
val _ = Datatype `ProcessCombinator_t =
		   Parallel
		 | NDC
		 | CondEq       ('a SapicTerm_t) ('a SapicTerm_t)
		 | Lookup       ('a SapicTerm_t) 'a
		 | Let          ('a SapicTerm_t) ('a SapicTerm_t)
		 | ProcessCall  string ('a SapicTerm_t list)`;



val _ = Datatype `Process_t =
        ProcessNull
    |   ProcessComb    ('a ProcessCombinator_t) (Process_t) (Process_t)
    |   ProcessAction  ('a SapicAction_t) (Process_t)`;        


(* sapicplus semantics *)
    
val _ = Datatype `sapic_substitution_t =
   Substitution (('a Var_t) -> ('a SapicTerm_t) option)
`;    
    
