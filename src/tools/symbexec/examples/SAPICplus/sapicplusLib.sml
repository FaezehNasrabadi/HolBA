structure sapicplusLib =
struct

local
    open HolKernel Parse;
    open Int intSyntax;
    open String bitstringSyntax stringSyntax;
    val ERR = Feedback.mk_HOL_ERR "sapicplusLib";
in


(* Names *)

val _ = Datatype `NameTag = FreshName | PubName | NodeName`;
    
val _ = Datatype `Name_t = Name NameTag string`;


(* Variables *)
    
val _ = Datatype `LSort =
	 LSortPub
       | LSortFresh
       | LSortMsg
       | LSortNode`;
    
val _ = Datatype `LVar_t = LVar string LSort int`;    


  
(* Function symbols *)
    
val _ = Datatype `ACSym_t = Union | Mult | Xor`;


val _ = Datatype `Privacy_t = Private | Public`;

    
val _ = Datatype `Constructability_t = Constructor | Destructor`;


val _ = Datatype `ipc_t = <| arity:int; privacy:Privacy_t; Constructability:Constructability_t |>`;
    

val _ = Datatype `NoEqSym_t = <|Funname:string; Funsig:ipc_t |>`;


val _ = Datatype `CSym_t = EMap`;
    
  
val _ = Datatype `FunSym_t =
              NoEq  NoEqSym_t
            | AC    ACSym_t
            | C     CSym_t
            | List`;


(* Terms *)
	      
val _ = Datatype `Term_t =
	      Con Name_t
	    | Var LVar_t
	    | FAPP FunSym_t (Term_t list)`;



val _ = Datatype `SapicNTerm_t =
	      Con Name_t
	    | Var 'a
	    | FAPP FunSym_t (SapicNTerm_t list)`;
    
(* Facts *)
    
val _ = Datatype `Multiplicity_t = ReadOnly | Consume`;

    
val _ = Datatype `FactTag_t =
	       ProtoFact Multiplicity_t string int
             | FreshFact
	     | OutFact
             | InFact
             | KUFact
             | KDFact
             | DedFact
             | TermFact`;


val _ = Datatype `FactAnnotation_t = SolveFirst | SolveLast | NoSources`;

    
val _ = Datatype `Fact_t = 
    <| factTag         : FactTag_t;
       factAnnotations : (FactAnnotation_t set);
       factTerms       : (Term_t list)|>`;


val _ = Datatype `LNFact_t = Fact Fact_t`;


val _ = Datatype `NFact_t = 
    <| factTag         : FactTag_t;
       factAnnotations : (FactAnnotation_t set);
       factTerms       : ('a SapicNTerm_t list)|>`;


val _ = Datatype `SapicNFact_t = Fact ('a NFact_t)`;
    

(* Atoms *)


val _ = Datatype `SyntacticSugar_t = Pred ('a SapicNFact_t)`;



val _ = Datatype `ProtoAtom_t = Action ('a SapicNTerm_t) ('a SapicNFact_t)
                 | EqE  ('a SapicNTerm_t) ('a SapicNTerm_t)
                 | Less ('a SapicNTerm_t) ('a SapicNTerm_t)
                 | Last ('a SapicNTerm_t)
                 | Syntactic ('a SyntacticSugar_t)`;
		  
  
(* Formulas *)
    
val _ = Datatype `Connective_t = And | Or | Imp | Iff`;
		  
val _ = Datatype `Quantifier_t = All | Ex`;


val _ = Datatype `Quetuple_t = <|Qname:string; Qsig:LSort |>`;

val _ = Datatype `SapicNFormula_t  = Ato ('a ProtoAtom_t)
                   | TF bool
                   | Not SapicNFormula_t
                   | Conn Connective_t SapicNFormula_t SapicNFormula_t
                   | Qua Quantifier_t Quetuple_t SapicNFormula_t`;


(* Action *)

val _ = Datatype `intuple_t = <|inChan: ('a SapicNTerm_t) option; inMsg: ('a SapicNTerm_t); inMatch: ('a set)|>`;

val _ = Datatype `MSRtuple_t = <|
		  iPrems : ('a SapicNFact_t list);
		  iActs :  ('a SapicNFact_t list);
		  iConcs : ('a SapicNFact_t list);
                  iRest :  ('a SapicNFormula_t list);
                  iMatch : ('a set)|>`;
    
val _ = Datatype `SapicAction_t =
                   Rep
                 | New    'a
                 | ChIn   ('a intuple_t)
                 | ChOut  (('a SapicNTerm_t) option) ('a SapicNTerm_t)
                 | Insert ('a SapicNTerm_t) ('a SapicNTerm_t)
                 | Delete ('a SapicNTerm_t)
                 | Lock   ('a SapicNTerm_t)
                 | Unlock ('a SapicNTerm_t)
                 | Event  ('a SapicNTerm_t)
                 | MSR    ('a MSRtuple_t)`;   

(* Processes *)

val _ = Datatype `lettuple_t = <|letLeft: ('a SapicNTerm_t); letRight: ('a SapicNTerm_t); letMatch: ('a set)|>`;

    
val _ = Datatype `ProcessCombinator_t =
		   Parallel | NDC | Cond ('a SapicNFormula_t)
		 | CondEq ('a SapicNTerm_t) ('a SapicNTerm_t)
		 | Lookup ('a SapicNTerm_t) 'a
		 | Let    ('a lettuple_t)
		 | ProcessCall string ('a SapicNTerm_t list)`;

(* Process with annotations

val _ = Datatype `Process_t =
        ProcessNull 'ann
    |   ProcessComb ('a ProcessCombinator_t) 'ann (Process_t) (Process_t)
    |   ProcessAction ('a SapicAction_t) 'ann (Process_t)`;

*)

(* Process without annotations *)
    
val _ = Datatype `Process_t =
        ProcessNull
    |   ProcessComb ('a ProcessCombinator_t) (Process_t) (Process_t)
    |   ProcessAction ('a SapicAction_t) (Process_t)`;    











    
end (* local *)
end (* struct *)
