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
	      

(*TODO: Syntax of process calculus of sapic+ *)

    
end (* local *)
end (* struct *)
