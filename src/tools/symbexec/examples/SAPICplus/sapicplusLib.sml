structure sapicplusLib =
struct

local
    open HolKernel Parse;
    open Int intSyntax;
    open String bitstringSyntax stringSyntax;
    val ERR = Feedback.mk_HOL_ERR "sapicplusLib";
in


(* Names *)

datatype NameTag = FreshName | PubName | NodeName;
    
datatype Name_t =
	 Name of ( NameTag * string);



(* Variables *)
    
datatype LSort =
	 LSortPub
       | LSortFresh
       | LSortMsg
       | LSortNode;
    
datatype LVar_t = LVar of (string * LSort * int);    


  
(* Function symbols *)
    
datatype ACSym_t = Union | Mult | Xor;


datatype Privacy_t = Private | Public;

    
datatype Constructability_t = Constructor | Destructor;
   

type NoEqSym_t = (string * (int * Privacy_t * Constructability_t));


datatype CSym_t = EMap;
    
  
datatype FunSym_t =
              NoEq  of NoEqSym_t
            | AC    of ACSym_t
            | C     of CSym_t
            | List;


(* Terms *)
	      
datatype Term_t =
	      Con  of Name_t
	    | Var  of LVar_t
	    | FAPP of (FunSym_t * (Term_t list));


datatype 'a SapicNTerm_t =
	      Con  of Name_t
	    | Var  of 'a
	    | FAPP of (FunSym_t * ('a SapicNTerm_t list));
    
(* Facts *)
    
datatype Multiplicity_t = ReadOnly | Consume;

    
datatype FactTag_t =
	       ProtoFact of (Multiplicity_t * string * int)
             | FreshFact
	     | OutFact
             | InFact
             | KUFact
             | KDFact
             | DedFact
             | TermFact;


datatype FactAnnotation_t = SolveFirst | SolveLast | NoSources;

    
datatype Fact_t =
	 Fact of {
       factTag         : FactTag_t,
       factAnnotations : (FactAnnotation_t set),
       factTerms       : (Term_t list)
};



datatype 'a SapicNFact_t =
	 Fact of {
       factTag         : FactTag_t,
       factAnnotations : (FactAnnotation_t set),
       factTerms       : ('a SapicNTerm_t list)};
    

(* Atoms *)


datatype 'a SyntacticSugar_t = Pred of ('a SapicNFact_t);



datatype 'a ProtoAtom_t = Action of ('a SapicNTerm_t)*('a SapicNFact_t)
                 | EqE  of ('a SapicNTerm_t)*('a SapicNTerm_t)
                 | Less of ('a SapicNTerm_t)*('a SapicNTerm_t)
                 | Last of ('a SapicNTerm_t)
                 | Syntactic of ('a SyntacticSugar_t);
		  
  
(* Formulas *)
    
datatype Connective_t = And | Or | Imp | Iff;
		  
datatype Quantifier_t = All | Ex;


datatype 'a SapicNFormula_t  = Ato of ('a ProtoAtom_t)
                   | TF of bool
                   | Not of ('a SapicNFormula_t)
                   | Conn of Connective_t * ('a SapicNFormula_t) * ('a SapicNFormula_t)
                   | Qua of Quantifier_t * (string * LSort) * ('a SapicNFormula_t);


(* Action *)

    
datatype 'a SapicAction_t =
                   Rep
                 | New    of 'a
                 | ChIn   of { inChan: ('a SapicNTerm_t) option, inMsg: ('a SapicNTerm_t), inMatch: ('a set)}
                 | ChOut  of (('a SapicNTerm_t) option) * ('a SapicNTerm_t)
                 | Insert of ('a SapicNTerm_t) * ('a SapicNTerm_t)
                 | Delete of ('a SapicNTerm_t)
                 | Lock   of ('a SapicNTerm_t)
                 | Unlock of ('a SapicNTerm_t)
                 | Event  of ('a SapicNTerm_t)
                 | MSR    of {
		  iPrems : ('a SapicNFact_t list),
		  iActs :  ('a SapicNFact_t list),
		  iConcs : ('a SapicNFact_t list),
                  iRest :  ('a SapicNFormula_t list),
                  iMatch : ('a set)};   

(* Processes *)

    
datatype 'a ProcessCombinator_t =
		   Parallel | NDC | Cond of ('a SapicNFormula_t)
		 | CondEq of ('a SapicNTerm_t) * ('a SapicNTerm_t)
		 | Lookup of ('a SapicNTerm_t) * 'a
		 | Let    of {letLeft: ('a SapicNTerm_t), letRight: ('a SapicNTerm_t), letMatch: ('a set)}
		 | ProcessCall of string * ('a SapicNTerm_t list);

(* Process with annotations

val _ = Datatype `Process_t =
        ProcessNull 'ann
    |   ProcessComb ('a ProcessCombinator_t) 'ann (Process_t) (Process_t)
    |   ProcessAction ('a SapicAction_t) 'ann (Process_t)`;

*)

(* Process without annotations *)
    
datatype 'a Process_t =
        ProcessNull
    |   ProcessComb   of ('a ProcessCombinator_t) * ('a Process_t) * ('a Process_t)
    |   ProcessAction of ('a SapicAction_t) * ('a Process_t);    




(* Translate to string by show functions *)

fun Name_to_string (Name (FreshName , n)) = "~'" ^ n ^ "'"
  | Name_to_string (Name (PubName , n))   = "'" ^ n ^ "'"
  | Name_to_string (Name (NodeName , n))  = "#'" ^ n ^ "'";




    
end (* local *)
end (* struct *)
