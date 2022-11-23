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

(* Pattern *)

datatype 'a SapicPattern_t =  PatternBind of 'a | PatternMatch of 'a;
	 
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
                 | Event  of ('a SapicNFact_t)
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



fun ACSym_to_string tag = case tag of
      Mult  => "*"
    | Union => "+"
    | Xor   => "⊕";

fun FunSym_to_string tag = case tag of
              (NoEq (bs , _)) => bs
            | (AC Op)         => (ACSym_to_string Op)
            | (C Op)          => "EMap"
            | List            => "List";
	 
fun SapicNTerm_to_string tag = case tag of
       Con n        => (Name_to_string n)
   |   Var v        => v
   |   FAPP (f,[t]) => (FunSym_to_string f) ^ "(" ^ (SapicNTerm_to_string t)^ ")"
   |   FAPP (f,n)   => (FunSym_to_string f) ^ "(" ^((SapicNTerm_to_string (hd n))^(List.foldr (fn (x,s) => s ^","^ (SapicNTerm_to_string x) ^ "") "" (tl n)) ^ "")^ ")";

    
    
(*
val b = FAPP(List,[Var "v",Var "n"]);

SapicNTerm_to_string b
 *)


fun FactTag_to_string tag = case tag of
     KUFact            => "KU"
 |   KDFact            => "KD"
 |   DedFact           => "Ded"
 |   InFact            => "In"
 |   OutFact           => "Out"
 |   FreshFact         => "Fr"
 |   TermFact          => "Term"
 |  (ProtoFact (_ , n , _)) => n;
    

fun Multiplicity_to_string tag = case tag of
     Consume            => ""
 |   ReadOnly           => "!";


fun FactAnnotation_to_string tag = case tag of
      SolveFirst     => "+"
    | SolveLast      => "-"
    | NoSources      => "no_precomp";


fun Fact_to_string (Fact tag) =
    (FactTag_to_string (#factTag tag)) ^ "(" ^
    ((SapicNTerm_to_string (hd (#factTerms tag)))^
    (List.foldr (fn (x,s) => s ^","^ (SapicNTerm_to_string x) ^ "") "" (tl (#factTerms tag))) ^ "")^ ")";


    
fun SapicPattern_to_string tag =  case tag of
    (PatternBind v) => v
  | (PatternMatch v) => "="^v;    



fun SapicRule_to_string (MSR tag) =
    "[" ^
    ((Fact_to_string (hd (#iPrems tag)))^
     (List.foldr (fn (x,s) => s ^","^ (Fact_to_string x) ^ "") "" (tl (#iPrems tag))) ^ "")^ "]--[" ^
    ((Fact_to_string (hd (#iActs tag)))^
     (List.foldr (fn (x,s) => s ^","^ (Fact_to_string x) ^ "") "" (tl (#iActs tag))) ^ "")^ "]->[" ^
    ((Fact_to_string (hd (#iConcs tag)))^
    (List.foldr (fn (x,s) => s ^","^ (Fact_to_string x) ^ "") "" (tl (#iConcs tag))) ^ "")^ "]";
    
fun SapicAction_to_string tag = case tag of
                   Rep     => "!"
                 | (New n) => "new "^n
                 | (Insert (t1,t2)) => "insert "^(SapicNTerm_to_string t1)^","^(SapicNTerm_to_string t2)
                 | (Delete t) => "delete "^(SapicNTerm_to_string t)
                 | (Lock t)   => "lock "^(SapicNTerm_to_string t)
		 | (Unlock t) => "unlock "^(SapicNTerm_to_string t)
                 | (Event a)  => "event "^(Fact_to_string a)	   
                 | (ChOut (NONE , t2))     => "out("^(SapicNTerm_to_string t2)^")"
                 | (ChOut (SOME(t1) , t2)) => "out("^(SapicNTerm_to_string t1)^","^(SapicNTerm_to_string t2)^")"
                 | (ChIn {inChan = NONE, inMsg = t, inMatch = _})       => "in("^(SapicNTerm_to_string t)^")"
                 | (ChIn {inChan = (SOME t1), inMsg = t2, inMatch = _}) => "in("^(SapicNTerm_to_string t1)^","^(SapicNTerm_to_string t2)^")"
                 | (MSR r) =>  (SapicRule_to_string (MSR r));   

    
(*
val b = FAPP(NoEq("pair",(2,Public,Constructor)),[Var "v",Var "n"]);

SapicAction_to_string (Lock b)
 *)


fun Connective_to_string tag =
    case tag of
	And => "&&"
      | Or  => "||"
      | Imp => "==>"
      | Iff => "<=>";
		  
fun Quantifier_to_string tag =
    case tag of
	All => "∀"
      | Ex  => "∃";


fun SapicNFormula_to_string  tag =
    case tag of
        (TF T)  => "⊤"
      | (TF F)  => "⊥"
      | (Not f) => "¬"^(SapicNFormula_to_string f)
      | (Conn (Op,p,q)) => ((SapicNFormula_to_string p)^(Connective_to_string Op)^(SapicNFormula_to_string q))
      | _ => "";


 
fun ProcessCombinator_to_string tag =
    case tag of
	Parallel => "|"
      | NDC      => "+"
      | (Cond f) => "if "^(SapicNFormula_to_string f)
      | (CondEq (t1,t2)) => "if "^(SapicNTerm_to_string t1)^"="^(SapicNTerm_to_string t2)
      | (Lookup (t,v))   => "lookup "^(SapicNTerm_to_string t)^" as "^v
      | (Let {letLeft = t1, letRight = t2, letMatch = _}) => "let "^(SapicNTerm_to_string t1)^"="^(SapicNTerm_to_string t2)
      | (ProcessCall (v,ts)) => (v^"("^((SapicNTerm_to_string (hd ts))^
				       (List.foldr (fn (x,s) => s ^","^ (SapicNTerm_to_string x) ^ "") "" (tl ts)) ^ "")^")");


(*
val b = [FAPP(NoEq("pair",(2,Public,Constructor)),[Var "v",Var "n"]),Var "m"];

ProcessCombinator_to_string (ProcessCall ("test",b))
 *)



fun Process_to_string tag =
    case tag of
	ProcessNull => "0"
      | (ProcessComb ((ProcessCall (v,ts)), _ , _)) => (ProcessCombinator_to_string (ProcessCall (v,ts))) 
      | (ProcessComb (c,pl,pr)) =>  ((Process_to_string pl)^(ProcessCombinator_to_string c)^(Process_to_string pr))
      | (ProcessAction (Rep,p)) => ((SapicAction_to_string Rep)^(Process_to_string p))
      | (ProcessAction (a,ProcessNull)) => (SapicAction_to_string a)
      | (ProcessAction (a,p)) => ((SapicAction_to_string a)^(Process_to_string p));

(*
val b = [FAPP(NoEq("pair",(2,Public,Constructor)),[Var "v",Var "n"]),Var "m"];

Process_to_string (ProcessComb ((ProcessCall ("test",b)),ProcessNull,ProcessNull))

val c = FAPP(NoEq("pair",(2,Public,Constructor)),[Var "v",Var "n"]);

Process_to_string (ProcessAction ((Delete c),ProcessNull))


Process_to_string (ProcessComb ((Parallel),(ProcessAction ((Delete c),ProcessNull)),(ProcessAction ((Lock c),ProcessNull))))
 *)

	 
    
end (* local *)
end (* struct *)
