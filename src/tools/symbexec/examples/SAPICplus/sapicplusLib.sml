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


  
(* Function symbols *)


datatype Privacy_t = Private | Public;

    
datatype Constructability_t = Constructor | Destructor;
   

type FunSym_t = (string * (int * Privacy_t * Constructability_t));


(* Terms *)
	      

datatype 'a SapicNTerm_t =
	      Con  of Name_t
	    | Var  of 'a
	    | FAPP of (FunSym_t * ('a SapicNTerm_t list));
    
(* Facts *)


datatype 'a SapicNFact_t =
	 Fact of {
       factTag         : (string * int),
       factTerms       : ('a SapicNTerm_t list)};
    
	 
(* Action *)

    
datatype 'a SapicAction_t =
                   Rep
                 | New    of 'a
                 | ChIn   of (('a SapicNTerm_t) option) * ('a SapicNTerm_t)
                 | ChOut  of (('a SapicNTerm_t) option) * ('a SapicNTerm_t)
                 | Event  of ('a SapicNFact_t);
                    

(* Processes *)

    
datatype 'a ProcessCombinator_t =
		   Parallel 
		 | CondEq of ('a SapicNTerm_t) * ('a SapicNTerm_t)	
		 | Let    of ('a SapicNTerm_t) * ('a SapicNTerm_t)


datatype 'a Process_t =
        ProcessNull
    |   ProcessComb   of ('a ProcessCombinator_t) * ('a Process_t) * ('a Process_t)
    |   ProcessAction of ('a SapicAction_t) * ('a Process_t);    




(* Translate to string by show functions *)

fun Name_to_string (Name (FreshName , n)) = "~'" ^ n ^ "'"
  | Name_to_string (Name (PubName , n))   = "'" ^ n ^ "'"
  | Name_to_string (Name (NodeName , n))  = "#'" ^ n ^ "'";




fun SapicNTerm_to_string tag = case tag of
       Con n        => (Name_to_string n)
   |   Var v        => v
   |   FAPP ((bs , _),[t]) => (bs) ^ "(" ^ (SapicNTerm_to_string t)^ ")"
   |   FAPP ((bs , _),n)   => (bs) ^ "(" ^((SapicNTerm_to_string (hd n))^(List.foldr (fn (x,s) => s ^","^ (SapicNTerm_to_string x) ^ "") "" (tl n)) ^ "")^ ")";

    
    
(*
val b = FAPP(("pair",(2,Public,Constructor)),[Var "v",Var "n"]);

SapicNTerm_to_string b
 *)


fun Fact_to_string (Fact tag) =
    (fst (#factTag tag)) ^ "(" ^
    ((SapicNTerm_to_string (hd (#factTerms tag)))^
    (List.foldr (fn (x,s) => s ^","^ (SapicNTerm_to_string x) ^ "") "" (tl (#factTerms tag))) ^ "")^ ")";



fun SapicAction_to_string tag = case tag of
                   Rep     => "!"
                 | (New n) => "new "^n
                 | (Event a)  => "event "^(Fact_to_string a)	   
                 | (ChOut (NONE , t))      => "out("^(SapicNTerm_to_string t)^")"
                 | (ChOut (SOME(t1) , t2)) => "out("^(SapicNTerm_to_string t1)^","^(SapicNTerm_to_string t2)^")"
                 | (ChIn  (NONE, t))        => "in("^(SapicNTerm_to_string t)^")"
                 | (ChIn  (SOME(t1) , t2)) => "in("^(SapicNTerm_to_string t1)^","^(SapicNTerm_to_string t2)^")";
         

    
(*
val b = ChOut(SOME(Var "c"),FAPP(("pair",(2,Public,Constructor)),[Var "v",Var "n"]));

SapicAction_to_string (b)
 *)



 
fun ProcessCombinator_to_string tag =
    case tag of
	Parallel => "|"
      | (CondEq (t1,t2)) => "if "^(SapicNTerm_to_string t1)^"="^(SapicNTerm_to_string t2)
      | (Let (t1,t2)) => "let "^(SapicNTerm_to_string t1)^"="^(SapicNTerm_to_string t2);


(*
val b = (FAPP(("pair",(2,Public,Constructor)),[Var "v",Var "n"]),Var "m");

ProcessCombinator_to_string (CondEq b)
 *)



fun Process_to_string tag =
    case tag of
	ProcessNull => "0"
      | (ProcessComb (Parallel,pl,pr)) =>  ((Process_to_string pl)^(ProcessCombinator_to_string Parallel)^(Process_to_string pr))
      | (ProcessComb ((CondEq (t1,t2)),pl,pr)) =>  ((ProcessCombinator_to_string (CondEq (t1,t2)))^" then "^(Process_to_string pl)^" else "^(Process_to_string pr))
      | (ProcessComb ((Let p),pl,pr)) =>  ((ProcessCombinator_to_string (Let p))^" in "^(Process_to_string pl)^" else "^(Process_to_string pr))
      | (ProcessAction (Rep,p)) => ((SapicAction_to_string Rep)^(Process_to_string p))
      | (ProcessAction (a,ProcessNull)) => (SapicAction_to_string a)
      | (ProcessAction (a,p)) => ((SapicAction_to_string a)^(Process_to_string p));

(*
val b = (FAPP(("pair",(2,Public,Constructor)),[Var "v",Var "n"]),Var "m");

Process_to_string (ProcessComb ((CondEq b),ProcessNull,ProcessNull))

val c = ChOut(SOME(Var "c"),FAPP(("pair",(2,Public,Constructor)),[Var "v",Var "n"]));

Process_to_string (ProcessAction ((c),ProcessNull))


Process_to_string (ProcessComb ((Parallel),(ProcessAction (( c),ProcessNull)),(ProcessComb ((CondEq b),ProcessNull,ProcessNull))))
 *)

fun SAPIC_to_file str =
    let
	val SFile = TextIO.openAppend "SAIC_Translation.txt";
	    
    in
	(TextIO.output (SFile, str); TextIO.flushOut SFile)
    end;	 
    
end (* local *)
end (* struct *)
