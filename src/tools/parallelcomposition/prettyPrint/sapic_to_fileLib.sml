structure sapic_to_fileLib =
struct

local

    open HolKernel Parse
    open sapicplusTheory;
    open sapicplusSyntax;
    open messagesTheory;
    open messagesSyntax;

    val ERR = mk_HOL_ERR "sapic_to_fileLib";
    val wrap_exn = Feedback.wrap_exn "sapic_to_fileLib";
end

(* print Name

val N = “Name FreshName "OTP"”*)

fun name_to_string N =
    let
	val (tag,str) = dest_Name N;
    in
	if (is_FreshName tag)
	then ("~'" ^ (stringSyntax.fromHOLstring str) ^ "'")
	else if (is_PubName tag)
	then ("'"  ^ (stringSyntax.fromHOLstring str) ^ "'")
	else if (is_NodeName tag)
	then ("#'" ^ (stringSyntax.fromHOLstring str) ^ "'")
	else raise ERR "name_to_string" ("Don't know Sapic Name: " ^ (term_to_string N))
    end;

(* print Var

val V = “Var "X" 0”;*)		 

fun var_to_string V =
    let
	val (str,id) = dest_Var V;
    in
	(stringSyntax.fromHOLstring str)
    end;

(* print Term

val trm = “FAPP ("conc",2,Public,Constructor) [TVar (Var "OTP1" 0);TVar (Var "OTP2" 0)]”;*)	
fun term_to_name trm =
    if (is_TVar trm)
    then ((var_to_string o dest_TVar) trm)
    else if (is_Con trm)
    then ((name_to_string  o dest_Con) trm)
    else if (is_FAPP trm)
    then
	let
	    val (fun_sig,fun_vals) = dest_FAPP trm;
	    val (trm_list,_) = listSyntax.dest_list fun_vals;
	    val name = (stringSyntax.fromHOLstring o hd o pairSyntax.strip_pair) fun_sig;
	in
	    (name ^ "(" ^ ((term_to_name (hd trm_list))^(List.foldr (fn (x,s) => s ^ (term_to_name x)) "," (tl trm_list)) ^ ")"))	   
	end	
    else raise ERR "term_to_name" ("Don't know Sapic Term: " ^ (term_to_string trm))



(*
 HOL_Interactive.toggle_quietdec();
open pairSyntax;
 HOL_Interactive.toggle_quietdec();
 *)
    
in(*local*)

end (* struct *)
