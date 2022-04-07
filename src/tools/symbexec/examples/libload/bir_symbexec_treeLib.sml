structure bir_symbexec_treeLib =
struct

local
    open HolKernel Parse boolLib pairLib hol88Lib numLib reduceLib tautLib
		   pairTheory numTheory prim_recTheory arithmeticTheory
		   realTheory Ho_Rewrite jrhUtils Canon_Port AC numSyntax Arbint;
    open String;
    open boolSyntax;
    open bitstringSyntax;
    open imlLib;
    open List;
    open bir_envSyntax;
    open bir_immSyntax;
    open bir_expSyntax;
    open bir_exp_immSyntax;
    open commonBalrobScriptLib;
    open bir_symbexec_oracleLib;
    open bir_symbexec_stateLib;
    open bir_symbexec_coreLib;
    open Int;
    open Redblackmap;
    open Redblackset;
    open bitstringSyntax;
    open  bir_symbexec_funcLib;
    val ERR = Feedback.mk_HOL_ERR "bir_symbexec_treeLib"

in

fun rev_name pred_name =
    let
	val a = (fst o (bir_auxiliaryLib.list_split_pred #"_") o explode) pred_name;
	val b = (snd o (bir_auxiliaryLib.list_split_pred #"_") o explode) pred_name;

	val rev_pred_name = (implode b)^"_"^(implode a);
    in
	rev_pred_name
    end;

fun Fun_Str str_be =
    let
	val a = (fst o (bir_auxiliaryLib.list_split_pred #" ") o explode) str_be;

	val b = (snd o (bir_auxiliaryLib.list_split_pred #" ") o explode) str_be;

	val fun_str = if (List.exists (fn x => x = #" ") b)
		      then
			  let
			      val c = (fst o (bir_auxiliaryLib.list_split_pred #" ")) b;

			      val d = (snd o (bir_auxiliaryLib.list_split_pred #" ")) b;
			  in
			      (implode a)^"("^(implode c)^","^(implode d)^")"
			  end
		      else
			  (implode a)^"("^(implode b)^")";
    in
	fun_str
    end;  
(*Collect path names*)
fun path_to_names [] Pred_Names =
    (Pred_Names)
  | path_to_names (pred::preds) Pred_Names =
    let
	val pred_name = (fst o bir_envSyntax.dest_BVar_string) pred;

	val Pred_Names = pred_name::Pred_Names;
    in
	path_to_names preds Pred_Names
    end; 

(*Collect all path names*)
fun symb_execs_preds [] All_preds =
        (All_preds)
  | symb_execs_preds (exec_st::exec_sts) All_preds =
    let
	val preds = SYST_get_pred exec_st;

	val pred_names = path_to_names preds [];

	val All_preds = pred_names@All_preds;

    in	
	symb_execs_preds exec_sts All_preds
    end;

fun swap(A,i,j) = 
    let
        val t = Array.sub(A,i)
    in
        Array.update(A,i,Array.sub(A,j));
        Array.update(A,j,t)
    end;

fun firstAfter(A,i,f) =
    if f(Array.sub(A,i)) then i else firstAfter(A,i+1,f);

fun lastBefore(A,j,f) =
    if f(Array.sub(A,j)) then j else lastBefore(A,j-1,f);

fun partition1(A,lo,hi)=
    let 
        fun partition'(A,lo,hi,pivot) = 
            let 
                val i = firstAfter(A,lo,fn k => (Option.valOf o Int.fromString)k >= pivot);
                val j = lastBefore(A,hi,fn k => (Option.valOf o Int.fromString)k <= pivot);
            in
                if i >= j then 
                    j
                else
                (
                    swap(A,i,j);
                    partition'(A,i+1,j-1,pivot)
                 )
             end
   in
      partition'(A,lo,hi,(Option.valOf o Int.fromString)(Array.sub(A,lo)))
    end;

fun quicksort(A,lo,hi) = 
    if hi <= lo then
        ()
    else
        let
            val p = partition1(A,lo,hi)
        in
            (
                quicksort(A,lo,p);
                quicksort(A,p+1,hi)
             )
        end;

fun qsort A = quicksort(A,0,Array.length A - 1);

fun arrayToList arr = Array.foldr (op ::) [] arr;    

(*Remove repeated path names*)
fun Remove_Repeated_preds (pred::[]) No_Repeat =
        (No_Repeat)
  | Remove_Repeated_preds (pred::preds) (No_Repeat: string list) =
    let
	val hd_pr = hd(preds); 
	val No_Repeat = if (pred = hd_pr)
			then No_Repeat
			else hd_pr::No_Repeat;
    in	
	Remove_Repeated_preds (preds) No_Repeat
    end;


(*Sort and refine path names*)
(*
val all_preds =
   ["2_init_pred", "37_Key", "39_T", "42_iv", "44_T", "47_K", "46_Adv",
    "53_cjmp_true_cnd", "56_Key", "58_T", "2_init_pred", "37_Key", "39_T",
    "42_iv", "44_T", "47_K", "46_Adv", "54_cjmp_false_cnd", "61_K", "60_Adv"];

val sort_preds =
   ["2_init_pred", "2_init_pred", "37_Key", "37_Key", "39_T", "39_T",
    "42_iv", "42_iv", "44_T", "44_T", "46_Adv", "46_Adv", "47_K", "47_K",
    "53_cjmp_true_cnd", "54_cjmp_false_cnd", "56_Key", "58_T", "60_Adv",
    "61_K"];

val refine_preds =
   ["61_K", "60_Adv", "58_T", "56_Key", "54_cjmp_false_cnd",
    "53_cjmp_true_cnd", "47_K", "46_Adv", "44_T", "42_iv", "39_T", "37_Key",
    "2_init_pred"];

val b = "2_init_pred";

(Option.valOf o Int.fromString) b
open Array;

val b = (List.map (fn x => (Option.valOf o Int.fromString) x) all_preds);
val A = Array.fromList all_preds;

val a = qsort A;
open Vector;
*)
fun get_refine_preds_list exec_sts =
    let
	val all_preds = symb_execs_preds exec_sts [];

	val A = Array.fromList all_preds;

	val _ = qsort A;

	val sort_preds = arrayToList A;
	    
	val refine_preds = Remove_Repeated_preds sort_preds [hd sort_preds];
  
    in
	refine_preds
    end;
    

(*Collect all symbolic value*)
fun symb_execs_vals_term [] All_vals =
        (All_vals)
  | symb_execs_vals_term (exec_st::exec_sts) All_vals =
    let
	val vals = SYST_get_vals exec_st;

	val vals_list = Redblackmap.listItems vals;

	val All_vals = vals_list@All_vals;

    in	
	symb_execs_vals_term exec_sts All_vals
    end;


(*Find bir expression*)
fun find_be_val vals_list bv =
    let
	val find_val = List.find (fn (a,_) => Term.term_eq a bv) vals_list;
    in
	(snd o Option.valOf) find_val
    end;

(*Find the latest library output*)
fun find_latest_T refine_preds exec_sts preds =
    let
	
	val previous_preds = drop(refine_preds, (length preds));
	    
	val (preds_keep, preds_removed) = List.partition (String.isSuffix "T") previous_preds;

    in
	if List.null preds_keep
	then NONE
	else SOME(hd(preds_keep))
    end;
    
(*Translate knowledge to IML out*)
(*
val All_preds =
   ["2_init_pred", "37_Key", "39_T", "42_iv", "44_T", "46_Adv", "47_K",
    "53_cjmp_true_cnd", "54_cjmp_false_cnd", "56_Key", "58_T", "60_Adv",
    "61_K"];
-----------
val pred = "47_K";
val preds = ["53_cjmp_true_cnd", "54_cjmp_false_cnd", "56_Key", "58_T", "60_Adv",
    "61_K"];
val t_pred = "44_T";
val t_term = “BVar "44_T" BType_Bool”;
val t_be = “enc inputs iv”;
val pred_term = “BVar "47_K" BType_Bool”;
val k_be = “enc inputs iv”;
val result = out(c, enc inputs iv);
-------
val pred = "61_K";
val preds = [];
val t_pred = "58_T";
val t_term = “BVar "58_T" BType_Bool”;
val t_be = “BVar "57_k" (BType_Imm Bit64)”;
val pred_term = “BVar "61_K" BType_Bool”;
val k_be = “BVar "48_a" (BType_Imm Bit64)”;
val result = ();
 *)


fun K_to_Out vals_list refine_preds exec_sts pred preds =
    let
	val t_pred_option = find_latest_T refine_preds exec_sts preds;

	val result = if ((not o Option.isSome) t_pred_option)
		     then ""
		     else (
			 let
			     val t_term = bir_envSyntax.mk_BVar_string((Option.valOf t_pred_option), “BType_Bool”);
				 
			     val t_be = symbval_bexp (find_be_val vals_list t_term);

			     val pred_term = bir_envSyntax.mk_BVar_string(pred, “BType_Bool”);    

			     val k_be =  symbval_bexp (find_be_val vals_list pred_term);

			     val str_be = term_to_string k_be;

			     val fun_str = Fun_Str str_be;

			 in
			     if (Term.term_eq t_be k_be)
			     then (to_string (I_Out [(Var (fun_str))]))
			     else ""
			 end);
			 

    in
	result
    end;
    
(*Translate deduce to IML in*)
fun D_to_In pred_name = (I_In [(rev_name pred_name)]);
    
(*Translate fresh to IML new*)
fun Fr_to_New pred_name = (I_New ((rev_name pred_name), N(64)));    

(*Translate branch true to IML True*)
fun Br_True pred_name = (I_True (Var pred_name));

(*Translate assume to IML event*)
fun assume_to_event pred_name = (I_Event pred_name);

fun IML_event event_names pred =
    let

	val pred_name = if (String.isSuffix "event_false_cnd" pred) then ("bad"^" "^(hd(event_names)))
			else if ((String.isSuffix "event_true_cnd" pred) orelse (String.isSuffix "event1" pred))
			then (List.nth (event_names, 1))
			else if (String.isSuffix "event2" pred)
			then (List.nth (event_names, 2))
			else if (String.isSuffix "event3" pred)
			then (List.nth (event_names, 3))
			else raise ERR "IML_event" "cannot handle this pred";

    in
	((to_string o I_Event) pred_name)
    end;

(*Translate XOR to IML*)    
fun Xor_to_IML vals_list pred =
    let
	
	val pred_term = bir_envSyntax.mk_BVar_string(pred, “BType_Bool”);    

	val x_be =  symbval_bexp (find_be_val vals_list pred_term);

	val str_be = term_to_string x_be;

	val fun_str = Fun_Str str_be;

    in
	(to_string (I_Out [(Var (fun_str))]))

    end;

(*Translate Let to IML*)    
fun Let_to_IML vals_list pred =
    let
	
	val pred_term = bir_envSyntax.mk_BVar_string(pred, “BType_Bool”);    

	val be =  symbval_bexp (find_be_val vals_list pred_term);

	val fun_str = if (is_BExp_Den be)
		      then ((rev_name o fst o dest_BVar_string o dest_BExp_Den) be)
		      else if (is_BVar be)
		      then ((rev_name o fst o dest_BVar_string) be)
		      else Fun_Str (term_to_string be);

	val fun_str = if (String.isSuffix "kS" pred)
		      then ("kgen("^fun_str^")")
		      else if(String.isSuffix "kAB" pred)
		      then ("lookup(hClient,hServer,"^fun_str^")")
		      else fun_str;

    in
	(to_string (I_Let ((rev_name pred), (Var (fun_str)))))

    end;    
(*Translate BIR expressions to IML expressions*)
(*
val pred_be = “BExp_Const (Imm64 2840w)”; val result = "2840";
val be = “BExp_Den (BVar "88_MEM" (BType_Mem Bit64 Bit8))”;
val pred_be = ``BExp_Cast BIExp_LowCast
                        (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32``;
val pred_be = ``BExp_UnaryExp BIExp_Not
                       (BExp_Den (BVar "ProcState_C" BType_Bool))``;
val pred_be = “BExp_BinPred BIExp_Equal
          (BExp_Cast BIExp_LowCast
             (BExp_Den (BVar "16_Adv" (BType_Imm Bit64))) Bit64)
          (BExp_Const (Imm64 0w))”;
val pred_be = ``BExp_BinExp BIExp_And
		       (BExp_BinPred BIExp_LessOrEqual
 (BExp_BinExp BIExp_Plus
  (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
(BExp_Const (Imm64 24w)))
(BExp_Const (Imm64 18446744073709551607w)))
(BExp_BinExp BIExp_Or
(BExp_BinPred BIExp_NotEqual
(BExp_BinExp BIExp_Minus
(BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
(BExp_Const (Imm64 24w)))
(BExp_Const (Imm64 3489660928w)))
(BExp_BinPred BIExp_LessThan
(BExp_BinExp BIExp_Mult
(BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
(BExp_Const (Imm64 24w)))
(BExp_Const (Imm64 3489660928w))))``;
 *)

fun BExp_to_IMLExp vals_list exec_sts pred_be =
    let
	(* val _ = print ((term_to_string pred_be)^"\n"); *)
	val result = if (is_BExp_Const pred_be) then
			 (if (is_Imm128 o dest_BExp_Const) pred_be then
			      ((Arbnum.toString o wordsSyntax.dest_word_literal o dest_Imm128 o dest_BExp_Const) pred_be)
			  else if (is_Imm64 o dest_BExp_Const) pred_be then
			      ((Arbnum.toString o wordsSyntax.dest_word_literal o dest_Imm64 o dest_BExp_Const) pred_be)
			  else if (is_Imm32 o dest_BExp_Const) pred_be then
			      ((Arbnum.toString o wordsSyntax.dest_word_literal o dest_Imm32 o dest_BExp_Const) pred_be)
			  else if (is_Imm16 o dest_BExp_Const) pred_be then
			      ((Arbnum.toString o wordsSyntax.dest_word_literal o dest_Imm16 o dest_BExp_Const) pred_be)
			  else if (is_Imm8 o dest_BExp_Const) pred_be then
			      ((Arbnum.toString o wordsSyntax.dest_word_literal o dest_Imm8 o dest_BExp_Const) pred_be)
			  else if (is_Imm1 o dest_BExp_Const) pred_be then
			      ((Arbnum.toString o wordsSyntax.dest_word_literal o dest_Imm1 o dest_BExp_Const) pred_be)
			  else raise ERR "BExp_Const:BExp_to_IMLExp" "this should not happen")
		     else if (is_BExp_Den pred_be) then
			 (if identical “BType_Bool” ((snd o dest_BVar o dest_BExp_Den) pred_be) then
			      let
				  val pred_be_bool = symbval_bexp (find_be_val vals_list (dest_BExp_Den pred_be));
				  
			      in
				  BExp_to_IMLExp vals_list exec_sts pred_be_bool
			      end
			  else ((fst o dest_BVar_string o dest_BExp_Den) pred_be))
		     else if (is_BExp_Cast pred_be) then
			 let
			     val (castt, subexp, sz) = (dest_BExp_Cast) pred_be;
			 in
			     BExp_to_IMLExp vals_list exec_sts subexp
			 end
		     else if (is_BExp_UnaryExp pred_be) then
			 let
			     val (uop, subexp) = (dest_BExp_UnaryExp) pred_be;
			     val res = if identical uop BIExp_Not_tm then
					   ("¬")
				       else raise ERR "BExp_UnaryExp:BExp_to_IMLExp" "this should not happen"
			 in
			     (res^(BExp_to_IMLExp vals_list exec_sts subexp))
			 end
		     else if (is_BExp_BinExp pred_be) then
			 let
			     val (bop, subexp1, subexp2) = (dest_BExp_BinExp) pred_be;

			     val flag = if ((is_BExp_Const subexp1) orelse (is_BExp_Const subexp2))
					then (if ((identical bop BIExp_And_tm) orelse (identical bop BIExp_Xor_tm) orelse (identical bop BIExp_Or_tm))
					     then true
					     else false)
					else false;


			     val res = if flag
				       then
					   (if identical bop BIExp_And_tm then ("Bitwise_And")
					    else if identical bop BIExp_Or_tm then ("Bitwise_Or")
					    else if identical bop BIExp_Xor_tm then ("Bitwise_Xor")
					    else raise ERR "BExp_BinExp:Bitwise:BExp_to_IMLExp" ((term_to_string bop)^" this should not happen"))
				       else
					   (if identical bop BIExp_And_tm then ("∧")
					    else if identical bop BIExp_Or_tm then ("∨")
					    else if identical bop BIExp_Plus_tm then ("+")
					    else if identical bop BIExp_Minus_tm then ("-")
					    else if identical bop BIExp_Mult_tm then ("*")
					    else raise ERR "BExp_BinExp:Logical:BExp_to_IMLExp" ((term_to_string bop)^" this should not happen"));

			 in
			     if flag
			     then
				 IExp_to_string (Ops [(Var res), (Var (BExp_to_IMLExp vals_list exec_sts subexp1)), (Var (BExp_to_IMLExp vals_list exec_sts subexp2))])
			     else
				 ("("^(BExp_to_IMLExp vals_list exec_sts subexp1)^res^(BExp_to_IMLExp vals_list exec_sts subexp2)^")")
			 end
		     else if (is_BExp_BinPred pred_be) then
			 let 
			     val (bop, subexp1, subexp2) = (dest_BExp_BinPred) pred_be;
			     val res = if identical bop BIExp_Equal_tm then ("=")
				       else if identical bop BIExp_NotEqual_tm then ("≠")
				       else if ((identical bop BIExp_LessThan_tm) orelse (identical bop BIExp_SignedLessThan_tm)) then ("<")
				       else if ((identical bop BIExp_LessOrEqual_tm) orelse (identical bop BIExp_SignedLessOrEqual_tm)) then ("<=")
				       else raise ERR "BExp_BinPred:BExp_to_IMLExp" "this should not happen" 
			 in
			     ("("^(BExp_to_IMLExp vals_list exec_sts subexp1)^res^(BExp_to_IMLExp vals_list exec_sts subexp2)^")")
			 end
		     else if (bir_bool_expSyntax.is_bir_exp_false pred_be) then (BExp_to_IMLExp vals_list exec_sts ``BExp_Const (Imm1 0w)``)
		     else if (bir_bool_expSyntax.is_bir_exp_true pred_be) then (BExp_to_IMLExp vals_list exec_sts ``BExp_Const (Imm1 1w)``)					     
		     else if (is_BExp_IfThenElse pred_be) then raise ERR "BExp_IfThenElse:BExp_to_IMLExp" "this should not happen"
		     else if (is_BExp_MemConst pred_be) then raise ERR "BExp_MemConst:BExp_to_IMLExp" "this should not happen"
		     else if (is_BExp_MemEq pred_be) then raise ERR "BExp_MemEq:BExp_to_IMLExp" "this should not happen"
		     else if (is_BExp_Load pred_be) then raise ERR "BExp_Load:BExp_to_IMLExp" "this should not happen"
		     else if (is_BExp_Store pred_be) then raise ERR "BExp_Store:BExp_to_IMLExp" "this should not happen"
		     else raise ERR "BExp_to_IMLExp" "this should not happen";

    in
	result
    end;

(*Extract BIR expressions from pred name*)
(*
val pred = "165_assert_true_cnd";
val pred_term = “BVar "23_cjmp_true_cnd" BType_Bool”;
val pred_be = “BExp_Den (BVar "22_ProcState_Z" BType_Bool)”;
*)
(*val _ = let val IFile = TextIO.openAppend "Symbolic Execution Preds Vals.txt"; in TextIO.output (IFile, (term_to_string pred_be) ^ "\n ----------------- \n" ); TextIO.flushOut IFile end;*)
    
fun IMLExp_from_pred vals_list exec_sts pred =
    let

	(* val _ = print ("\n "^pred); *)
	val pred_term = bir_envSyntax.mk_BVar_string(pred, “BType_Bool”);
	    
	val pred_be = symbval_bexp (find_be_val vals_list pred_term);

	(* val _ = print ("\n "^(term_to_string pred_be)); *)
	val pred_IML_Exp = BExp_to_IMLExp vals_list exec_sts pred_be;

    in
	pred_IML_Exp
    end;
    
(*Translate paths to IML*)
(*
val pred = "37_Key";
val preds = ["39_T", "42_iv", "44_T", "46_Adv", "47_K",
    "53_cjmp_true_cnd", "54_cjmp_false_cnd", "56_Key", "58_T", "60_Adv",
    "61_K"];
val Act = new 37_Key: 64;

val pred = "60_Adv";
val preds = ["61_K"];
val Act = in(c, 60_Adv);
 *)

fun assert_false_string event_names vals_list exec_sts pred =
    let
	val assert_if = ((to_string o Br_True) (IMLExp_from_pred vals_list exec_sts pred));
	val assert_event = ((to_string o assume_to_event) ("bad"^" "^(hd(event_names))));
	val assert_else = (to_string (I_False ()));
    in
	(assert_if^assert_event^assert_else)
    end;
    
	
fun path_of_tree event_names vals_list refine_preds exec_sts [] str =
    (str)
  | path_of_tree event_names vals_list refine_preds exec_sts (pred::preds) str =
    let

	val Act = if (String.isSuffix "assert_true_cnd" pred) then ""
		  else if (String.isSuffix "cjmp_true_cnd" pred) then (if (String.isSuffix "0" (IMLExp_from_pred vals_list exec_sts pred))
	then ""
	     else (to_string o Br_True) (IMLExp_from_pred vals_list exec_sts pred))
		  else if (String.isSuffix "assert_false_cnd" pred) then (assert_false_string event_names vals_list exec_sts pred)
		  else if (String.isSuffix "cjmp_false_cnd" pred) then ""
		  else if ((String.isSuffix "Key" pred) orelse (String.isSuffix "iv" pred) orelse (String.isSuffix "RAND_NUM" pred) orelse (String.isSuffix "OTP" pred) orelse (String.isSuffix "SKey" pred)) then (to_string o Fr_to_New) pred
		  else if (String.isSuffix "K" pred) then (K_to_Out vals_list refine_preds exec_sts pred preds)
		  else if (String.isSuffix "Adv" pred) then (to_string o D_to_In) pred
		  else if (String.isSuffix "XOR" pred) then (Xor_to_IML vals_list pred)
		  else if ((String.isSuffix "msg" pred) orelse (String.isSuffix "cipher" pred) orelse (String.isSuffix "kS" pred) orelse (String.isSuffix "kAB" pred)) then (Let_to_IML vals_list pred)
		  else if ((String.isSuffix "event_true_cnd" pred) orelse (String.isSuffix "event1" pred) orelse (String.isSuffix "event2" pred) orelse (String.isSuffix "event3" pred) orelse (String.isSuffix "event_false_cnd" pred))
		  then (IML_event event_names pred)
		  else "";

	val str = str^Act;
	    
    in
	(*if (String.isSuffix "cjmp_false_cnd" pred andalso ((not o List.null) preds))
	   	then (path_of_tree event_names vals_list refine_preds exec_sts (tl preds) str)
	 else*)
	     (if (String.isSuffix "cjmp_true_cnd" pred andalso (List.length preds = 2))
	then ((path_of_tree event_names vals_list refine_preds exec_sts [((hd o tl) preds)] str)^(to_string (I_False ())))
	else (path_of_tree event_names vals_list refine_preds exec_sts preds str))
    end;


(*Translate symbolic execution states to IML*)
(*
 val refine_preds =
     ["61_K", "60_Adv", "58_T", "56_Key", "54_cjmp_false_cnd",
      "53_cjmp_true_cnd", "47_K", "46_Adv", "44_T", "42_iv", "39_T", "37_Key",
      "2_init_pred"];
    
 Final Output:
     new 37_Key: 64;
     new 42_iv: 64;
in(c, 46_Adv);
  out(c, enc inputs iv);
  if 53_cjmp_true_cnd then
      new 56_Key: 64;
  else in(c, 60_Adv);

val exec_sts = systs;
*) 
fun sym_exe_to_IML exec_sts =
    let
	
	val event_names = bir_symbexec_oracleLib.read_fun_names "Event-Names";

	val vals_list = symb_execs_vals_term exec_sts [];

	val refine_preds = get_refine_preds_list exec_sts;

	(* val _ = print ("\n number of refine path predicates found: " ^ (Int.toString (length refine_preds))^"\n \n"); *)
	    
	val IML_str = path_of_tree event_names vals_list refine_preds exec_sts (rev refine_preds) "";
    
    in
	IML_to_file IML_str
    end;
    

end(*local*)

end (* struct *)
