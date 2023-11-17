structure sbir_treeLib =
struct
local
    open HolKernel Parse;
    open HolBACoreSimps;
    open HolBASimps;
    open boolSyntax;
    open pred_setTheory;
    open simpLib;
    open bossLib;
    open bir_symbexec_stateLib;
    open Option;
    open List;

  val ERR      = Feedback.mk_HOL_ERR "sbir_treeLib"
  val wrap_exn = Feedback.wrap_exn   "sbir_treeLib"
in


(*
(* Define a datatype for binary trees *)
datatype 'a tree = Leaf | Node of 'a * 'a tree | Branch of 'a tree * 'a tree;


(* Define a function to create a tree from two lists *)
fun listsToTree [] [] = Leaf
  | listsToTree [] (y::ys) = Node (y, listsToTree [] ys)
  | listsToTree (x::xs) [] = Node (x, listsToTree xs [])
  | listsToTree (x::xs) (y::ys) =
    if identical x y 
    then Node (x, listsToTree xs ys)
    else Branch ((Node (x,(listsToTree xs []))),(Node (y,(listsToTree [] ys))));


val a = rev(SYST_get_pred (List.nth (systs, 1)));
val b = rev(SYST_get_pred (List.nth (systs, 3)));
val c = listsToTree a b;
    
val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst))
                         systs;
 
 ((List.foldl (fn (true,ls) => if (is_true (identical (hd hdOfFirstList) (hd ls))) then true else raise ERR "" "") true lst)handle _ => false)
  
compareHeads [[]]
 *)


fun is_true b = ((lift_bool “:bool” b) ~~ T)
fun is_false b = ((lift_bool “:bool” b) ~~ F)

fun is_true_list [] = true
  | is_true_list (h::t) =
    if (is_true h)
    then (is_true_list t)
    else false		 
		
fun allHeadsEqual ([]: term list list) = false
  | allHeadsEqual (lst: term list list) =
  if ((not o null o hd) lst)
  then
      let
	  (* val _ = print "1\n" *)
	  val hdOfFirstList = hd lst
	  (* val _ = print "2\n" *)
				val result = ((List.map (fn ls => if (is_true (identical (hd hdOfFirstList) (hd ls))) then true else raise ERR "" "") lst) handle _ => [false]);

	(*		     
	  fun compareHeads ([]: term list list) = true
	    | compareHeads ((h: term list)::t) = if (identical (hd hdOfFirstList) (hd h)) then compareHeads t else false*)
      (* val _ = print "3\n" *)
      in
      (* compareHeads lst *)
	  if (is_false (hd result))
	  then false
	  else true
      end
  else false;
 

(*
fun HeadsEqual fulllist ([]: term list) = false
  | HeadsEqual fulllist (lst: term list) =
    let
	(* val _ = print "4\n" *)
	val hdOfFirstList = hd lst
			    
	(* val _ = print "5\n" *)
	val result = ((List.map (fn ls => if (is_true (identical hdOfFirstList (hd ls))) then true else raise ERR "" "") fulllist) handle _ => [false]);
	    
	(* fun compareHeads ([]: term list list) = true *)
	(*   | compareHeads ((h: term list )::t) = if (identical hdOfFirstList (hd h)) then compareHeads t else false *)
    (* val _ = print "6\n" *)
    in
	compareHeads fulllist
    end;



fun fnd_dif m =
 (identical ((hd o hd) lst) (hd m))


val fulllist = lst;
val lst = [“BVar "7427_Ver" BType_Bool”];
val lst =[  [
     “BVar "31_assert_true_cnd" BType_Bool”,
     “BVar "34_assert_true_cnd" BType_Bool”,
     “BVar "39_assert_true_cnd" BType_Bool”,
     “BVar "44_assert_true_cnd" BType_Bool”,
     “BVar "48_OTP" BType_Bool”, “BVar "50_T" BType_Bool”,
     “BVar "51_assert_true_cnd" BType_Bool”,
     “BVar "54_assert_false_cnd" BType_Bool”],
    [“BVar "50_T" BType_Bool”,
     “BVar "51_assert_true_cnd" BType_Bool”,
     “BVar "53_assert_true_cnd" BType_Bool”,
     “BVar "57_assert_false_cnd" BType_Bool”]];


 val lst = [[],[“BVar "57_assert_false_cnd" BType_Bool”]]
val lst = [[“BVar "57_assert_false_cnd" BType_Bool”],[“BVar "57_assert_false_cnd" BType_Bool”,“BVar "59_assert_false_cnd" BType_Bool”]]  
tl 
val ls = [“BVar "57_assert_false_cnd" BType_Bool”]
val head_eq = [[“BVar "59_assert_false_cnd" BType_Bool”],[“BVar "59_assert_false_cnd" BType_Bool”,“BVar "60_assert_false_cnd" BType_Bool”]] 
predlist_to_tree lst
val  
val smltree = predlist_to_tree lst;
val lst =  [[]]
tl lst
val lst = [[], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [], [], [], [], [], [], [], [], [], [], [], [], [], [], [],
    [“BVar "7427_Ver" BType_Bool”], [“BVar "7427_Ver" BType_Bool”],
    [“BVar "7427_Ver" BType_Bool”], [“BVar "7427_Ver" BType_Bool”],
    [“BVar "7944_Ver" BType_Bool”], [“BVar "7944_Ver" BType_Bool”],
    [“BVar "7944_Ver" BType_Bool”], [“BVar "7944_Ver" BType_Bool”]];
raise ERR "predlist_to_tree" ("cannot do it "^(String.concat(List.concat(List.map (fn ls => (List.map (fn l => ("\n"^(term_to_string l))) ls)) lst))))

)handle _ => raise ERR "predlist_to_tree" ("cannot do it "^(String.concat(List.map (fn ls => ("\n"^((int_to_string o List.length) ls))) lst)))
val lst = head_noteq;
*)
(* Define a datatype for trees *)
datatype 'a tree = Leaf | Node of 'a * 'a tree | Branch of 'a * 'a tree * 'a tree;

(*	 
fun predlist_to_tree ([[]]: term list list) = Leaf
  | predlist_to_tree ([]: term list list) = Leaf
  | predlist_to_tree (lst: term list list) =    
    if (allHeadsEqual lst) then
	if ((not o null o hd) lst)
	then
	(Node ((hd (hd lst)), (predlist_to_tree (List.map (fn ls => (tl ls)) lst))))handle _ => raise ERR "predlist_to_tree" ("cannot do it "^(String.concat(List.map (fn ls => ("\n"^((int_to_string o List.length) ls))) lst)))

	else predlist_to_tree (tl lst)
    else 
	(let
	     (* val _ = print "7.5\n" *)
	     val (head_noteq, head_eq) = List.partition (fn ls => (identical ((hd o hd) lst) (hd ls))) lst

	(* val _  = if ((not o null o hd) head_eq) *)
	(* 	 then print "not empty\n" *)
	(* 	 else print "empty\n" *)
		     
		     
	 in
	     if ((not o null) head_eq) then
		 if ((not o null o hd) head_eq)
		 then
		     Branch ((hd (hd head_eq)),(predlist_to_tree (List.map (fn ls => (tl ls)) head_eq)),(predlist_to_tree (List.map (fn ls => (tl ls)) head_noteq)))
		 else predlist_to_tree head_noteq
	     else predlist_to_tree head_noteq
	 end)



then
		if ((not o null o hd) head_eq)
		then
		    if (is_true_list (List.map (fn ls => ((null o tl) ls)) head_eq))
		    then (Node ((hd (hd head_eq)), Leaf))
		    else
			if ((exists is_false (List.map (fn ls => ((null o tl) ls)) head_eq)) andalso (exists is_true (List.map (fn ls => ((null o tl) ls)) head_eq)))
			then
			    let
				
		    else
     
 *)

	 
fun predlist_to_tree ([[]]: term list list) = Leaf
  | predlist_to_tree ([]: term list list) = Leaf
  | predlist_to_tree (lst: term list list) =    
    if (is_true_list (List.map (fn ls => (null ls)) lst)) then Leaf
    else
	let
	val (empty, notempty) =
	    if ((exists is_false (List.map (fn ls => (null ls)) lst)) andalso (exists is_true (List.map (fn ls => (null ls)) lst)))
	    then List.partition (fn ls => (null ls)) lst
	    else ([[]],lst)
		    
	val (head_eq, head_noteq) = if ((not o null o hd) notempty)
				    then List.partition (fn ls => (identical ((hd o hd) notempty) (hd ls))) notempty
				    else List.partition (fn ls => (identical ((hd o hd o rev) notempty) (hd ls))) notempty;
    in
	    if (null head_noteq)
	    then
		    (Node ((hd (hd head_eq)), (predlist_to_tree (List.map (fn ls => (tl ls)) head_eq))))handle _ => raise ERR "predlist_to_tree" ("cannot do it "^(String.concat(List.map (fn ls => ("\n"^((int_to_string o List.length) ls))) head_eq)))
	    else
		if ((not o null) head_eq) then
		    if ((not o null o hd) head_eq)
		    then
			Branch ((hd (hd head_eq)),(predlist_to_tree (List.map (fn ls => (tl ls)) head_eq)),(predlist_to_tree (List.map (fn ls => (tl ls)) head_noteq)))
		    else predlist_to_tree head_noteq
		else predlist_to_tree head_noteq
		     
    end

	
(*Find bir expression*)
fun find_be_val vals_list bv =
    let
	val find_val = List.find (fn (a,_) => Term.term_eq a bv) vals_list;
	val symbv = ((snd o Option.valOf) find_val) handle _ => raise ERR "find_be_val" ("cannot find symbolic value for "^(term_to_string bv)^"\n");
	val exp =
	    case symbv of
		SymbValBE (x, _) => x
              | _ => raise ERR "find_be_val" "cannot handle symbolic value type";
    in
	exp
    end;


(* Define a datatype for trees with values *)
datatype 'a valtree = VLeaf | VNode of ('a * 'a) * 'a valtree | VBranch of ('a * 'a) * 'a valtree * 'a valtree;

	 
fun tree_with_value tr sort_vals =
    case tr of
	Leaf => VLeaf
      | Node (bv, subtr) => VNode ((bv,(find_be_val sort_vals bv)), (tree_with_value subtr sort_vals))
      | Branch (bv, subtr1, subtr2) => VBranch ((bv,(find_be_val sort_vals bv)), (tree_with_value subtr1 sort_vals), (tree_with_value subtr2 sort_vals))


fun hd_of_tree tr =
    case tr of
	VLeaf => NONE
      | VNode ((bv,be), subtr) => SOME (bv,be)
      | VBranch ((bv,be), subtr1, subtr2) => SOME (bv,be)


fun purge_tree tr =
    case tr of
	VLeaf => VLeaf
      | VNode ((bv,be), subtr) => if (isSome (hd_of_tree subtr)) then
				      if ((identical ((fst o valOf o hd_of_tree) subtr) bv) andalso (identical ((snd o valOf o hd_of_tree) subtr) be))
				      then (purge_tree subtr)
				      else VNode ((bv,be), (purge_tree subtr))
				  else VNode ((bv,be), (purge_tree subtr))
      | VBranch ((bv,be), subtr1, subtr2) => VBranch ((bv,be), (purge_tree subtr1), (purge_tree subtr2))					     

(* define a symbolic tree hol datatype 
val _ = Datatype `stree =
SLeaf
| SNode 'a 'b stree
| SBranch 'a 'b stree stree
	  `;

fun smltree_to_holtree tree =
    case tree of
        VLeaf => mk_const ("SLeaf",``:(bir_var_t,bir_exp_t) stree``)
      | VBranch ((a,b),lsubtree, rsubtree) => (mk_comb (mk_comb (mk_comb (mk_comb (mk_const ("SBranch",``:bir_var_t -> bir_exp_t -> (bir_var_t,bir_exp_t) stree -> (bir_var_t,bir_exp_t) stree -> (bir_var_t,bir_exp_t) stree``),a),b), smltree_to_holtree lsubtree), smltree_to_holtree rsubtree))
      | VNode ((a,b), subtree) => (mk_comb (mk_comb (mk_comb (mk_const ("SNode",``:bir_var_t -> bir_exp_t -> (bir_var_t,bir_exp_t) stree -> (bir_var_t,bir_exp_t) stree``), a),b), smltree_to_holtree subtree)) handle HOL_ERR {message = "incompatible types", ...} =>
      mk_const ("SLeaf",``:(bir_var_t,bir_exp_t) stree``);

HOL_Interactive.toggle_quietdec();
open List;
HOL_Interactive.toggle_quietdec(); 

purge_tree valtr				       


val holtree = smltree_to_holtree smltree;
 
val symbtree_def = Define `
    symbtree = ^(holtree)
		    `;
		    
*)
end (* local *)

end (* struct *)



(*

val valtr =
   VNode
    ((“BVar "0_init_pred" BType_Bool”, “bir_exp_true”),
     VNode
      ((“BVar "1_assert_true_cnd" BType_Bool”,
        “BExp_BinPred BIExp_Equal
           (BExp_BinExp BIExp_And
              (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
              (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w))”),
       VNode
        ((“BVar "3_assert_true_cnd" BType_Bool”,
          “BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_LessOrEqual
                (BExp_BinExp BIExp_Minus
                   (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
                   (BExp_Const (Imm64 64w)))
                (BExp_Const (Imm64 0xFFFFFFFFFFFFFFEFw)))
             (BExp_BinExp BIExp_And
                (BExp_BinExp BIExp_Or
                   (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 64w))))
                   (BExp_BinPred BIExp_LessOrEqual
                      (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 16w))
                         (BExp_BinExp BIExp_Minus
                            (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 64w))))
                      (BExp_Const (Imm64 0w))))
                (BExp_BinExp BIExp_Or
                   (BExp_BinPred BIExp_LessThan
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 64w))) (BExp_Const (Imm64 0w)))
                   (BExp_BinPred BIExp_LessOrEqual
                      (BExp_Const (Imm64 0xFFFFFFFFw))
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 64w))))))”),
         VNode
          ((“BVar "7_assert_true_cnd" BType_Bool”,
            “BExp_BinPred BIExp_Equal
               (BExp_BinExp BIExp_And
                  (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w))”),
           VNode
            ((“BVar "9_assert_true_cnd" BType_Bool”,
              “BExp_BinExp BIExp_And
                 (BExp_BinPred BIExp_LessOrEqual
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 24w)))
                    (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                 (BExp_BinExp BIExp_And
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 0w))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den
                                (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 24w))))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                             (BExp_BinExp BIExp_Plus
                                (BExp_Den
                                   (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 24w))))
                          (BExp_Const (Imm64 0w))))
                    (BExp_BinExp BIExp_Or
                       (BExp_BinPred BIExp_LessThan
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den
                                (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 24w)))
                          (BExp_Const (Imm64 0w)))
                       (BExp_BinPred BIExp_LessOrEqual
                          (BExp_Const (Imm64 0xFFFFFFFFw))
                          (BExp_BinExp BIExp_Plus
                             (BExp_Den
                                (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                             (BExp_Const (Imm64 24w))))))”),
             VNode
              ((“BVar "13_assert_true_cnd" BType_Bool”,
                “BExp_BinPred BIExp_Equal
                   (BExp_BinExp BIExp_And
                      (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                      (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w))”),
               VNode
                ((“BVar "15_assert_true_cnd" BType_Bool”,
                  “BExp_BinExp BIExp_And
                     (BExp_BinPred BIExp_LessOrEqual
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 32w)))
                        (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                     (BExp_BinExp BIExp_And
                        (BExp_BinExp BIExp_Or
                           (BExp_BinPred BIExp_LessThan
                              (BExp_Const (Imm64 0w))
                              (BExp_BinExp BIExp_Plus
                                 (BExp_Den
                                    (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w))))
                           (BExp_BinPred BIExp_LessOrEqual
                              (BExp_BinExp BIExp_Plus (BExp_Const (Imm64 8w))
                                 (BExp_BinExp BIExp_Plus
                                    (BExp_Den
                                       (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 32w))))
                              (BExp_Const (Imm64 0w))))
                        (BExp_BinExp BIExp_Or
                           (BExp_BinPred BIExp_LessThan
                              (BExp_BinExp BIExp_Plus
                                 (BExp_Den
                                    (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w)))
                              (BExp_Const (Imm64 0w)))
                           (BExp_BinPred BIExp_LessOrEqual
                              (BExp_Const (Imm64 0xFFFFFFFFw))
                              (BExp_BinExp BIExp_Plus
                                 (BExp_Den
                                    (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 32w))))))”),
                 VNode
                  ((“BVar "18_assert_true_cnd" BType_Bool”,
                    “BExp_BinPred BIExp_Equal
                       (BExp_BinExp BIExp_And
                          (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                          (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w))”),
                   VNode
                    ((“BVar "22_assert_true_cnd" BType_Bool”,
                      “BExp_BinPred BIExp_Equal
                         (BExp_BinExp BIExp_And
                            (BExp_Den (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                            (BExp_Const (Imm64 7w))) (BExp_Const (Imm64 0w))”),
                     VNode
                      ((“BVar "24_assert_true_cnd" BType_Bool”,
                        “BExp_BinExp BIExp_And
                           (BExp_BinPred BIExp_LessOrEqual
                              (BExp_BinExp BIExp_Plus
                                 (BExp_Den
                                    (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                 (BExp_Const (Imm64 40w)))
                              (BExp_Const (Imm64 0xFFFFFFFFFFFFFFF7w)))
                           (BExp_BinExp BIExp_And
                              (BExp_BinExp BIExp_Or
                                 (BExp_BinPred BIExp_LessThan
                                    (BExp_Const (Imm64 0w))
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_Den
                                          (BVar "5_tmp_SP_EL0"
                                             (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 40w))))
                                 (BExp_BinPred BIExp_LessOrEqual
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_Const (Imm64 8w))
                                       (BExp_BinExp BIExp_Plus
                                          (BExp_Den
                                             (BVar "5_tmp_SP_EL0"
                                                (BType_Imm Bit64)))
                                          (BExp_Const (Imm64 40w))))
                                    (BExp_Const (Imm64 0w))))
                              (BExp_BinExp BIExp_Or
                                 (BExp_BinPred BIExp_LessThan
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_Den
                                          (BVar "5_tmp_SP_EL0"
                                             (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 40w)))
                                    (BExp_Const (Imm64 0w)))
                                 (BExp_BinPred BIExp_LessOrEqual
                                    (BExp_Const (Imm64 0xFFFFFFFFw))
                                    (BExp_BinExp BIExp_Plus
                                       (BExp_Den
                                          (BVar "5_tmp_SP_EL0"
                                             (BType_Imm Bit64)))
                                       (BExp_Const (Imm64 40w))))))”),
                       VNode
                        ((“BVar "27_assert_true_cnd" BType_Bool”,
                          “BExp_BinPred BIExp_Equal
                             (BExp_BinExp BIExp_And
                                (BExp_Den
                                   (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                (BExp_Const (Imm64 7w)))
                             (BExp_Const (Imm64 0w))”),
                         VNode
                          ((“BVar "31_assert_true_cnd" BType_Bool”,
                            “BExp_BinExp BIExp_And
                               (BExp_BinPred BIExp_LessOrEqual
                                  (BExp_Den (BVar "29_R0" (BType_Imm Bit64)))
                                  (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFEw)))
                               (BExp_BinExp BIExp_And
                                  (BExp_BinExp BIExp_Or
                                     (BExp_BinPred BIExp_LessThan
                                        (BExp_Const (Imm64 0w))
                                        (BExp_Den
                                           (BVar "29_R0" (BType_Imm Bit64))))
                                     (BExp_BinPred BIExp_LessOrEqual
                                        (BExp_BinExp BIExp_Plus
                                           (BExp_Const (Imm64 1w))
                                           (BExp_Den
                                              (BVar "29_R0" (BType_Imm Bit64))))
                                        (BExp_Const (Imm64 0w))))
                                  (BExp_BinExp BIExp_Or
                                     (BExp_BinPred BIExp_LessThan
                                        (BExp_Den
                                           (BVar "29_R0" (BType_Imm Bit64)))
                                        (BExp_Const (Imm64 0w)))
                                     (BExp_BinPred BIExp_LessOrEqual
                                        (BExp_Const (Imm64 0xFFFFFFFFw))
                                        (BExp_Den
                                           (BVar "29_R0" (BType_Imm Bit64))))))”),
                           VNode
                            ((“BVar "34_assert_true_cnd" BType_Bool”,
                              “BExp_BinPred BIExp_Equal
                                 (BExp_BinExp BIExp_And
                                    (BExp_Den
                                       (BVar "5_tmp_SP_EL0" (BType_Imm Bit64)))
                                    (BExp_Const (Imm64 7w)))
                                 (BExp_Const (Imm64 0w))”),
                             VNode
                              ((“BVar "39_assert_true_cnd" BType_Bool”,
                                “BExp_BinPred BIExp_Equal
                                   (BExp_BinExp BIExp_And
                                      (BExp_Den
                                         (BVar "5_tmp_SP_EL0"
                                            (BType_Imm Bit64)))
                                      (BExp_Const (Imm64 7w)))
                                   (BExp_Const (Imm64 0w))”),
                               VNode
                                ((“BVar "44_assert_true_cnd" BType_Bool”,
                                  “BExp_BinPred BIExp_Equal
                                     (BExp_BinExp BIExp_And
                                        (BExp_Den
                                           (BVar "5_tmp_SP_EL0"
                                              (BType_Imm Bit64)))
                                        (BExp_Const (Imm64 7w)))
                                     (BExp_Const (Imm64 0w))”),
                                 VNode
                                  ((“BVar "48_OTP" BType_Bool”,
                                    “BExp_Den
                                       (BVar "49_otp" (BType_Imm Bit64))”),
                                   VNode
                                    ((“BVar "48_OTP" BType_Bool”,
                                      “BExp_Den
                                         (BVar "49_otp" (BType_Imm Bit64))”),
                                     VNode
                                      ((“BVar "50_T" BType_Bool”,
                                        “BExp_Den
                                           (BVar "49_otp" (BType_Imm Bit64))”),
                                       VNode
                                        ((“BVar "51_assert_true_cnd"
                                             BType_Bool”,
                                          “BExp_BinPred BIExp_Equal
                                             (BExp_BinExp BIExp_And
                                                (BExp_Den
                                                   (BVar "5_tmp_SP_EL0"
                                                      (BType_Imm Bit64)))
                                                (BExp_Const (Imm64 7w)))
                                             (BExp_Const (Imm64 0w))”),
                                         VNode
                                          ((“BVar "53_assert_true_cnd"
                                               BType_Bool”,
                                            “BExp_BinExp BIExp_And
                                               (BExp_BinPred
                                                  BIExp_LessOrEqual
                                                  (BExp_BinExp BIExp_Plus
                                                     (BExp_Den
                                                        (BVar "5_tmp_SP_EL0"
                                                           (BType_Imm Bit64)))
                                                     (BExp_Const (Imm64 48w)))
                                                  (BExp_Const
                                                     (Imm64
                                                        0xFFFFFFFFFFFFFFF7w)))
                                               (BExp_BinExp BIExp_And
                                                  (BExp_BinExp BIExp_Or
                                                     (BExp_BinPred
                                                        BIExp_LessThan
                                                        (BExp_Const
                                                           (Imm64 0w))
                                                        (BExp_BinExp
                                                           BIExp_Plus
                                                           (BExp_Den
                                                              (BVar
                                                                 "5_tmp_SP_EL0"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64 48w))))
                                                     (BExp_BinPred
                                                        BIExp_LessOrEqual
                                                        (BExp_BinExp
                                                           BIExp_Plus
                                                           (BExp_Const
                                                              (Imm64 8w))
                                                           (BExp_BinExp
                                                              BIExp_Plus
                                                              (BExp_Den
                                                                 (BVar
                                                                    "5_tmp_SP_EL0"
                                                                    (BType_Imm
                                                                       Bit64)))
                                                              (BExp_Const
                                                                 (Imm64 48w))))
                                                        (BExp_Const
                                                           (Imm64 0w))))
                                                  (BExp_BinExp BIExp_Or
                                                     (BExp_BinPred
                                                        BIExp_LessThan
                                                        (BExp_BinExp
                                                           BIExp_Plus
                                                           (BExp_Den
                                                              (BVar
                                                                 "5_tmp_SP_EL0"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64 48w)))
                                                        (BExp_Const
                                                           (Imm64 0w)))
                                                     (BExp_BinPred
                                                        BIExp_LessOrEqual
                                                        (BExp_Const
                                                           (Imm64 0xFFFFFFFFw))
                                                        (BExp_BinExp
                                                           BIExp_Plus
                                                           (BExp_Den
                                                              (BVar
                                                                 "5_tmp_SP_EL0"
                                                                 (BType_Imm
                                                                    Bit64)))
                                                           (BExp_Const
                                                              (Imm64 48w))))))”),
                                           VNode
                                            ((“BVar "56_assert_true_cnd"
                                                 BType_Bool”,
                                              “BExp_BinPred BIExp_Equal
                                                 (BExp_BinExp BIExp_And
                                                    (BExp_Den
                                                       (BVar "5_tmp_SP_EL0"
                                                          (BType_Imm Bit64)))
                                                    (BExp_Const (Imm64 7w)))
                                                 (BExp_Const (Imm64 0w))”),
                                             VNode
                                              ((“BVar "59_assert_true_cnd"
                                                   BType_Bool”,
                                                “BExp_BinPred BIExp_Equal
                                                   (BExp_BinExp BIExp_And
                                                      (BExp_Den
                                                         (BVar "5_tmp_SP_EL0"
                                                            (BType_Imm Bit64)))
                                                      (BExp_Const (Imm64 7w)))
                                                   (BExp_Const (Imm64 0w))”),
                                               VNode
                                                ((“BVar "62_assert_true_cnd"
                                                     BType_Bool”,
                                                  “BExp_BinPred BIExp_Equal
                                                     (BExp_BinExp BIExp_And
                                                        (BExp_Den
                                                           (BVar
                                                              "5_tmp_SP_EL0"
                                                              (BType_Imm
                                                                 Bit64)))
                                                        (BExp_Const
                                                           (Imm64 7w)))
                                                     (BExp_Const (Imm64 0w))”),
                                                 VNode
                                                  ((“BVar "66_Conc1"
                                                       BType_Bool”,
                                                    “conc1
                                                       (BVar "48_OTP"
                                                          (BType_Imm Bit64))”),
                                                   VNode
                                                    ((“BVar "70_XOR"
                                                         BType_Bool”,
                                                      “exclusive_or
                                                         (BVar "66_Conc1"
                                                            (BType_Imm Bit64))
                                                         (BVar "69_pad"
                                                            (BType_Imm Bit64))”),
                                                     VNode
                                                      ((“BVar "73_Kr"
                                                           BType_Bool”,
                                                        “BVar "70_XOR"
                                                           (BType_Imm Bit64)”),
                                                       VNode
                                                        ((“BVar
                                                             "75_assert_true_cnd"
                                                             BType_Bool”,
                                                          “BExp_BinPred
                                                             BIExp_Equal
                                                             (BExp_BinExp
                                                                BIExp_And
                                                                (BExp_Den
                                                                   (BVar
                                                                      "5_tmp_SP_EL0"
                                                                      (BType_Imm
                                                                         Bit64)))
                                                                (BExp_Const
                                                                   (Imm64 7w)))
                                                             (BExp_Const
                                                                (Imm64 0w))”),
                                                         VNode
                                                          ((“BVar
                                                               "77_assert_true_cnd"
                                                               BType_Bool”,
                                                            “BExp_BinExp
                                                               BIExp_And
                                                               (BExp_BinPred
                                                                  BIExp_LessOrEqual
                                                                  (BExp_BinExp
                                                                     BIExp_Plus
                                                                     (BExp_Den
                                                                        (BVar
                                                                           "5_tmp_SP_EL0"
                                                                           (BType_Imm
                                                                              Bit64)))
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           56w)))
                                                                  (BExp_Const
                                                                     (Imm64
                                                                        0xFFFFFFFFFFFFFFF7w)))
                                                               (BExp_BinExp
                                                                  BIExp_And
                                                                  (BExp_BinExp
                                                                     BIExp_Or
                                                                     (BExp_BinPred
                                                                        BIExp_LessThan
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              0w))
                                                                        (BExp_BinExp
                                                                           BIExp_Plus
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "5_tmp_SP_EL0"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 56w))))
                                                                     (BExp_BinPred
                                                                        BIExp_LessOrEqual
                                                                        (BExp_BinExp
                                                                           BIExp_Plus
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 8w))
                                                                           (BExp_BinExp
                                                                              BIExp_Plus
                                                                              (BExp_Den
                                                                                 (BVar
                                                                                    "5_tmp_SP_EL0"
                                                                                    (BType_Imm
                                                                                       Bit64)))
                                                                              (BExp_Const
                                                                                 (Imm64
                                                                                    56w))))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              0w))))
                                                                  (BExp_BinExp
                                                                     BIExp_Or
                                                                     (BExp_BinPred
                                                                        BIExp_LessThan
                                                                        (BExp_BinExp
                                                                           BIExp_Plus
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "5_tmp_SP_EL0"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 56w)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              0w)))
                                                                     (BExp_BinPred
                                                                        BIExp_LessOrEqual
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              0xFFFFFFFFw))
                                                                        (BExp_BinExp
                                                                           BIExp_Plus
                                                                           (BExp_Den
                                                                              (BVar
                                                                                 "5_tmp_SP_EL0"
                                                                                 (BType_Imm
                                                                                    Bit64)))
                                                                           (BExp_Const
                                                                              (Imm64
                                                                                 56w))))))”),
                                                           VNode
                                                            ((“BVar
                                                                 "80_assert_true_cnd"
                                                                 BType_Bool”,
                                                              “BExp_BinPred
                                                                 BIExp_Equal
                                                                 (BExp_BinExp
                                                                    BIExp_And
                                                                    (BExp_Den
                                                                       (BVar
                                                                          "5_tmp_SP_EL0"
                                                                          (BType_Imm
                                                                             Bit64)))
                                                                    (BExp_Const
                                                                       (Imm64
                                                                          7w)))
                                                                 (BExp_Const
                                                                    (Imm64 0w))”),
                                                             VNode
                                                              ((“BVar
                                                                   "83_assert_true_cnd"
                                                                   BType_Bool”,
                                                                “BExp_BinPred
                                                                   BIExp_Equal
                                                                   (BExp_BinExp
                                                                      BIExp_And
                                                                      (BExp_Den
                                                                         (BVar
                                                                            "5_tmp_SP_EL0"
                                                                            (BType_Imm
                                                                               Bit64)))
                                                                      (BExp_Const
                                                                         (Imm64
                                                                            7w)))
                                                                   (BExp_Const
                                                                      (Imm64
                                                                         0w))”),
                                                               VNode
                                                                ((“BVar
                                                                     "86_assert_true_cnd"
                                                                     BType_Bool”,
                                                                  “BExp_BinPred
                                                                     BIExp_Equal
                                                                     (BExp_BinExp
                                                                        BIExp_And
                                                                        (BExp_Den
                                                                           (BVar
                                                                              "5_tmp_SP_EL0"
                                                                              (BType_Imm
                                                                                 Bit64)))
                                                                        (BExp_Const
                                                                           (Imm64
                                                                              7w)))
                                                                     (BExp_Const
                                                                        (Imm64
                                                                           0w))”),
                                                                 VNode
                                                                  ((“BVar
                                                                       "90_assert_true_cnd"
                                                                       BType_Bool”,
                                                                    “BExp_BinPred
                                                                       BIExp_Equal
                                                                       (BExp_BinExp
                                                                          BIExp_And
                                                                          (BExp_Den
                                                                             (BVar
                                                                                "5_tmp_SP_EL0"
                                                                                (BType_Imm
                                                                                   Bit64)))
                                                                          (BExp_Const
                                                                             (Imm64
                                                                                7w)))
                                                                       (BExp_Const
                                                                          (Imm64
                                                                             0w))”),
                                                                   VLeaf))))))))))))))))))))))))))))))));
*)
