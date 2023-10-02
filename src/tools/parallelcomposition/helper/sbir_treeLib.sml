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


  val ERR      = Feedback.mk_HOL_ERR "sbir_treeLib"
  val wrap_exn = Feedback.wrap_exn   "sbir_treeLib"
in



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

(*
val a = rev(SYST_get_pred (List.nth (systs, 1)));
val b = rev(SYST_get_pred (List.nth (systs, 3)));
val c = listsToTree a b;
    
val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst))
                         systs;
 *)
    
fun allHeadsEqual ([]: term list list) = false
| allHeadsEqual (lst: term list list) =
  let
    val hdOfFirstList = hd lst
    fun compareHeads ([]: term list list) = true
      | compareHeads ((h: term list)::t) = if (identical (hd hdOfFirstList) (hd h)) then compareHeads t else false
  in
    compareHeads lst
  end;


fun HeadsEqual ([]: term list) = false
| HeadsEqual (lst: term list) =
  let
    val hdOfFirstList = hd lst
    fun compareHeads ([]: term list) = true
      | compareHeads ((h: term)::t) = if (identical hdOfFirstList h) then compareHeads t else false
  in
    compareHeads lst
  end;    


(*
val lst =[  [
     “BVar "31_assert_true_cnd" BType_Bool”,
     “BVar "34_assert_true_cnd" BType_Bool”,
     “BVar "39_assert_true_cnd" BType_Bool”,
     “BVar "44_assert_true_cnd" BType_Bool”, “BVar "48_OTP" BType_Bool”,
     “BVar "48_OTP" BType_Bool”, “BVar "50_T" BType_Bool”,
     “BVar "51_assert_true_cnd" BType_Bool”,
     “BVar "54_assert_false_cnd" BType_Bool”],
    [“BVar "31_assert_true_cnd" BType_Bool”,
     “BVar "34_assert_true_cnd" BType_Bool”,
     “BVar "39_assert_true_cnd" BType_Bool”,
     “BVar "44_assert_true_cnd" BType_Bool”, “BVar "48_OTP" BType_Bool”,
     “BVar "48_OTP" BType_Bool”, “BVar "50_T" BType_Bool”,
     “BVar "51_assert_true_cnd" BType_Bool”,
     “BVar "53_assert_true_cnd" BType_Bool”,
     “BVar "57_assert_false_cnd" BType_Bool”]];
    
val smltree = predlist_to_tree lst;

*)
    
fun predlist_to_tree ([[]]: term list list) = Leaf
  | predlist_to_tree (lst: term list list) =    
    if allHeadsEqual lst then
	Node ((hd (hd lst)), (predlist_to_tree (List.map (fn ls => (tl ls)) lst)))
    else
	(let val (head_noteq, head_eq) = List.partition (HeadsEqual) lst in
	    Branch ((predlist_to_tree head_noteq),(predlist_to_tree head_eq))	
	end)

(* define a symbolic tree hol datatype *)
val _ = Datatype `stree =
SLeaf
| SNode 'a stree
| SBranch stree stree
	  `;

fun smltree_to_holtree tree =
    case tree of
        Leaf => mk_const ("SLeaf",``:bir_var_t stree``)
      | Node (a, subtree) => mk_comb (mk_comb (mk_const ("SNode",``:bir_var_t -> bir_var_t stree -> bir_var_t stree``), a), smltree_to_holtree subtree)
      | Branch (lsubtree, rsubtree) => mk_comb (mk_comb (mk_const ("SBranch",``:bir_var_t stree -> bir_var_t stree -> bir_var_t stree``), smltree_to_holtree lsubtree), smltree_to_holtree rsubtree);

(*
val holtree = smltree_to_holtree smltree;
 
val symbtree_def = Define `
    symbtree = ^(holtree)
`;
*)

end (* local *)

end (* struct *)
