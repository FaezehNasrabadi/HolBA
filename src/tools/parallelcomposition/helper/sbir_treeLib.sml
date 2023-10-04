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
(* Define a datatype for trees *)
datatype 'a tree = Leaf | Node of 'a * 'a tree | Branch of 'a * 'a tree * 'a tree;

	 
fun predlist_to_tree ([[]]: term list list) = Leaf
  | predlist_to_tree (lst: term list list) =    
    if allHeadsEqual lst then
	Node ((hd (hd lst)), (predlist_to_tree (List.map (fn ls => (tl ls)) lst)))
    else
	(let val (head_noteq, head_eq) = List.partition (HeadsEqual) lst in
	    Branch ((hd (hd head_eq)),(predlist_to_tree (List.map (fn ls => (tl ls)) head_eq)),(predlist_to_tree (List.map (fn ls => (tl ls)) head_noteq)))	
	 end)



(*Find bir expression*)
fun find_be_val vals_list bv =
    let
	val find_val = List.find (fn (a,_) => Term.term_eq a bv) vals_list;
	val symbv = ((snd o Option.valOf) find_val) handle _ => raise ERR "find_be_val" "cannot find symbolic value";
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




(* define a symbolic tree hol datatype *)
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


				       
(*

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
