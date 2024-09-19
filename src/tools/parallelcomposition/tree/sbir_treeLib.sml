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
	  val hdOfFirstList = hd lst
	  val result = ((List.map (fn ls => if (is_true (identical (hd hdOfFirstList) (hd ls))) then true else raise ERR "" "") lst) handle _ => [false]);
      in
	  if (is_false (hd result))
	  then false
	  else true
      end
  else false;
 

(* Define a datatype for trees *)
datatype 'a tree = Leaf | Node of 'a * 'a tree | Branch of 'a * 'a tree * 'a tree;

(* Helper function to check if all lists in a list are empty *)
fun all_empty lsts = List.all null lsts

(* Helper function to check if a list is not empty *)
fun not_empty ls = not (null ls)

fun prtion (lst: term list list) = case lst of
				       ([]: term list list) => ([], [])
				     | ([[]]: term list list) => ([], [])
				     | ((h::_): term list list) => 
				       let
					   val head_val = ((hd h):term)  (* Get the head of the first non-empty sublist *)
				       in
					   (* Partition all sublists based on whether their head matches head_val *)
					   List.partition (fn (ls: term list) => (identical (hd ls) head_val)) lst
				       end		   
(* Main function to convert predicate lists to tree *)
fun predlist_to_tree ([[]]: term list list) = Leaf
  | predlist_to_tree ([]: term list list) = Leaf
  | predlist_to_tree (lsts: term list list) =    
    if all_empty lsts then Leaf
    else
      let
        (* Partition the lists into empty and non-empty *)
          val (empty, notempty) = List.partition null lsts

          (* Partition the non-empty lists by the head element *)
          val (head_eq, head_noteq) = prtion notempty;
      in    
	      if null head_noteq then
		  let
		      val (head_tleq, head_tlnoteq) = (prtion (List.map (fn ls => (tl ls)) head_eq))handle _ => raise ERR "predlist_to_tree" ("cannot do it "^(String.concat(List.map (fn ls => ("|n"^((int_to_string o List.length) ls))) head_eq)));
		  in
		      if null head_tlnoteq then
			  Node (hd (hd head_eq), predlist_to_tree (List.map tl head_eq))
		      else
			  (* Create a Branch using the equal head before head_eq and head_noteq split *)
			  Branch (
			  (* The head we branch on is the common head of head_eq and head_noteq *)
			  hd (hd head_eq),
			  (* Left subtree for paths that match the head *)
			  predlist_to_tree head_tleq,
			  (* Right subtree for paths that have a different head *)
			  predlist_to_tree head_tlnoteq
			  )
		  end
	      else
		  raise ERR "predlist_to_tree" "heads not equal"
		  
      end 

	 
(*
tl [2]
val P1 = [“"f1"”,“"f3"”, “"f4"”, “"f5"”];
val P2 = [“"f1"”, “"f6"”, “"f7"”, “"f8"”];
val P3 = [“"f1"”, “"f6"”, “"f7"”, “"f9"”];
val lsts= [P1,P2,P3]	 

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
*)
(*SymbValBE (bv, _)
val bv = “BVar "sy_R30" (BType_Imm Bit64)”
Redblackset.empty Term.compare
*)	
(*Find bir expression*)
fun find_be_val vals_list bv =
    let
	val find_val = List.find (fn (a,_) => Term.term_eq a bv) vals_list;
	(* val symbv = ((snd o Option.valOf) find_val) handle _ => raise ERR "find_be_val" ("cannot find symbolic value for "^(term_to_string bv)^"\n"); *)
	val (bv_str, _) = bir_envSyntax.dest_BVar_string bv;
	val fr = get_bvar_fresh (bir_envSyntax.mk_BVar_string (bv_str, “BType_Imm Bit64”)); (* generate a fresh variable *)
	val symbv = ((snd o Option.valOf) find_val) handle _ => SymbValBE (fr, Redblackset.empty Term.compare) ;
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



(* fun cfg_tree tr = *)
(*     case tr of *)
(* 	VLeaf =>  *)
(*       | VNode ((bv,be), subtr) =>  *)
(*       | VBranch ((bv,be), subtr1, subtr2) =>  *)
					     
end (* local *)

end (* struct *)
