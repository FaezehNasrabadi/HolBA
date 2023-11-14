open HolKernel Parse

open binariesLib;
open binariesTheory;
open binariesCfgLib;
open binariesMemLib;
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_block_collectionLib;
open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_exec_typingLib;
open commonBalrobScriptLib;
open binariesDefsLib;
open bir_cfgLib;
open bir_cfg_m0Lib;
open bir_symbexec_driverLib;
open Redblackmap;
open bir_symbexec_oracleLib;
open sbir_treeLib;
open sapicplusTheory;
open sapicplusSyntax;
open translate_to_sapicTheory;
open rich_listTheory;
open translate_to_sapicLib;
open messagesTheory;
open messagesSyntax;
open tree_to_processLib;
open  sapic_to_fileLib;
(*Server*)   (*  
val lbl_tm = ``BL_Address (Imm64 4203632w)``;

val stop_lbl_tms = [``BL_Address (Imm64 4203760w)``];    
(*Client*)   *)  
val lbl_tm = ``BL_Address (Imm64 4203632w)``;

val stop_lbl_tms = [``BL_Address (Imm64 4203756w)``]; 

val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;


val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;
val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms adr_dict [];
val _ = print "\n\n";
val _ = print "finished exploration of all paths.\n\n";
val _ = print ("number of stopped symbolic execution states: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
    List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed)));
val _ = print "\n";     
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n";

    
val predlists = List.map (fn syst => ((rev o SYST_get_pred) syst))
                         systs_noassertfailed;

val tr = predlist_to_tree predlists;

val vals_list = bir_symbexec_treeLib.symb_execs_vals_term systs_noassertfailed [];
val sort_vals = bir_symbexec_sortLib.refine_symb_val_list vals_list;


val valtr =  tree_with_value tr sort_vals;

val _ = print "\n";     
val _ = print ("built a symbolic tree with value");
val _ = print "\n";
    
(*
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



val lst =
   [[
     “BVar "70_XOR" BType_Bool”,“BVar "51_assert_true_cnd" BType_Bool”]];
    
val tr = predlist_to_tree lst
val vals_list = bir_symbexec_treeLib.symb_execs_vals_term systs [];
val sort_vals = bir_symbexec_sortLib.refine_symb_val_list vals_list;
val valtr = tree_with_value tr sort_vals


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


val holtree = smltree_to_holtree valtr;
 
val symbtree_def = Define `
    symbtree = ^(holtree)
		    `;

val holtree = (snd o dest_eq o concl) symbtree_def;


(fst o dest_BVar_string) ``BVar "57_assert_false_cnd" BType_Bool``

(String.isSuffix "false_cnd"  ((fst o dest_BVar_string) a))
(String.isSuffix "event_false_cnd"  "60_event_false_cnd")
EVAL ``symbtree_to_sapic (^holtree)``
val a = “BVar "48_OTP" BType_Bool”
EVAL ``IS_SUFFIX ((FST o dest_BVar_string) BVar "57_assert_false_cnd" BType_Bool) "assert_true_cnd" ``
EVAL ``rich_list$IS_SUFFIX "51_assert_true_cnd" "assert_true_cnd"``
EVAL ``list$REV "57_assert_true_cnd" ""``
is_substring
 HOL_Interactive.toggle_quietdec();
open stringSyntax;
 HOL_Interactive.toggle_quietdec();
 
 *)


			 
val sapic_process = sbir_tree_sapic_process (purge_tree valtr);


val _ = print "\n";     
val _ = print ("sapic_process");
val _ = print "\n";
    
val _ =  ( write_sapic_to_file o process_to_string) sapic_process

val _ = print "\n";     
val _ = print ("wrote into file");
val _ = print "\n";
