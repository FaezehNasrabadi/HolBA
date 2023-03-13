(* HOL_Interactive.toggle_quietdec(); *)
open HolKernel Parse

open binariesLib;
open binariesTheory;
open binariesCfgLib;
open binariesMemLib;
open bir_symbexec_stateLib;
open bir_symbexec_coreLib;
open bir_symbexec_stepLib;
open bir_symbexec_sumLib;
open bir_countw_simplificationLib;
open bir_block_collectionLib;
open bir_programSyntax;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_exec_typingLib;
open commonBalrobScriptLib;
open binariesDefsLib;
open bir_cfgLib;
open bir_cfg_m0Lib;
open bir_symbexec_driverLib;
open Redblackmap;
open bir_symbexec_oracleLib;
open bir_symbexec_loopLib;
(* HOL_Interactive.toggle_quietdec(); *)

(******Start******)
(*


val lbl_tm = ``BL_Address (Imm64 4201404w)``;

val stop_lbl_tms = [``BL_Address (Imm64 4201696w)``];
    
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;

(* val ns = List.map (fn x => snd x)(listItems n_dict); *)
(* val _ =  bir_cfg_vizLib.cfg_display_graph_ns ns; *)

val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;
(* val b = Redblackmap.find(adr_dict,“BL_Address (Imm64 4235844w)”); 
    listItems adr_dict
    val n = valOf (peek (n_dict, “BL_Address (Imm64 4235844w)”));*)
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;
val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms adr_dict [];

val _ = print "\n\n";
val _ = print "finished exploration of all paths.\n\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";
val _ = print ("number of \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed)));
val _ = print "\n\n";
*)  
 (*************)
  
val lbl_tm = ``BL_Address (Imm64 4209952w)``;
val stop_lbl_tms = [``BL_Address (Imm64 4212628w)``];

val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;

val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

val loop_pattern = ["CFGNT_Call","CFGNT_CondJump","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

val enter = find_loop n_dict adr_dict [lbl_tm] loop_pattern;

val adr_dict = Redblackmap.insert(adr_dict,enter,"loop"); 
    
(* 
val exit_adr = bir_symbexec_loopLib.next_pc enter;
List.foldr
List.exists
List.map
List.filter
::List.all
val g1 = cfg_create "toy" [lbl_tm] n_dict bl_dict_;
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g1))) (#CFGG_nodes g1);
val _ = bir_cfg_vizLib.cfg_display_graph_ns ns;
	      

val b = Redblackmap.find(adr_dict,“BL_Address (Imm64 4235844w)”); 
    listItems adr_dict
    val n = valOf (peek (n_dict, “BL_Address (Imm64 4235844w)”));*)
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [``bir_exp_true``];
    
val syst = state_add_preds "init_pred" pred_conjs syst;

val _ = print "initial state created.\n\n";

val cfb = false;
val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_ [syst] stop_lbl_tms adr_dict [];
    
val _ = print "\n\n";
val _ = print "finished exploration of all paths.\n\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";
val _ = print ("number of \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed)));
val _ = print "\n\n";
    (*
val b = [];
val systs =  List.map (fn s => if (identical ``BVar "sy_key" (BType_Imm Bit64)`` (find_bv_val "err" (SYST_get_env s) ``BVar "key" (BType_Imm Bit64)``)) then b else s::b) systs_noassertfailed;
val _ =  List.map (fn s => print_term (find_bv_val "err" (SYST_get_env s) ``BVar "key" (BType_Imm Bit64)``)) (concat systs);
    open List;*)
(************)
    
val lbl_tm = ``BL_Address (Imm64 4204336w)``;
val stop_lbl_tms = [``BL_Address (Imm64 4206916w)``];
val b = [];
val systs =  List.map (fn s => if (identical ``BVar "sy_key" (BType_Imm Bit64)`` (find_bv_val "err" (SYST_get_env s) ``BVar "key" (BType_Imm Bit64)``)) then b else s::b) systs;
val systs = [((hd o rev)(List.concat systs))];
val systs =  List.map (fn s => SYST_update_pc lbl_tm s) systs;
(*we need to find the right pattern*)
val loop_pattern = ["CFGNT_Call","CFGNT_CondJump","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

val enter = find_loop n_dict adr_dict [lbl_tm] loop_pattern;

val adr_dict = Redblackmap.insert(adr_dict,enter,"loop");
    
(* val syst = SYST_update_pred [] (SYST_update_status BST_Running_tm (SYST_update_pc lbl_tm ((hd o rev)systs))); *)
(* val syst = state_add_preds "init_pred" pred_conjs syst;  *)   
val systs = symb_exec_to_stop (abpfun cfb) n_dict bl_dict_  systs stop_lbl_tms adr_dict systs;
val _ = print "\n\n";
val _ = print "finished exploration of all paths.\n\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";
val _ = print ("number of \"assert failed\" paths found: " ^ (Int.toString (length systs_assertfailed)));
val _ = print "\n\n";

   
val Acts = bir_symbexec_treeLib.sym_exe_to_IML systs_noassertfailed;
(*
val b = listItems (SYST_get_env ((hd o rev) systs))
val b = listItems (SYST_get_vals ((hd o rev)systs))
val syst = (hd o rev)systs;
val be = “BVar "R1" (BType_Imm Bit64)”;
val be_r = (bir_symbexec_funcLib.symbval_bexp o get_state_symbv " vals not found " be) syst;

open binariesCfgVizLib;
open binariesDefsLib;
val _ = show_cfg_fun false  bl_dict_ n_dict "packet_kexdh";

val m = "D63F0060 (blr x3)"
((((isPrefix "(bl ") o implode o snd o (list_split_pred #" ") o explode) m) orelse  (((isPrefix "(blr ") o implode o snd o (list_split_pred #" ") o explode) m)) 
val n =  m
    open bir_auxiliaryLib;
open String;
((isPrefix "(blr ") o implode o snd o (list_split_pred #" ") o explode) m 

open graphVizLib;
val nodes = [(0,node_shape_default,[("id","abc"),("len","12")]),
             (1,node_shape_default,[("id","def"),("len","22")]),
             (2,node_shape_point,[]),
             (3,node_shape_circle,[("id","???")]),
             (4,node_shape_default,[("id","aaa")]),
             (5,node_shape_default,[("id","bbb")])];
val edges = [(2,0),
             (0,4),
             (4,5),
             (5,1),
             (1,1),
             (1,3)];


val (nodes, edges) = simplify_graph (nodes, edges);

val file = "test";
val dot_str = gen_graph (nodes, edges);
val _ = writeToFile dot_str (file ^ ".dot");
val _ = convertAndView file;

*)
