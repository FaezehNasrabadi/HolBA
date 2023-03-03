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
(*
void build_decoding_table(){}
 *)
     
val lbl_tm = ``BL_Address (Imm64 66228w)``;

val stop_lbl_tms = [``BL_Address (Imm64 66352w)``];

    
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;
val g1 = cfg_create "toy" [lbl_tm] n_dict bl_dict_;
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g1))) (#CFGG_nodes g1);
val _ = bir_cfg_vizLib.cfg_display_graph_ns ns;
	      
val loop_pattern = ["CFGNT_Jump","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

val enter = find_loop n_dict [lbl_tm] loop_pattern;

val adr_dict = bir_symbexec_PreprocessLib.fun_addresses_dict bl_dict_ prog_lbl_tms_;

val adr_dict = Redblackmap.insert(adr_dict,enter,"loop"); 
    
val syst = init_state lbl_tm prog_vars;

val pred_conjs = [];
    
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

open listSyntax;
val prog_def = Define `
prog
BirProgram
             [<|bb_label :=
                  BL_Address_HC (Imm64 65624w)
                    "97FFFFEA (bl 10000 <malloc>)";
                bb_statements :=
                  [BStmt_Assign (BVar "R30" (BType_Imm Bit64))
                     (BExp_Const (Imm64 65628w))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 65536w)))|>]`; 

val (first_block_label_tm, stmt, bbes) = (dest_bir_block o hd o fst o listSyntax.dest_list o dest_BirProgram o snd o dest_comb o concl) prog_def;




val stmt = “[BStmt_Assign (BVar "R30" (BType_Imm Bit64)) (BExp_Const (Imm64 66400w))]”;

((dest_BStmt_Assign o hd o fst o listSyntax.dest_list) stmt
(((is_BStmt_Assign  o hd o fst o listSyntax.dest_list) stmt) andalso (identical ((fst o dest_BStmt_Assign o hd o fst o listSyntax.dest_list) stmt) “BVar "R30" (BType_Imm Bit64)”))






(fst o dest_comb) stmt



val stmt =``[BStmt_Assign (BVar "R30" (BType_Imm Bit64))
                     (BExp_Const (Imm64 65628w))]``;
val bbes = “BStmt_Jmp (BLE_Label (BL_Address (Imm64 65536w)))”;
if (identical ((fst o dest_BStmt_Assign o hd) stmt) “BVar "R30" (BType_Imm Bit64)”)
		   then (CFGNT_Call [((mk_BL_Address o bir_expSyntax.dest_BExp_Const o snd o dest_BStmt_Assign o hd) stmt)],(((mk_BL_Address o bir_expSyntax.dest_BExp_Const o snd o dest_BStmt_Assign o hd) stmt)::(cfg_BLEs_to_targets [dest_BStmt_Jmp bbes])))
		   else (CFGNT_Basic,cfg_BLEs_to_targets [dest_BStmt_Jmp bbes])
val target = (dest_BStmt_Assign o hd) t;
if (identical ((fst o dest_BStmt_Assign o hd) t) “BVar "R30" (BType_Imm Bit64)”)
then ((mk_BL_Address o bir_expSyntax.dest_BExp_Const o snd o dest_BStmt_Assign o hd) t)::[“BL_Address (Imm64 65536w)”]
val t = “[]”;
val (l,r) = dest_comb stmt;
(snd o dest_comb o concl) stmt
(snd o dest_eq o (concl o fst o dest_comb) stmt
val Acts = bir_symbexec_treeLib.sym_exe_to_IML [(List.nth (systs_noassertfailed, 1))];

val a =listItems( SYST_get_env (List.nth (systs_noassertfailed, 0)));
val b =listItems( SYST_get_vals (List.nth (systs_noassertfailed, 0)));
val c = List.map (fn x => ( snd) x) b;
val d = List.map (fn SymbValBE(x,y) => (Redblackset.listItems y)) c;    

val Acts = bir_symbexec_treeLib.sym_exe_to_IML systs_noassertfailed;
val a =listItems( SYST_get_env ((hd o rev) systs));
val b =listItems( SYST_get_vals (List.nth (systs, 6)));
val c = List.map (fn x => ( snd) x) b;
val d = List.map (fn SymbValBE(x,y) => (Redblackset.listItems y)) c;
	     
*)
