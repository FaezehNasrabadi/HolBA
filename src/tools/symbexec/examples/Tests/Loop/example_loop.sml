HOL_Interactive.toggle_quietdec();
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
HOL_Interactive.toggle_quietdec();


fun mk_key_from_address64 i addr = (mk_BL_Address o bir_immSyntax.mk_Imm64 o wordsSyntax.mk_word) (addr, Arbnum.fromInt i);
(* build the cfg and update the basic blocks *)
val _ = print "Building node dict.\n";
open bir_cfgLib;
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict_ prog_lbl_tms_;
val entries = [mk_key_from_address64 64 (Arbnum.fromHexString "10080")];
val _ = print "Building cfg.\n";
val g1 = cfg_create "toy" entries n_dict bl_dict_;

 (* display the cfg *)
val _ = print "Display cfg.\n";
open bir_cfg_vizLib;
val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g1))) (#CFGG_nodes g1);
val _ = cfg_display_graph_ns ns;



fun print_list lst =
    List.map (fn x => print_term x) lst;


(* val loop_pattern = "CFGNT_Jump"^"CFGNT_Basic"^"CFGNT_Basic"^"CFGNT_CondJump"; *)
val node_type =  ref ([]: (string * term) list);
val loop_pattern = ["CFGNT_Jump","CFGNT_Basic","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

fun detect_loop (g:cfg_graph) entry visited =
  let
    val n = lookup_block_dict_value (#CFGG_node_dict g) entry "traverse_graph" "n";
    val targets = #CFGN_targets n;
    val n_type  = #CFGN_type n;
    val s_type = bir_cfgLib.toString n_type
    val _ = node_type:= !node_type@[(s_type, (#CFGN_lbl_tm n))];
    
    val targets_to_visit = List.filter (fn x => List.all (fn y => not (identical x y)) visited) targets;
    val result = List.foldr (fn (entry', visited') => detect_loop g entry' visited') (entry::visited) targets_to_visit;
  in result end;

val _ = node_type := [];
val _ =  detect_loop  g1 (hd (#CFGG_entries g1)) [];
!node_type;

fun get_range (trace1, pattern) =
    let fun toChar t =
	  case t of "CFGNT_Jump"     => "J"
		  | "CFGNT_CondJump" => "C"
		  | "CFGNT_Halt"     => "H"
		  | "CFGNT_Basic"    => "B"
		  | "CFGNT_Call"     => "L"
		  | "CFGNT_Return"   => "R"

	fun index (str: string, substr: string) : int option =
	    let
		fun loop  (i: int) =
		    let val subt = ((String.size str) - (String.size substr))
		    in
			if (i > subt) then
			    NONE
			else if String.isSubstring (String.substring(str, i, (String.size substr))) substr then
			    SOME i
			else
			    loop (i + 1)
		    end
	    in
		loop 0
	    end
	val tc = List.foldr (fn (x, y) => x^y ) "" (List.map (fn x => toChar (fst x)) trace1)
	val _ = print tc
	val _ = print "\n"
	val pc = List.foldr (fn (x, y) => x^y ) "" (List.map (fn x => toChar x) pattern)
	val _ = print pc
	val _ = print "\n"
    in
	index(tc, pc)
    end
(*
val str = "BBBBBBBBBBBBBBBBBBBBBJBBBCBBBBBBCBBBBBBBBCBBJBJ";
val substr = "JBBBC";
val i = 21;*)
    
val in_loop = get_range(!node_type, loop_pattern);    

val entry_adr = snd (List.nth (!node_type, ((valOf in_loop)+((List.length loop_pattern)-1))));

fun next_pc lbl_tm =
    let
	val wpc = (bir_immSyntax.dest_Imm64 o dest_BL_Address) lbl_tm;
	val incpc = (rhs o concl o EVAL o wordsSyntax.mk_word_add) (wpc,``4w:word64``);
	val tgt = (mk_BL_Address o bir_immSyntax.mk_Imm64) incpc;
    in
	tgt
    end;

val exit_adr = next_pc entry_adr;
    
val _ = print "Address of entry node to loop :\n"    

val _ = print_term entry_adr;   

val _ = print "Address of exit node from loop :\n"    

val _ = print_term exit_adr;      
    
