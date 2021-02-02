open HolKernel Parse

open binariesLib;
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
     
val prog = ``BirProgram
      [<|bb_label :=
           BL_Address_HC (Imm32 2802w)
             "52800000 (mov w0, #0x0                    // #0)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit32))
              (BExp_Const (Imm32 0w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2804w)))|>;
        <|bb_label := BL_Address_HC (Imm32 2804w) "11000400 (add w0, w0, #0x1)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit32))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                        (BExp_Const (Imm32 1w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2808w)))|>;
       <|bb_label := BL_Address_HC (Imm32 2808w) "94000020 (bl 88 <.text+0x88>)";
         bb_statements :=
           [BStmt_Assign (BVar "R30" (BType_Imm Bit32))
              (BExp_Const (Imm32 2812w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2002w)))|>;
	<|bb_label := BL_Address_HC (Imm32 2812w) "2A0003E2 (mov w2, w0)";
         bb_statements :=
           [BStmt_Assign (BVar "R2" (BType_Imm Bit32))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit32))) Bit32) Bit32)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2816w)))|>;
	<|bb_label :=
           BL_Address_HC (Imm32 2816w)
             "52800121 (mov w1, #0x9                    // #9)";
         bb_statements :=
           [BStmt_Assign (BVar "R1" (BType_Imm Bit32))
              (BExp_Const (Imm32 9w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2820w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm32 2820w) "94000024 (bl a4 <.text+0xa4>)";
         bb_statements :=
           [BStmt_Assign (BVar "R30" (BType_Imm Bit32))
              (BExp_Const (Imm32 2824w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2202w)))|>;
       <|bb_label := BL_Address_HC (Imm32 2824w) "2A0003E3 (mov w3, w0)";
         bb_statements :=
           [BStmt_Assign (BVar "R3" (BType_Imm Bit32))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit32))) Bit32) Bit32)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2828w)))|>;
	<|bb_label :=
           BL_Address_HC (Imm32 2828w) "94000028 (bl 72 <.text+0x72>)";
         bb_statements :=
           [BStmt_Assign (BVar "R30" (BType_Imm Bit32))
              (BExp_Const (Imm32 2832w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm32 2w)))|>;

      ]``;
 
val bl_dict  = bir_block_collectionLib.gen_block_dict prog;
val prog_lbl_tms = bir_block_collectionLib.get_block_dict_keys bl_dict;
val prog_lbl_tms_0 = “BL_Address (Imm32 2802w)”;
val prog_vars = bir_exec_typingLib.gen_vars_of_prog prog;
val n_dict = bir_cfgLib.cfg_build_node_dict bl_dict prog_lbl_tms;
val stop_lbl_tms = [“BL_Address (Imm32 2816w)”];
    
val syst = init_state prog_lbl_tms_0 prog_vars;

val Fr_bv = get_bvar_fresh (bir_envSyntax.mk_BVar_string ("init", “BType_Imm Bit32”));
val bv = ``BVar "R0" (BType_Imm Bit32)``;
val deps = Redblackset.add (symbvalbe_dep_empty, bv);
val symbv = SymbValBE (Fr_bv,deps);
val syst = bir_symbexec_stateLib.insert_symbval bv symbv syst;

val pred_conjs =
   [``BExp_BinPred BIExp_Equal
                        (BExp_Den (BVar "R0" (BType_Imm Bit32)))
                        (BExp_Const (Imm32 0w))``];

val syst = state_add_preds "init_pred" pred_conjs syst;
val _ = print "initial state created.\n\n";

val cfb = false;

val systs = symb_exec_to_stop (commonBalrobScriptLib.abpfun cfb) n_dict bl_dict [syst] stop_lbl_tms [];
val _ = print "finished exploration of all paths.\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

val stop_lbl_tms = [“BL_Address (Imm32 2832w)”];
val systs = symb_exec_to_stop (commonBalrobScriptLib.abpfun cfb) n_dict bl_dict [syst] stop_lbl_tms systs;
val _ = print "finished exploration of all paths.\n";
val _ = print ("number of paths found: " ^ (Int.toString (length systs)));
val _ = print "\n\n";

    
val (systs_noassertfailed, systs_assertfailed) =
  List.partition (fn syst => not (identical (SYST_get_status syst) BST_AssertionViolated_tm)) systs;
val _ = print ("number of \"no assert failed\" paths found: " ^ (Int.toString (length systs_noassertfailed)));
val _ = print "\n\n";
(*Redblackmap.listItems bl_dict;*)
