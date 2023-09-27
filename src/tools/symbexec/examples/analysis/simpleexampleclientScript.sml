open HolKernel Parse boolLib bossLib;

open birs_stepLib;
open birs_composeLib;
open birs_driveLib;
open birs_auxTheory;
open bir_backlifterTheory;
open simpleexampleTheory;

open bir_program_transfTheory;

val _ = new_theory "simpleexampleclient";

(*
val _ = print_term (concl bin_motor_func_thm);
*)


val birenvtyl_def = Define `
    birenvtyl = MAP BVarToPair (SET_TO_LIST arm8_vars)
`;


        
val bprog = List.nth((snd o strip_comb o concl) simpleexample_thm, 3);
(*
(hd o fst o listSyntax.dest_list o snd o dest_comb) bprog
(hd o tl o fst o listSyntax.dest_list o snd o dest_comb) bprog

List.nth ((fst o listSyntax.dest_list o snd o dest_comb) bprog, 13)
*)
val bprog_def = Define `
    bprog = ^(bprog)
`;
val bprog_tm = (fst o dest_eq o concl) bprog_def;
(* ........................... *)

(* client *)
val birs_state_init_lbl = (snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x40063Cw))``;
(*
val birs_stop_lbls = [``<|bpc_label := BL_Address (Imm64 0xb08w); bpc_index := 7|>``];
*)
val birs_stop_lbls = [((snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x400644w))``),((snd o dest_eq o concl o EVAL) ``bir_block_pc (BL_Address (Imm64 0x400650w))``)];



(* TODO: add a sanity check here that all the variables of the program are included in birenvtyl! *)

val birs_state_init = ``
  <|bsst_pc :=  ^birs_state_init_lbl;
    bsst_environ :=
      birs_gen_env
        [("SP_process",
          BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit64)))
            (BExp_Const (Imm64 8w)));
         ("MEM",
          BExp_Store
            (BExp_Store (BExp_Den (BVar "sy_MEM" (BType_Mem Bit64 Bit8)))
               (BExp_BinExp BIExp_Minus
                  (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit64)))
                  (BExp_Const (Imm64 8w))) BEnd_LittleEndian
               (BExp_Den (BVar "sy_R7" (BType_Imm Bit64))))
            (BExp_BinExp BIExp_Minus
               (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit64)))
               (BExp_Const (Imm64 4w))) BEnd_LittleEndian
            (BExp_Den (BVar "sy_LR" (BType_Imm Bit64))));
         ("countw",
          BExp_BinExp BIExp_Plus
            (BExp_Den (BVar "sy_countw" (BType_Imm Bit64)))
            (BExp_Const (Imm64 3w)));
         ("tmp_SP_process",
          BExp_BinExp BIExp_Minus
            (BExp_Den (BVar "sy_SP_process" (BType_Imm Bit64)))
            (BExp_Const (Imm64 8w)));
         ("ProcState_C",BExp_Den (BVar "sy_ProcState_C" (BType_Imm Bit1)));
         ("ProcState_N",BExp_Den (BVar "sy_ProcState_N" (BType_Imm Bit1)));
         ("ProcState_V",BExp_Den (BVar "sy_ProcState_V" (BType_Imm Bit1)));
         ("ProcState_Z",BExp_Den (BVar "sy_ProcState_Z" (BType_Imm Bit1)));
         ("SP_EL0",BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)));
         ("R30",BExp_Den (BVar "sy_R30" (BType_Imm Bit64)));
         ("R0",BExp_Den (BVar "sy_R0" (BType_Imm Bit64)));
         ("R1",BExp_Den (BVar "sy_R1" (BType_Imm Bit64)));
         ("R2",BExp_Den (BVar "sy_R2" (BType_Imm Bit64)));
         ("R3",BExp_Den (BVar "sy_R3" (BType_Imm Bit64)));
         ("R4",BExp_Den (BVar "sy_R4" (BType_Imm Bit64)));
         ("R5",BExp_Den (BVar "sy_R5" (BType_Imm Bit64)));
         ("R6",BExp_Den (BVar "sy_R6" (BType_Imm Bit64)));
         ("R7",BExp_Den (BVar "sy_R7" (BType_Imm Bit64)));
         ("R8",BExp_Den (BVar "sy_R8" (BType_Imm Bit64)));
         ("R9",BExp_Den (BVar "sy_R9" (BType_Imm Bit64)));
         ("R10",BExp_Den (BVar "sy_R10" (BType_Imm Bit64)));
         ("R11",BExp_Den (BVar "sy_R11" (BType_Imm Bit64)));
         ("R12",BExp_Den (BVar "sy_R12" (BType_Imm Bit64)));
         ("LR",BExp_Den (BVar "sy_LR" (BType_Imm Bit64)));
         ("SP_main",BExp_Den (BVar "sy_SP_main" (BType_Imm Bit64)));
         ("ModeHandler",BExp_Den (BVar "sy_ModeHandler" (BType_Imm Bit1)));
         ("tmp_PC",BExp_Den (BVar "sy_tmp_PC" (BType_Imm Bit64)));
         ("tmp_COND",BExp_Den (BVar "sy_tmp_COND" (BType_Imm Bit1)));
         ("tmp_MEM",BExp_Den (BVar "sy_tmp_MEM" (BType_Mem Bit64 Bit8)));
         ("tmp_PSR_C",BExp_Den (BVar "sy_tmp_PSR_C" (BType_Imm Bit1)));
         ("tmp_PSR_N",BExp_Den (BVar "sy_tmp_PSR_N" (BType_Imm Bit1)));
         ("tmp_PSR_V",BExp_Den (BVar "sy_tmp_PSR_V" (BType_Imm Bit1)));
         ("tmp_PSR_Z",BExp_Den (BVar "sy_tmp_PSR_Z" (BType_Imm Bit1)));
         ("tmp_R0",BExp_Den (BVar "sy_tmp_R0" (BType_Imm Bit64)));
         ("tmp_R1",BExp_Den (BVar "sy_tmp_R1" (BType_Imm Bit64)));
         ("tmp_R2",BExp_Den (BVar "sy_tmp_R2" (BType_Imm Bit64)));
         ("tmp_R3",BExp_Den (BVar "sy_tmp_R3" (BType_Imm Bit64)));
         ("tmp_R4",BExp_Den (BVar "sy_tmp_R4" (BType_Imm Bit64)));
         ("tmp_R5",BExp_Den (BVar "sy_tmp_R5" (BType_Imm Bit64)));
         ("tmp_R6",BExp_Den (BVar "sy_tmp_R6" (BType_Imm Bit64)));
         ("tmp_R7",BExp_Den (BVar "sy_tmp_R7" (BType_Imm Bit64)));
         ("tmp_R8",BExp_Den (BVar "sy_tmp_R8" (BType_Imm Bit64)));
         ("tmp_R9",BExp_Den (BVar "sy_tmp_R9" (BType_Imm Bit64)));
         ("tmp_R10",BExp_Den (BVar "sy_tmp_R10" (BType_Imm Bit64)));
         ("tmp_R11",BExp_Den (BVar "sy_tmp_R11" (BType_Imm Bit64)));
         ("tmp_R12",BExp_Den (BVar "sy_tmp_R12" (BType_Imm Bit64)));
         ("tmp_LR",BExp_Den (BVar "sy_tmp_LR" (BType_Imm Bit64)));
         ("tmp_SP_main",BExp_Den (BVar "sy_tmp_SP_main" (BType_Imm Bit64)));
         ("tmp_ModeHandler",
          BExp_Den (BVar "sy_tmp_ModeHandler" (BType_Imm Bit1)));
         ("tmp_countw",BExp_Den (BVar "sy_tmp_countw" (BType_Imm Bit64)))];
    bsst_status := BST_Running;
    bsst_pcond :=
          BExp_BinExp BIExp_And
             (BExp_BinPred BIExp_LessOrEqual (BExp_Const (Imm64 0x600000w))
                (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64))))
             (BExp_UnaryExp BIExp_Not
                (BExp_BinPred BIExp_Equal
                   (BExp_BinExp BIExp_And
                      (BExp_BinExp BIExp_Minus
                         (BExp_Den (BVar "sy_SP_EL0" (BType_Imm Bit64)))
                         (BExp_Const (Imm64 16w))) (BExp_Const (Imm64 3w)))
                   (BExp_Const (Imm64 0w))))
          |>
          ``;
    (*
val birs_state_init = ``<|
  bsst_pc       := ^birs_state_init_lbl;
  bsst_environ  := bir_senv_GEN_list birenvtyl;
  bsst_status   := BST_Running;
  bsst_pcond    := bir_exp_true
|>``;*)
(* TODO: probably need this later in the path condition: 
  ``BExp_UnaryExp BIExp_Not (BExp_Den (BVar "ModeHandler" BType_Bool))``;
 *)
(* ........................... *)

val birs_rule_STEP_thm = birs_rule_STEP_prog_fun (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_SUBST_thm = birs_rule_SUBST_prog_fun bprog_tm;
val birs_rule_STEP_fun_spec = (birs_rule_SUBST_trysimp_const_add_subst_fun birs_rule_SUBST_thm o birs_rule_tryjustassert_fun true o birs_rule_STEP_fun birs_rule_STEP_thm bprog_tm);
(* now the composition *)
val birs_rule_SEQ_thm = birs_rule_SEQ_prog_fun bprog_tm;
val birs_rule_SEQ_fun_spec = birs_rule_SEQ_fun birs_rule_SEQ_thm;
(* ........................... *)


val single_step_A_thm = birs_rule_STEP_fun_spec birs_state_init;
(* ........................... *)



(* and also the sequential composition *)
val birs_rule_STEP_SEQ_thm = MATCH_MP birs_rulesTheory.birs_rule_STEP_SEQ_gen_thm (bir_prog_has_no_halt_fun bprog_tm);
val birs_rule_STEP_SEQ_fun_spec = birs_rule_STEP_SEQ_fun (birs_rule_SUBST_thm, birs_rule_STEP_SEQ_thm);
(* ........................... *)


val tree = build_tree (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
val _ = print "done building the tree\n";


val _ = print "now reducing it to one sound structure\n";

val timer = bir_miscLib.timer_start 0;
val result = exec_until (birs_rule_STEP_fun_spec, birs_rule_SEQ_fun_spec, birs_rule_STEP_SEQ_fun_spec) single_step_A_thm birs_stop_lbls;
val _ = bir_miscLib.timer_stop (fn delta_s => print ("\n======\n > exec_until took " ^ delta_s ^ "\n")) timer;

val _ = (print_term o concl) result;

val _ = show_tags := true;
val _ = Portable.pprint Tag.pp_tag (tag result);



val _ = save_thm ("bin_small_example_analysis_thm", result);

val _ = export_theory();
