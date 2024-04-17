open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open parallelcompositionconcreteTheory;
open interleavingconcreteTheory;
open parallelcompositiongeneraldeductionTheory;
open interleavinggeneraldeductionTheory;
open derived_rules_generaldeductionTheory;

val _ = new_theory "instantiations";

 (*

bir_inst_liftingTheory.bir_is_lifted_prog_def
“bir_is_lifted_prog arm8_bmr (WI_end 0w 0xFFFFFFFFw)
          [(0w,
            [255w; 67w; 0w; 209w; 224w; 7w; 0w; 249w; 225w; 3w; 0w; 249w;
             225w; 7w; 64w; 249w; 224w; 3w; 64w; 249w; 63w; 0w; 0w; 235w;
             41w; 2w; 0w; 84w; 225w; 3w; 64w; 249w; 224w; 3w; 1w; 170w; 0w;
             244w; 126w; 211w; 0w; 0w; 1w; 139w; 0w; 248w; 127w; 211w;
             224w; 3w; 0w; 249w; 225w; 3w; 64w; 249w; 224w; 3w; 1w; 170w;
             0w; 244w; 126w; 211w; 0w; 0w; 1w; 139w; 224w; 3w; 0w; 249w;
             225w; 3w; 64w; 249w; 224w; 7w; 64w; 249w; 32w; 124w; 0w; 155w;
             224w; 3w; 0w; 249w; 31w; 32w; 3w; 213w; 31w; 32w; 3w; 213w;
             255w; 67w; 0w; 145w; 192w; 3w; 95w; 214w])]
          (BirProgram
             [<|bb_label :=
                  BL_Address_HC (Imm64 0w) "D10043FF (sub sp, sp, #0x10)";
                bb_statements :=
                  [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 16w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>])”

"bir_backlifterTheory.exist_bir_of_arm8_thm"
bir_backlifterTheory.bir_pre_arm8_to_bir_def
bir_backlifterTheory.bir_post_bir_to_arm8_def
((
!ms.
?bs.
  (bir_envty_list_b birenvtyl st.bst_environ) /\
  bmr_rel (m0_mod_bmr (F,T)) bs ms
))
bir_lifting_machinesTheory.bmr_rec



((
``
!bprog bs n L bs'.
(step_n_in_L (\x. x.bst_pc) (bir_exec_step_state bprog) bs n L bs') ==>
  ?n' lo.
  (bir_exec_to_addr_label_n bprog bs n' = BER_Ended lo n n' bs')
``
))



bir_backlifterTheory.bir_post_bir_to_arm8_def
lift_contract_thm

bir_lifting_machinesTheory.bmr_rel_def

bir_backlifterTheory.bir_pre_arm8_to_bir_def
bir_backlifterTheory.bir_post_bir_to_arm8_def

bir_programTheory.bir_exec_steps_GEN_def  
val m0_mod_vars_def = Define `
    m0_mod_vars = bmr_vars (m0_mod_bmr (T,T))
`;

val m0_mod_vars_thm = store_thm(
   "m0_mod_vars_thm", ``
!ef sel.
  m0_mod_vars = bmr_vars (m0_mod_bmr (ef,sel))
``,
  METIS_TAC [m0_mod_vars_def, bir_lifting_machinesTheory.m0_mod_bmr_vars_EVAL]
);




  );*)
  
val _ = export_theory();

