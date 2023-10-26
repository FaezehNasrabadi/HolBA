open HolKernel Parse boolLib bossLib;

open pred_setTheory;
open bir_programTheory;
open HolBACoreSimps;
open sbir_treeTheory;
open sapicplusTheory;


val _ = new_theory "birs_eventstep";

(*
val _ = new_constant("Rfun", ``:sbir_environment_t -> bir_var_t``);
val _ = new_constant("Oracle", ``:sbir_environment_t -> bir_var_t``);
val _ = new_constant("birs_exec_step", ``:((sbir_pc_t,sbir_environment_t) stree) -> (sbir_pc_t#sbir_environment_t) -> ((sbir_pc_t#sbir_environment_t) -> bool)``);
    
(* calculate next label *)
val calculate_next_label_def  =
Define `
       calculate_next_label (((BL_Address (Imm32 w))): bir_label_t) =
       (BL_Address (Imm32 (word_add w (4w:word32))))
           `;

(* update pc by its label + 4w *)          
val birs_next_bsst_pc_def = Define `
   birs_next_bsst_pc pc = pc with bpc_label updated_by calculate_next_label`;

(* symbolic execution step for event functions *)    
val birs_exec_event_fun_def =
Define `
       birs_exec_event_fun (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (Event e) =
if ((st ∈ (STATES t)) ∧ (e NOTIN ((symb_env_dom o SND) st)) ∧ ((FST st) = PC_Event))
then {(PC_Normal,(SND st))}
else {}
`;
                                                                  
                                                                      
(* symbolic execution step for RNG functions *)    
val birs_exec_rng_fun_def =
Define `
       birs_exec_rng_fun (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (Sync_Fr n) =
if ((st ∈ (STATES t)) ∧ (n NOTIN ((symb_env_dom o SND) st)) ∧ (n = (Rfun (SND st))) ∧ ((FST st) = PC_Fr))
then
    {(PC_Normal,(symb_env_update (SND st) ((BVar "RNG" (BType_Imm Bit64)), SOME (BExp_Den n))))}
else {}
`;    


(* symbolic execution step for Crypto functions *)    
val birs_exec_crypto_fun_def =
Define `
       birs_exec_crypto_fun (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (Crypto v) =
if ((st ∈ (STATES t)) ∧ (v NOTIN ((symb_env_dom o SND) st)) ∧ (v = (Oracle (SND st))) ∧ ((FST st) = PC_Cr))
then
    {(PC_Normal,(symb_env_update (SND st) ((BVar "crypto" (BType_Imm Bit64)), SOME (BExp_Den v))))}
else {}
     `;
     

(* symbolic execution step for Input functions *)    
val birs_exec_in_fun_def =
Define `
       birs_exec_in_fun (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (A2P r) =
if ((st ∈ (STATES t)) ∧ (r NOTIN ((symb_env_dom o SND) st)) ∧ ((FST st) = PC_In))
then
    {(PC_Normal,(symb_env_update (SND st) ((BVar "Adv" (BType_Imm Bit64)), SOME (BExp_Den r))))}
else {}
     `;
    
(* symbolic execution step for Output functions *)    
val birs_exec_out_fun_def =
Define `
       birs_exec_out_fun (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (P2A s) =
if ((st ∈ (STATES t)) ∧ ((SOME (BExp_Den s)) = (symb_env_get (SND st) (BVar "R0" (BType_Imm Bit64)))) ∧ ((FST st) = PC_Out))
then {(PC_Normal,(SND st))}
else {}
`; 
 
(* symbolic execution step for Loops *)    
val birs_exec_loop_def =
Define `
       birs_exec_loop (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (Loop t') =
if ((st ∈ (STATES t)) ∧ (t' NOTIN ((symb_env_dom o SND) st)) ∧ ((FST st) = PC_Loop))
then {(PC_Normal,(SND st))}
else {}
     `;

(* symbolic execution step for Loops *)    
val birs_exec_branch_def =
Define `
       birs_exec_branch (t:(sbir_pc_t,sbir_environment_t) stree) (st:(sbir_pc_t#sbir_environment_t)) (Branch v) =
if ((st ∈ (STATES t)) ∧ ((FST st) = PC_Branch))
then {(PC_Normal,(SND st))}∪{(PC_Normal,(SND st))}
else {}
     `;

(* symbolic execution single-step labeled transition *)     
val birs_exec_event_step_def = Define `
    birs_exec_event_step (t:(sbir_pc_t,sbir_environment_t) stree) (state:(sbir_pc_t#sbir_environment_t)) event states =
  case event of
    | NONE                   => (birs_exec_step t state states) (* normal steps *)
    | SOME ( (Event e))   => (birs_exec_event_fun t state (Event e) states) (* event functions *)
    | SOME ( (Crypto v))  => (birs_exec_crypto_fun t state (Crypto v) states) (* Crypto functions *)
    | SOME ( (Loop t'))   => (birs_exec_loop t state (Loop t') states) (* Loops *)
    | SOME ( (Branch v))    => (birs_exec_branch t state (Branch v) states) (* Branch *)
    | SOME ( (Sync_Fr n)) => (birs_exec_rng_fun t state (Sync_Fr n) states) (* RNG functions *)
    | SOME ( (P2A s))     => (birs_exec_out_fun t state (P2A s) states) (* Output functions *)
    | SOME ( (A2P r))     => (birs_exec_in_fun t state (A2P r) states) (* Input functions *)
`;
*)

val _ = export_theory();
