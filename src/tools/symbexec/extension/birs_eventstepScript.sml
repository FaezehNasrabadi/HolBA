open HolKernel Parse boolLib bossLib;

open pred_setTheory;
open bir_programTheory;
open bir_symbTheory;
open bslSyntax;
open bir_symb_sound_coreTheory;
open HolBACoreSimps;



val _ = new_theory "birs_eventstep";


val _ = new_constant("Rfun", ``:(string -> bir_exp_t option) -> bir_var_t``);
val _ = new_constant("Oracle", ``:(string -> bir_exp_t option) -> bir_var_t``);

(* Synchronize Event *)
val _ = Datatype `sync_event =
    P2A bir_var_t
    | A2P bir_var_t
    | Sync_Fr bir_var_t
              `;
                
(* SBIR non-synchronous events *)        
val _ = Datatype
        `SBIRnsyc_event =
Event bir_var_t
| Crypto bir_var_t
| Loop bir_var_t
        `;
                
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
       birs_exec_event_fun p state (Event e) =
if (e NOTIN (birs_symb_symbols state))
then {(state with bsst_pc updated_by birs_next_bsst_pc)}
else {birs_state_set_failed state}
`;
                                                                  
                                                                      
(* symbolic execution step for RNG functions *)    
val birs_exec_rng_fun_def =
Define `
       birs_exec_rng_fun p state (Sync_Fr n) =
if ((n NOTIN (birs_symb_symbols state)) ∧ (n = (Rfun state.bsst_environ)))
then
    {<|
        bsst_pc       := ((state with bsst_pc updated_by birs_next_bsst_pc).bsst_pc);
        bsst_environ  := (birs_update_env ("RNG", (BExp_Den n)) state.bsst_environ);
        bsst_pcond    := state.bsst_pcond;
        bsst_status   := state.bsst_status
      |>}
else {birs_state_set_failed state}
`;    


(* symbolic execution step for Crypto functions *)    
val birs_exec_crypto_fun_def =
Define `
       birs_exec_crypto_fun p state (Crypto v) =
if ((v NOTIN (birs_symb_symbols state)) ∧ (v = (Oracle state.bsst_environ)))
then
    {<|
        bsst_pc       := ((state with bsst_pc updated_by birs_next_bsst_pc).bsst_pc);
        bsst_environ  := (birs_update_env ("crypto", (BExp_Den v)) state.bsst_environ);
        bsst_pcond    := state.bsst_pcond;
        bsst_status   := state.bsst_status
      |>}
else {birs_state_set_failed state}
`; 

(* symbolic execution step for Input functions *)    
val birs_exec_in_fun_def =
Define `
       birs_exec_in_fun p state (A2P r) =
if (r NOTIN (birs_symb_symbols state))
then 
  {<|
    bsst_pc       := ((state with bsst_pc updated_by birs_next_bsst_pc).bsst_pc);
    bsst_environ  := (birs_update_env ("Adv", (BExp_Den r)) state.bsst_environ);
    bsst_pcond    := state.bsst_pcond;
    bsst_status   := state.bsst_status
                             |>}
else {birs_state_set_failed state}
     `;
     
(* symbolic execution step for Output functions *)    
val birs_exec_out_fun_def =
Define `
       birs_exec_out_fun p state (P2A s) =
if ((SOME (BExp_Den s)) = (state.bsst_environ "R0"))
then {(state with bsst_pc updated_by birs_next_bsst_pc)}
else {birs_state_set_failed state}
`; 

(* symbolic execution step for Loops *)    
val birs_exec_loop_def =
Define `
       birs_exec_loop p state (Loop t) =
if (t NOTIN (birs_symb_symbols state))
then (birs_exec_step p state)
else {birs_state_set_failed state}
     `;

(* symbolic execution single-step labeled transition *)     
val birs_exec_event_step_def = Define `
    birs_exec_event_step p state event states =
  case event of
    | NONE => (birs_exec_step p state states) (* normal steps *)
    | SOME (INL (Event e)) => (birs_exec_event_fun p state (Event e) states) (* event functions *)
    | SOME (INL (Crypto v)) => (birs_exec_crypto_fun p state (Crypto v) states) (* Crypto functions *)
    | SOME (INL (Loop t)) => (birs_exec_loop p state (Loop t) states) (* Loops *)
    | SOME (INR (Sync_Fr n)) => (birs_exec_rng_fun p state (Sync_Fr n) states) (* RNG functions *)
    | SOME (INR (P2A s)) => (birs_exec_out_fun p state (P2A s) states) (* Output functions *)
    | SOME (INR (A2P r)) => (birs_exec_in_fun p state (A2P r) states) (* Input functions *)
`;


val _ = export_theory();
