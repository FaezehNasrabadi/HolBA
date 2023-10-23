
open HolKernel Parse;
open HolBACoreSimps;
open HolBASimps;
open boolTheory;
open pred_setTheory;
open simpLib;
open bossLib;


val _ = new_theory "sbir_tree";

    
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
| Branch
| Silent
        `;

                
(* define a symbolic tree hol datatype *)
val _ = Datatype `stree =
SLeaf
| SNode ('a # 'b) stree
| SBranch ('a # 'b) stree stree
	  `;

val STATES_def = Define`
(STATES (SLeaf) = {}) /\
(STATES (SNode n st) = ({n}∪(STATES st))) /\
(STATES (SBranch n lst rst) = ({n}∪(STATES lst)∪(STATES rst)))`;

        
val val_of_tree_def = Define`
(val_of_tree (SLeaf) = NONE) /\
(val_of_tree (SNode n st) = SOME n) /\
(val_of_tree (SBranch n lst rst) = SOME n)`;

             
val connected_def  = Define`
(connected (SLeaf) (a:α # β) (b:α # β) = F) /\
(connected (SNode n st) (a:α # β) (b:α # β) = ((a = n) ∧ (b = THE (val_of_tree st)))) /\
(connected (SBranch n lst rst) (a:α # β) (b:α # β) = ((a = n) ∧ ((b = THE (val_of_tree lst)) ∨ (b = THE (val_of_tree rst)))))`;                                              

val _ = Datatype `sbir_pc_t =
  | PC_Normal 
  | PC_Event
  | PC_In
  | PC_Out
  | PC_Cr
  | PC_Fr
  | PC_Loop
  | PC_Branch
    `;
    
val _ = Datatype `sbir_environment_t = SEnv (bir_var_t -> (bir_exp_t option))`;

val symb_env_dom_def = Define `
    symb_env_dom (SEnv ro) = {symb | ro symb <> NONE}
                             `;

val symb_env_update_def = Define `
    symb_env_update (SEnv ro) (symb, vo) = SEnv ((symb =+ vo) ro)
                                                `;

val symb_env_get_def = Define `
    symb_env_get (SEnv ro) symb = ro symb
`;
                                                                     
(*

                                                        
val execute_symbolic_tree_def = Define`
(execute_symbolic_tree (SLeaf) [] = {}) /\
(execute_symbolic_tree (SNode (PC_Normal,(SEnv e)) st) (INL Silent::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t))) /\
(execute_symbolic_tree (SNode (PC_Event,(SEnv e)) st) (INL (Event v)::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t))) /\
(execute_symbolic_tree (SNode (PC_Cr,(SEnv e)) st) (INL (Crypto v)::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t))) /\
(execute_symbolic_tree (SNode (PC_Loop,(SEnv e)) st) (INL (Loop v)::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t)))  /\
(execute_symbolic_tree (SNode (PC_Out,(SEnv e)) st) (INR (P2A v)::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t))) /\
(execute_symbolic_tree (SNode (PC_In,(SEnv e)) st) (INR (A2P v)::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t))) /\
(execute_symbolic_tree (SNode (PC_Fr,(SEnv e)) st) (INR (Sync_Fr v)::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree st t)))/\
(execute_symbolic_tree (SBranch (PC_Branch,(SEnv e)) lst rst) (INL Silent::t) = ({(PC_Normal,(SEnv e))}∪(execute_symbolic_tree lst t)∪(execute_symbolic_tree rst t))) /\
(execute_symbolic_tree _ _ = {})`;

*)
                       
val execute_symbolic_tree_def = Define`
(execute_symbolic_tree (SLeaf) = {}) /\
(execute_symbolic_tree (SNode (INL Silent,(SEnv e)) st) = ({(INL Silent,(SEnv e))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode (INL (Event v),(SEnv e)) st) = ({(INL (Event v),(SEnv e))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode (INL (Crypto v),(SEnv e)) st) = ({(INL (Crypto v),(SEnv (((BVar "crypto" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode (INL (Loop v),(SEnv e)) st) = ({(INL (Loop v),(SEnv e))}∪(execute_symbolic_tree st)))  /\
(execute_symbolic_tree (SNode (INR (P2A v),(SEnv e)) st) = ({(INR (P2A v),(SEnv e))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode (INR (A2P v),(SEnv e)) st) = ({(INR (A2P v),(SEnv (((BVar "Adv" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode (INR (Sync_Fr v),(SEnv e)) st) = ({(INR (Sync_Fr v),(SEnv (((BVar "RNG" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st)))/\
(execute_symbolic_tree (SBranch (INL Branch,(SEnv e)) lst rst) = ({(INL Branch,(SEnv e))}∪(execute_symbolic_tree lst)∪(execute_symbolic_tree rst))) /\
(execute_symbolic_tree _ = {})`;

val traces_of_tree_def  = Define`
(traces_of_tree (SLeaf) = []) /\
(traces_of_tree (SNode (a,b) st) = (a::(traces_of_tree st))) /\
(traces_of_tree (SBranch (a,b) lst rst) = (a::(APPEND (traces_of_tree lst) (traces_of_tree rst))))`;                          


                                                                                                                                

    
val _ = export_theory();


