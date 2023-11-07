
open HolKernel Parse boolLib bossLib;
open HolBACoreSimps;
open HolBASimps;
open boolTheory;
open pred_setTheory;
open simpLib;
open symb_interpretTheory;

val _ = new_theory "sbir_tree";

 (*   
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
 *)

(* SBIR events *) 
val _ = Datatype `sbir_event =
P2A bir_var_t
| A2P bir_var_t
| Sync_Fr bir_var_t
| Event bir_var_t
| Crypto bir_var_t
| Loop bir_var_t
| Branch bir_var_t
| Silent
  `;

val _ = Datatype `stree =
SLeaf
| SNode ('a # 'b # 'c) stree
| SBranch ('a # 'b # 'c) stree stree
	  `;

val val_of_tree_def = Define`
(val_of_tree (SLeaf) = NONE) /\
(val_of_tree (SNode n st) = SOME n) /\
(val_of_tree (SBranch n lst rst) = SOME n)`;
                                          
(*define a symbolic tree hol datatype
val _ = Datatype `stree =
SLeaf
| SNode ('a # 'b) stree
| SBranch ('a # 'b) stree stree
	  `;


val _ = Datatype `stree =
SLeaf
| SNode 'a 'b 'c stree
| SBranch 'a 'b 'c stree stree
	  `;

val STATES_def = Define`
(STATES (SLeaf) = {}) /\
(STATES (SNode n st) = ({n}∪(STATES st))) /\
(STATES (SBranch n lst rst) = ({n}∪(STATES lst)∪(STATES rst)))`;

val ENVs_def = Define`
(ENVs (SLeaf) = {}) /\
(ENVs (SNode p e f st) = ({f}∪(ENVs st))) /\
(ENVs (SBranch p e f lst rst) = ({f}∪(ENVs lst)∪(ENVs rst)))`;

        
val val_of_tree_def = Define`
(val_of_tree (SLeaf) = NONE) /\
(val_of_tree (SNode n st) = SOME n) /\
(val_of_tree (SBranch n lst rst) = SOME n)`;

val position_in_tree_def = Define`
(position_in_tree (SLeaf) = NONE) /\
(position_in_tree (SNode p e f st) = SOME p) /\
(position_in_tree (SBranch p e f lst rst) = SOME p)`;

             
val connected_def  = Define`
(connected (SLeaf) (a:α # β) (b:α # β) = F) /\
(connected (SNode p n st) (a:α # β) (b:α # β) = ((a = n) ∧ (b = THE (val_of_tree st)))) /\
(connected (SBranch p n lst rst) (a:α # β) (b:α # β) = ((a = n) ∧ ((b = THE (val_of_tree lst)) ∨ (b = THE (val_of_tree rst)))))`;                                            
 *)

val position_in_tree_def = Define`
(position_in_tree (SLeaf) = NONE) /\
(position_in_tree (SNode (e,p,f) st) = SOME p) /\
(position_in_tree (SBranch (e,p,f) lst rst) = SOME p)`;


val event_of_tree_def = Define`
(event_of_tree (SLeaf) = NONE) /\
(event_of_tree (SNode (e,p,f) st) = SOME e) /\
(event_of_tree (SBranch (e,p,f) lst rst) = SOME e)`;

val env_of_tree_def = Define`
(env_of_tree (SLeaf) = NONE) /\
(env_of_tree (SNode (e,p,f) st) = SOME f) /\
(env_of_tree (SBranch (e,p,f) lst rst) = SOME f)`;

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

val env_of_val_thm = store_thm(
  "env_of_val_thm",
  ``∀Tree e i h. ((val_of_tree Tree) = SOME (e,i,h)) ⇒ ((env_of_tree Tree) = SOME h)``,
                                                                                    GEN_TAC >>
     Cases_on ‘Tree’ >>
     ASM_SIMP_TAC (srw_ss()) [val_of_tree_def] >>
     Cases_on ‘p’ >>
     Cases_on ‘r’ >>
     ASM_SIMP_TAC (srw_ss()) [val_of_tree_def,env_of_tree_def] >>
     Cases_on ‘p’ >>
     Cases_on ‘r’ >>
     ASM_SIMP_TAC (srw_ss()) [val_of_tree_def,env_of_tree_def]           
  );

val position_of_val_thm = store_thm(
  "position_of_val_thm",
  ``∀Tree e i h. ((val_of_tree Tree) = SOME (e,i,h)) ⇒ ((position_in_tree Tree) = SOME i)``,
                                                                                    GEN_TAC >>
     Cases_on ‘Tree’ >>
     ASM_SIMP_TAC (srw_ss()) [val_of_tree_def] >>
     Cases_on ‘p’ >>
     Cases_on ‘r’ >>
     ASM_SIMP_TAC (srw_ss()) [val_of_tree_def,position_in_tree_def] >>
     Cases_on ‘p’ >>
     Cases_on ‘r’ >>
     ASM_SIMP_TAC (srw_ss()) [val_of_tree_def,position_in_tree_def]           
  );
  
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


                       
val execute_symbolic_tree_def = Define`
(execute_symbolic_tree (SLeaf) = {}) /\
(execute_symbolic_tree (SNode ( Silent,(SEnv e)) st) = ({( Silent,(SEnv e))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode ( (Event v),(SEnv e)) st) = ({( (Event v),(SEnv e))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode ( (Crypto v),(SEnv e)) st) = ({( (Crypto v),(SEnv (((BVar "crypto" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode ( (Loop v),(SEnv e)) st) = ({( (Loop v),(SEnv e))}∪(execute_symbolic_tree st)))  /\
(execute_symbolic_tree (SNode ( (P2A v),(SEnv e)) st) = ({( (P2A v),(SEnv e))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode ( (A2P v),(SEnv e)) st) = ({( (A2P v),(SEnv (((BVar "Adv" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st))) /\
(execute_symbolic_tree (SNode ( (Sync_Fr v),(SEnv e)) st) = ({( (Sync_Fr v),(SEnv (((BVar "RNG" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st)))/\
(execute_symbolic_tree (SBranch ( Branch v,(SEnv e)) lst rst) = ({( Branch v,(SEnv e))}∪(execute_symbolic_tree lst)∪(execute_symbolic_tree rst))) /\
(execute_symbolic_tree _ = {})`;

val traces_of_tree_def  = Define`
(traces_of_tree (SLeaf) = []) /\
(traces_of_tree (SNode (a,b) st) = (a::(traces_of_tree st))) /\
(traces_of_tree (SBranch (a,b) lst rst) = (a::(APPEND (traces_of_tree lst) (traces_of_tree rst))))`;

val traces_of_tree_def  = Define`
(traces_of_tree (SLeaf) = []) /\
(traces_of_tree (SNode p e f st) = (e::(traces_of_tree st))) /\
(traces_of_tree (SBranch p e f lst rst) = (e::(APPEND (traces_of_tree lst) (traces_of_tree rst))))`;  
                                                                                                  

val single_step_execute_symbolic_tree_def = Define`
(single_step_execute_symbolic_tree (SLeaf) = SLeaf) /\
(single_step_execute_symbolic_tree (SNode i Silent H st) = (SNode (i+1) Silent H st)) /\
(single_step_execute_symbolic_tree (SNode i (Event v) H st) = (SNode (i+1) Silent H st)) /\
(single_step_execute_symbolic_tree (SNode i (Crypto v) H st) = (SNode (i+1) Silent (symb_interpr_update H ((BVar "crypto" (BType_Imm Bit64)), SOME (BExp_Den v))) st)) /\
(single_step_execute_symbolic_tree (SNode i (Loop v) H st) = (SNode (i+1) Silent H st)) /\
(single_step_execute_symbolic_tree (SNode ( (P2A v),H) st) = (SNode (i+1) (P2A v),H) st)) /\
(single_step_execute_symbolic_tree (SNode ( (A2P v),H) st) = (SNode ( (A2P v),(symb_interpr_update H ((BVar "Adv" (BType_Imm Bit64)), SOME (BExp_Den v)))) st)) /\
(single_step_execute_symbolic_tree (SNode ( (Sync_Fr v),H) st) = (SNode ( (Sync_Fr v),(symb_interpr_update H ((BVar "RNG" (BType_Imm Bit64)), SOME (BExp_Den v)))) st)) /\
(single_step_execute_symbolic_tree (SBranch ( Branch v,H) lst rst) = (SBranch ( Branch v,H) lst rst)) /\
(single_step_execute_symbolic_tree t = t)`;*)

val single_step_execute_symbolic_tree_def =
Define`single_step_execute_symbolic_tree tre ev tre' =
(case ev of
   Silent => (∃ i H st. (tre = (SNode (Silent,i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i,H)))
 | (Event v) => (∃ i H st. (tre = (SNode ((Event v),i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i+1,H)))
 | (Loop v) => (∃ i H st. (tre = (SNode ((Loop v),i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i+1,H)))
 | (P2A v) => (∃ i H st. (tre = (SNode ((P2A v),i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i+1,H)))
 | (Crypto v) => (∃ i H st. (tre = (SNode ((Crypto v),i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i+1,(symb_interpr_update H ((BVar "crypto" (BType_Imm Bit64)), SOME (BExp_Den v))))))
 | (A2P v) => (∃ i H st. (tre = (SNode ((A2P v),i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i+1,(symb_interpr_update H ((BVar "Adv" (BType_Imm Bit64)), SOME (BExp_Den v))))))
 | (Sync_Fr v) => (∃ i H st. (tre = (SNode ((Sync_Fr v),i,H) st)) ∧ (tre' = st) ∧ ((val_of_tree tre') = SOME (Silent,i+1,(symb_interpr_update H ((BVar "RNG" (BType_Imm Bit64)), SOME (BExp_Den v))))))             
| (Branch v) => (∃ i H lst rst. (tre = (SBranch ((Branch v),i,H) lst rst)) ∧ ((tre' = lst) ∨ (tre' = rst)) ∧ ((val_of_tree tre') = SOME (Silent,i+1,H)))
)
`;  
   

val execute_symbolic_tree_def =
Define`execute_symbolic_tree tre Eve tre' =
(case Eve of
   [] => (tre = tre')
 | (e::ev) => (∃tre''. (execute_symbolic_tree tre ev tre'') ∧ (single_step_execute_symbolic_tree tre'' e tre'))
)
`;


val traces_of_tree_def  = Define`
traces_of_tree tre = {e| ∃tre'. (execute_symbolic_tree tre e tre')}`;

val _ = export_theory();


