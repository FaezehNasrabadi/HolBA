
open HolKernel Parse;
open HolBACoreSimps;
open HolBASimps;
open boolTheory;
open pred_setTheory;
open simpLib;
open bossLib;
open bir_symbexec_stateLib;

val _ = new_theory "sbir_tree";


(* define a symbolic tree hol datatype *)
val _ = Datatype `stree =
SLeaf
| SNode ('a # 'a) stree
| SBranch ('a # 'a) stree stree
	  `;


val STATES_def = Define`
(STATES (SLeaf) = {}) /\
(STATES (SNode (a,b) st) = ({(a,b)}∪(STATES st))) /\
(STATES (SBranch (a,b) lst rst) = ({(a,b)}∪(STATES lst)∪(STATES rst)))`;
                                                                      
		       
val _ = export_theory();


