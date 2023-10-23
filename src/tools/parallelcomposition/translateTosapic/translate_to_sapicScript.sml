
open HolKernel Parse boolLib bossLib;
open sapicplusTheory;
open messagesTheory;
open wordsTheory;
open ASCIInumbersTheory;
open Arbnumcore;
open bir_immTheory;
open integerTheory;
open Term;
open sbir_treeTheory;
open optionTheory;



val _ = new_theory "translate_to_sapic";                

(*****************start translation Bir Exp to Sapic Term**********************)

val translate_Imm_to_string_def = Define`
translate_Imm_to_string imm =
(toString o b2n) imm

`;


 val translate_birvar_to_sapicvar_def = Define`
 translate_birvar_to_sapicvar (BVar str _) =
 (Var str 0)
      `;

 val translate_bir_immtype_to_sapicterm_def = Define`
 translate_bir_immtype_to_sapicterm immty =
 Con (Name PubName ((toString o size_of_bir_immtype) immty))
      `;        
      
val translate_UnaryExp_to_string_def = Define`
translate_UnaryExp_to_string ue =
(case ue of
   BIExp_ChangeSign => "ChangeSign"
 | BIExp_Not        => "Not"
 | BIExp_CLZ        => "CLZ"
 | BIExp_CLS        => "CLS"
)`;

val translate_BinExp_to_string_def = Define`
translate_BinExp_to_string be =
(case be of
   BIExp_And              => "And"
 | BIExp_Or               => "Or"
 | BIExp_Xor              => "Xor"
 | BIExp_Plus             => "Plus"
 | BIExp_Minus            => "Minus"
 | BIExp_Mult             => "Mult"
 | BIExp_Div              => "Div"
 | BIExp_SignedDiv        => "SignedDiv"
 | BIExp_Mod              => "Mod"
 | BIExp_SignedMod        => "SignedMod"
 | BIExp_LeftShift        => "LeftShift"
 | BIExp_RightShift       => "RightShift"
 | BIExp_SignedRightShift => "SignedRightShift"
)`;

val translate_BinPred_to_string_def = Define`
translate_BinPred_to_string bp =
(case bp of
   BIExp_Equal             => "Equal"
 | BIExp_NotEqual          => "NotEqual"
 | BIExp_LessThan          => "LessThan"
 | BIExp_SignedLessThan    => "SignedLessThan"
 | BIExp_LessOrEqual       => "LessOrEqual"
 | BIExp_SignedLessOrEqual => "SignedLessOrEqual"
)`;


val translate_Cast_to_string_def = Define`
translate_Cast_to_string ct =
(case ct of
   BIExp_UnsignedCast => "UnsignedCast"
 | BIExp_SignedCast   => "SignedCast"
 | BIExp_HighCast     => "HighCast"
 | BIExp_LowCast      => "LowCast"
)`;


val translate_Endian_to_string_def = Define`
translate_Endian_to_string en =
(case en of        
   BEnd_BigEndian    => "BigEndian"
 | BEnd_LittleEndian => "LittleEndian"
 | BEnd_NoEndian     => "NoEndian"
)`;


val translate_birexp_to_sapicterm_def = Define`
                                               translate_birexp_to_sapicterm exp =
 (case exp of
    BExp_Const c                      => Con (Name PubName (translate_Imm_to_string c))
  | BExp_MemConst v1 v2 v3            => Con (Name PubName (toString ((size_of_bir_immtype v1) + (size_of_bir_immtype v2))))
  | BExp_Den bv                       => TVar (translate_birvar_to_sapicvar bv)
  | BExp_Load e1 e2 a b               => FAPP ("Load",(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
  | BExp_Store e1 e2 a e3             => FAPP ("Store",(3, Public, Destructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2);(translate_birexp_to_sapicterm e3)]
  | BExp_UnaryExp ue e                => FAPP ((translate_UnaryExp_to_string ue),(1, Public, Constructor)) [(translate_birexp_to_sapicterm e)]
  | BExp_BinExp be e1 e2              => FAPP ((translate_BinExp_to_string be),(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
  | BExp_BinPred bp e1 e2             => FAPP ((translate_BinPred_to_string bp),(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
  | BExp_MemEq e1 e2                  => FAPP ("MemEq",(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
  | BExp_IfThenElse e1 e2 e3          => FAPP ("IfThenElse",(3, Public, Destructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2);(translate_birexp_to_sapicterm e3)]
  | BExp_Cast v8 v9 v10               => FAPP ((translate_Cast_to_string v8),(2, Public, Constructor)) [(translate_birexp_to_sapicterm v9);(Con (Name PubName ((toString o size_of_bir_immtype) v10)))]
 ) 
 `;

        
(*****************end translation Bir Exp to Sapic Term**********************)
val _ = new_constant("trans", ``:(bir_var_t -> bir_exp_t option) -> (Var_t -> SapicTerm_t option)``);                    
(*

val symbtree_to_sapic_def = Define`
(symbtree_to_sapic (SLeaf) = ProcessNull) /\
(symbtree_to_sapic (SNode (INL Silent,(SEnv e)) st) = ({(INL Silent,(SEnv e))}∪(execute_symbolic_tree st))) /\
(symbtree_to_sapic (SNode (INL (Event v),(SEnv e)) st) =
(ProcessAction (Event (Fact TermFact [(translate_birexp_to_sapicterm (BExp_Den v))])) (symbtree_to_sapic str)))
({(INL (Event v),(SEnv e))}∪(execute_symbolic_tree st))) /\
(symbtree_to_sapic (SNode (INL (Crypto v),(SEnv e)) st) =
(ProcessComb  (Let (TVar (translate_birvar_to_sapicvar (BVar "crypto" (BType_Imm Bit64)))) (translate_birexp_to_sapicterm (BExp_Den v))) (symbtree_to_sapic str) (ProcessNull)) /\
(symbtree_to_sapic (SNode (INL (Loop v),(SEnv e)) st) = ({(INL (Loop v),(SEnv e))}∪(execute_symbolic_tree st)))  /\
(symbtree_to_sapic (SNode (INR (P2A v),(SEnv e)) st) = ({(INR (P2A v),(SEnv e))}∪(execute_symbolic_tree st))) /\
(symbtree_to_sapic (SNode (INR (A2P v),(SEnv e)) st) = ({(INR (A2P v),(SEnv (((BVar "Adv" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st))) /\
(symbtree_to_sapic (SNode (INR (Sync_Fr v),(SEnv e)) st) = ({(INR (Sync_Fr v),(SEnv (((BVar "RNG" (BType_Imm Bit64)) =+ SOME (BExp_Den v)) e)))}∪(execute_symbolic_tree st)))/\
(symbtree_to_sapic (SBranch (INL Branch,(SEnv e)) lst rst) =
(ProcessComb (Cond (translate_birexp_to_sapicterm b)) (symbtree_to_sapic lstr) (symbtree_to_sapic rstr)) /\
(symbtree_to_sapic _ = ProcessNull)`;

                       
val symbtree_to_sapic_def = Define `
    symbtree_to_sapic holtree  =
case holtree of
SLeaf => ProcessNull
| SBranch (a,b) lstr rstr  => ProcessComb (Cond (translate_birexp_to_sapicterm b)) (symbtree_to_sapic lstr) (symbtree_to_sapic rstr)
| SNode ((BVar name type),b) str  =>  (
if ((IS_SUFFIX name "assert_true_cnd") /\ (IS_SUFFIX name "assert_false_cnd") /\ (IS_SUFFIX name "cjmp_false_cnd")) then (symbtree_to_sapic str)
else (ProcessComb  (Let (TVar (translate_birvar_to_sapicvar (BVar name type))) (translate_birexp_to_sapicterm b)) (symbtree_to_sapic str) (ProcessNull)) 
)
                                      `;

val sim_def = Define`
                    sim snod conf =
((THE (sapic_substitution_get (get_substitution_conf conf) (translate_birvar_to_sapicvar (FST snod)))) = (translate_birexp_to_sapicterm (SND snod)))
`;


                      
val tree_node_to_process_thm = store_thm(
  "tree_node_to_process",
        ``∀(Tree: bir_exp_t stree) (var: bir_exp_t) (valu: bir_exp_t). ((var,valu) ∈ (STATES Tree)) ⇒ (∃(C:sapic_configuration_t). THE (sapic_substitution_get (get_substitution_conf C) (THE ( var_of_term (translate_birexp_to_sapicterm var)))) = (translate_birexp_to_sapicterm valu))``,
                           rpt strip_tac >>
                           Q.EXISTS_TAC `Config (Ns,St,Pold,(Substitution Sb),Al)`>>
                       rewrite_tac[sapic_substitution_get_def,get_substitution_conf_def] >>
                       Cases_on `var` >>
                       rewrite_tac[translate_birexp_to_sapicterm_def]

                        
  );


val tree_node_to_process_thm = store_thm(
  "tree_node_to_process",
        ``∀(Tree: (bir_var_t,bir_exp_t) stree) (var: bir_var_t) (valu: bir_exp_t). ((var,valu) ∈ (STATES Tree)) ⇒ (∃(C:sapic_configuration_t). THE (sapic_substitution_get (get_substitution_conf C) (translate_birvar_to_sapicvar var)) = (translate_birexp_to_sapicterm valu))``,
        rpt strip_tac >>
                           Q.EXISTS_TAC `Config (Ns,St,Pold,(Substitution Sb),Al)`>>
                       rewrite_tac[sapic_substitution_get_def,get_substitution_conf_def] >>
                       Cases_on `var` >>
                           
   rewrite_tac[translate_birvar_to_sapicvar_def]                     
  );
    
  translate_birexp_to_sapicterm x

translate_birexp_to_sapicterm (BExp_Const (Imm64 64w)) = Con (Name PubName "64")

 

val tree_node_to_process_thm = store_thm(
  "tree_node_to_process",
        ``∀(Tree: (bir_var_t,bir_exp_t) stree) (snod: (bir_var_t # bir_exp_t)) (snod': (bir_var_t # bir_exp_t)) (C:sapic_configuration_t).
        ((connected Tree snod snod') ∧ (sim snod C))
        ⇒ (∃(C':sapic_configuration_t). sim snod' C')``,
        gen_tac >>
        Cases_on `Tree`
rewrite_tac[connected_def]
rewrite_tac[connected_def]
reverse (Cases_on `s`)
rewrite_tac[val_of_tree_def]
        
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
rewrite_tac[sim_def]
gen_tac

     (Cases_on `C`)
       Cases_on `p''`
       Cases_on `r`
       Cases_on `r'`
       rewrite_tac[get_substitution_conf_def]
       Cases_on `q'''`
       rewrite_tac[sapic_substitution_get_def]
       strip_tac
                           Q.EXISTS_TAC `Config (Ns,St,Pold,(Substitution f),Al)`>>
                       rewrite_tac[sapic_substitution_get_def,get_substitution_conf_def] >>
                       Cases_on `var` >>
                           
   asm_rewrite_tac[translate_birvar_to_sapicvar_def]                     
  );
       DB.find "THE NONE"     
*)

       
  
val _ = export_theory();
