open HolKernel Parse boolLib bossLib;
open sapicplusTheory;
open wordsTheory;
open ASCIInumbersTheory;
open Arbnumcore;
open bir_immTheory;
open integerTheory;
open Term;
(* open sbir_treeLib; *)
val _ = new_theory "translate_to_sapic";

                 
(*
val translate_Imm_to_string_def = Define`
translate_Imm_to_string imm =
(case imm of
    Imm1   w1   => (w2s 1 HEX w1)
  | Imm8   w8   => (w2s 8 HEX w8)
  | Imm16  w16  => (w2s 16 HEX w16)
  | Imm32  w32  => (w2s 32 HEX w32)
  | Imm64  w64  => (w2s 64 HEX w64)
  | Imm128 w128 => (w2s 128 HEX w128)
)
`;*)

val translate_Imm_to_string_def = Define`
translate_Imm_to_string imm =
(toString o b2n) imm
`;

val translate_birvar_to_sapicterm_def = Define`
translate_birvar_to_sapicterm (BVar str (BType_Imm s)) =
TVar (Var str ((int_of_num o size_of_bir_immtype) s))
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
        
val translate_birexp_to_sapicterm_def = Define`
                                              translate_birexp_to_sapicterm exp =
(case exp of
   BExp_Const c                      => Con (Name PubName (translate_Imm_to_string c))
 | BExp_Den bv                       => (translate_birvar_to_sapicterm bv)
 | BExp_Load e1 e2 a b               => FAPP ("Load",(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
 | BExp_Store e1 e2 a e3             => FAPP ("Store",(3, Public, Destructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2);(translate_birexp_to_sapicterm e3)]
 | BExp_UnaryExp ue e                => FAPP ((translate_UnaryExp_to_string ue),(1, Public, Constructor)) [(translate_birexp_to_sapicterm e)]
 | BExp_BinExp be e1 e2              => FAPP ((translate_BinExp_to_string be),(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
 | BExp_BinPred bp e1 e2             => FAPP ((translate_BinPred_to_string bp),(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
 | BExp_MemEq e1 e2                  => FAPP ("MemEq",(2, Public, Constructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2)]
 | BExp_IfThenElse e1 e2 e3          => FAPP ("IfThenElse",(3, Public, Destructor)) [(translate_birexp_to_sapicterm e1);(translate_birexp_to_sapicterm e2);(translate_birexp_to_sapicterm e3)]

) 
`;
  (*
| exclusive_or bv1 bv2              => FAPP ("exclusive_or",(2, Public, Constructor)) [(translate_birvar_to_sapicterm bv1);(translate_birvar_to_sapicterm bv2)]
 | conc1 bv                         => FAPP ("conc1",(1, Public, Constructor)) [(translate_birvar_to_sapicterm bv)]  

val symbtree_to_sapic_def = Define `
    symbtree_to_sapic holtree  =
case holtree of
SLeaf => ProcessNull
| SBranch a b lstr rstr  => ProcessComb (Cond (translate_birexp_to_sapicterm b)) (symbtree_to_sapic lstr) (symbtree_to_sapic rstr)
| SNode (BVar name ty) b str  =>  (
  if ((rich_list$IS_SUFFIX name "assert_true_cnd") \/
      (rich_list$IS_SUFFIX name "assert_false_cnd") \/
      (rich_list$IS_SUFFIX name "cjmp_false_cnd"))
  then (symbtree_to_sapic str)
  else if (rich_list$IS_SUFFIX name "XOR")
  then (ProcessComb  (Let (translate_birvar_to_sapicterm (BVar name ty)) (FAPP (((FST o strip_comb) b),(2, Public, Constructor)) [])) (symbtree_to_sapic str) (ProcessNull))
else (ProcessComb  (Let (translate_birvar_to_sapicterm (BVar name ty)) (translate_birexp_to_sapicterm b)) (symbtree_to_sapic str) (ProcessNull))) `;

val _ = EVAL ``symbtree_to_sapic (^holtree)``
*)
val _ = export_theory();
