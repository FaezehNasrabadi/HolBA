open HolKernel Parse boolLib bossLib;
open sapicplusTheory;
open birs_eventstepTheory;
open wordsTheory;
     
val _ = new_theory "translate_to_sapic";

    
val translate_birexp_to_sapicterm_def = Define`
translate_birexp_to_sapicterm exp =
(case exp of
   BExp_Const (Imm32 c) => Con (Name PubName (word_to_hex_string c))
  | BExp_Den (BVar str (BType_Imm Bit32)) => TVar (Var str 32)
(*  | BExp_UnaryExp ue e => 
  | BExp_BinExp be e1 e2 => 
  | BExp_BinPred bp e1 e2 => 
  | BExp_MemEq e1 e2 => 
  | BExp_IfThenElse e1 e2 e3 => 
  | BExp_Load e1 e2 a b => 
  | BExp_Store e1 e2 a e3 => *)
)

`;
  



val _ = export_theory();
