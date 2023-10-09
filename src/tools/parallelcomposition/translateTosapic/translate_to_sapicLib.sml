structure translate_to_sapicLib :> translate_to_sapicLib =
struct
open Abbrev

  local
open HolKernel Parse boolLib bossLib;
open sapicplusTheory;
open sapicplusSyntax;
open messagesTheory;
open messagesSyntax;
open wordsTheory;
open ASCIInumbersTheory;
open Arbnumcore;
open bir_immTheory;
open bir_valuesSyntax;
open bir_immSyntax;
open bir_expSyntax;
open bir_envSyntax;
open integerTheory;
open intSyntax;
open Term;
open translate_to_sapicTheory;

val ERR = mk_HOL_ERR "translate_to_sapicLib";
val wrap_exn = Feedback.wrap_exn "translate_to_sapicLib";

                

in

fun bir_exp_to_sapic_term exp =
let
	val _ = ()
in
    (* Constants *)
    (* Manual tests
        val exp = ``BExp_Const (Imm64 112w)``;*)
    if is_BExp_Const exp then
	let
	    val imm = (dest_BExp_Const) exp;	
	    val cons = (rhs o concl o (SIMP_CONV (srw_ss()) [b2n_def,translate_Imm_to_string_def])) “translate_Imm_to_string ^imm”;
	in
	    mk_Con (mk_Name (PubName_tm, cons))
	end

    (* Memory constants *)
	(* val exp = ``BExp_MemConst Bit64 Bit8 abcd``; *)
    else if is_BExp_MemConst exp then
      
        let 
            val (addr_bir_ty, val_bir_ty, tm_map) = dest_BExp_MemConst exp;
            
            val addr_ty = (rhs o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(size_of_bir_immtype) ^addr_bir_ty”; 
            val val_ty =  (rhs o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(size_of_bir_immtype) ^val_bir_ty”;
            val cons_int = (rhs o concl o (SIMP_CONV (srw_ss()) [])) (numSyntax.mk_plus(addr_ty,val_ty))
	    val cons =  (rhs o concl o (SIMP_CONV (srw_ss()) [])) “toString ^cons_int”
        in
            mk_Con (mk_Name (PubName_tm, cons))
        end
        handle e => raise wrap_exn "bir_exp_to_words::MemConst" e
    (* Den *)
    (*
	val exp = ``(BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))``;
     *)
    else if is_BExp_Den exp then
	let
          val (name,bir_type) = (dest_BVar o dest_BExp_Den) exp
          val size =
              if is_BType_Imm bir_type then
		  let val immty = dest_BType_Imm bir_type in
		      (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(int_of_num o size_of_bir_immtype) ^immty”
		  end
              else if is_BType_Mem bir_type then
		  let
                      val (addr_bir_ty, val_bir_ty) = dest_BType_Mem bir_type
                      val addr_ty =  (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(int_of_num o size_of_bir_immtype) ^addr_bir_ty”
                      val val_ty =  (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(int_of_num o size_of_bir_immtype) ^val_bir_ty”
		  in
                      intSyntax.mk_plus(addr_ty,val_ty)
		  end
              else
		  raise Fail ("unhandled type: " ^ (term_to_string bir_type))
    in   
          mk_TVar (mk_Var (name,size))
    end
    (* Casts *)
	(* 
        val exp = ``BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32``;
        *)
    else if is_BExp_Cast exp then
        let
            val (casttyp, ex, sz) = (dest_BExp_Cast) exp;
            val cast_sz = (rhs o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(toString o size_of_bir_immtype) ^sz”;
	    val cast_sz_st = mk_Con (mk_Name (PubName_tm, cast_sz));
            val val_st = bir_exp_to_sapic_term ex;
            val cast_ty = (rhs o concl o (SIMP_CONV (srw_ss()) [translate_Cast_to_string_def])) “translate_Cast_to_string ^casttyp”;
	    val trm_list = (listSyntax.mk_list ([val_st,cast_sz_st],SapicTerm_t_ty));
	    val fun_sig = pairSyntax.list_mk_pair [cast_ty,“(2:int)”,Public_tm, Constructor_tm]
		   
        in
          mk_FAPP (fun_sig,trm_list)
        end
        handle e => raise wrap_exn "bir_exp_to_sapic_term::Cast" e                         
  (* Unary expressions *)
  else if is_BExp_UnaryExp exp then
        (* 
        val exp = ``BExp_UnaryExp BIExp_Not
          (BExp_BinPred BIExp_Equal
            (BExp_Den (BVar "oracle" (BType_Imm Bit32)))
            (BExp_Const (Imm32 0w)))``;
        *)
        let
          val (uop, bir_exp) = (dest_BExp_UnaryExp) exp
          val exp_sap_tr = bir_exp_to_sapic_term bir_exp
          val to_str = ``translate_UnaryExp_to_string ^uop``
          val uop_str = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [translate_UnaryExp_to_string_def])) to_str
	  val trm_list = (listSyntax.mk_list ([exp_sap_tr],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair [uop_str,“(1:int)”,Public_tm, Constructor_tm]
		   
        in
          mk_FAPP (fun_sig,trm_list)
        end
          handle e => raise wrap_exn "bir_exp_to_sapic_term::unary_exp" e

      (* Binary expressions *)
      else if is_BExp_BinExp exp then
        (* 
        val exp = ``(BExp_BinExp BIExp_Plus (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))``;
        *)
        let
          val (bop, bir_exp1, bir_exp2) = (dest_BExp_BinExp) exp
          val st_exp1 =  bir_exp_to_sapic_term bir_exp1
          val st_exp2 =  bir_exp_to_sapic_term bir_exp2
          val to_st = ``translate_BinExp_to_string ^bop``
          val st_bop = (rhs o concl o SIMP_CONV (srw_ss()) [translate_BinExp_to_string_def]) to_st
          val trm_list = (listSyntax.mk_list ([st_exp1,st_exp2],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair [st_bop,“(2:int)”,Public_tm, Constructor_tm]
		   
        in
          mk_FAPP (fun_sig,trm_list)
        end
          handle e => raise wrap_exn "bir_exp_to_sapic_term::binary_exp" e

      (* Binary predicates *)
      else if is_BExp_BinPred exp then
        (*
        val exp = ``BExp_BinPred BIExp_Equal
          (BExp_Den (BVar "oracle" (BType_Imm Bit32)))
          (BExp_Const (Imm32 0w))``;
        *)
        let
          val (bpred, bir_exp1, bir_exp2) = (dest_BExp_BinPred) exp
          val st_exp1 = bir_exp_to_sapic_term bir_exp1
          val st_exp2 = bir_exp_to_sapic_term bir_exp2
          val to_st = ``translate_BinPred_to_string ^bpred``
          val st_bp = (rhs o concl o SIMP_CONV (srw_ss()) [translate_BinPred_to_string_def]) to_st
	  val trm_list = (listSyntax.mk_list ([st_exp1,st_exp2],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair [st_bp,“(2:int)”,Public_tm, Constructor_tm]
        in
          mk_FAPP (fun_sig,trm_list)
        end
          handle e => raise wrap_exn "bir_exp_to_sapic_term::binary_pred" e

      (* MemEq expressions *)
      else if is_BExp_MemEq exp then
        (* 
        val exp = ``
          BExp_MemEq
            (BExp_Den (BVar "MEM_dest" (BType_Mem Bit32 Bit8)))
            (BExp_Const (Imm16 (42w :word16)))
        ``;

        *)
        let
          val (bir_lhs, bir_rhs) = dest_BExp_MemEq exp
          val lhs = bir_exp_to_sapic_term bir_lhs
          val rhs = bir_exp_to_sapic_term bir_rhs
          val trm_list = (listSyntax.mk_list ([lhs,rhs],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"MemEq"”,“(2:int)”,Public_tm, Constructor_tm]
        in
          mk_FAPP (fun_sig,trm_list)
        end
        handle e => raise wrap_exn "bir_exp_to_sapic_term::mem_eq" e

      (* If-then-else *)
      else if is_BExp_IfThenElse exp then
        (* 
        val exp = ``BExp_IfThenElse
          (BExp_BinPred BIExp_LessThan (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))
          (BExp_Const (Imm64 200w))
          (BExp_Const (Imm64 404w))``;
        *)
        let
          val (bir_cond_exp, bir_then_exp, bir_else_exp) = dest_BExp_IfThenElse exp
          val st_cond_exp = bir_exp_to_sapic_term bir_cond_exp
          val st_then_exp = bir_exp_to_sapic_term bir_then_exp
          val st_else_exp = bir_exp_to_sapic_term bir_else_exp
          val trm_list = (listSyntax.mk_list ([st_cond_exp,st_then_exp,st_else_exp],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"IfThenElse"”,“(3:int)”,Public_tm, Destructor_tm]
        in
            mk_FAPP (fun_sig,trm_list)
	end
        handle e => raise wrap_exn "bir_exp_to_sapic_term::if_then_else" e

(* Load expressions *)
      else if is_BExp_Load exp then
        (*
	val exp = ``
          (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)``
        *)
        let
          val (bir_mem, bir_addr, bir_endi, bir_val_ty) = dest_BExp_Load exp;
          val mem_st = bir_exp_to_sapic_term bir_mem;
          val base_addr_st = bir_exp_to_sapic_term bir_addr;
	  val ld_endi = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [translate_Endian_to_string_def])) ``translate_Endian_to_string ^bir_endi``
	  val ld_endi_st = mk_TVar (mk_Var (ld_endi,(“0:int”)))
	  val ld_sz = (rhs o concl o (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def])) “(toString o size_of_bir_immtype) ^bir_val_ty”;
	  val ld_sz_st = mk_Con (mk_Name (PubName_tm, ld_sz)); 
          val trm_list = (listSyntax.mk_list ([mem_st,base_addr_st,ld_endi_st,ld_sz_st],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"Load"”,“(4:int)”,Public_tm, Constructor_tm]
        in
	    mk_FAPP (fun_sig,trm_list)
        end
        handle e => raise wrap_exn "bir_exp_to_sapic_term::mem_load" e
      
      (* Store expressions *)
      else if is_BExp_Store exp then
        (* 
        val exp = ``
          (BExp_Store
            (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
            (BExp_Den (BVar "ADDR1" (BType_Imm Bit64)))
            BEnd_BigEndian
            (BExp_Const (Imm128 (42w :word128))))
        ``;
        *)
        let
          val (bir_mem, bir_addr, bir_endi, bir_val) = dest_BExp_Store exp
          val mem_st = bir_exp_to_sapic_term bir_mem
          val base_addr_st = bir_exp_to_sapic_term bir_addr
          val val_st = bir_exp_to_sapic_term bir_val
	  val st_endi = (snd o dest_eq o concl o (SIMP_CONV (srw_ss()) [translate_Endian_to_string_def])) ``translate_Endian_to_string ^bir_endi``
	  val st_endi_st = mk_TVar (mk_Var (st_endi,(“0:int”)))
          val trm_list = (listSyntax.mk_list ([ mem_st,base_addr_st,st_endi_st,val_st],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"Store"”,“(4:int)”,Public_tm, Destructor_tm]
        in
          mk_FAPP (fun_sig,trm_list)
        end
        handle e => raise wrap_exn "bir_exp_to_sapic_term::mem_store" e
      else
        raise ERR "bir_exp_to_sapic_term" ("Don't know BIR expression: " ^ (term_to_string exp))
    end; 

       
  end (* local *)

end (* translate_to_sapicLib *)

