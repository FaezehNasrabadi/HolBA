
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
open bir_expTheory;
open bir_envSyntax;
open integerTheory;
open intSyntax;
open Term;
open translate_to_sapicTheory;

val ERR = mk_HOL_ERR "translate_to_sapicLib";
val wrap_exn = Feedback.wrap_exn "translate_to_sapicLib";


open simpLib;


open Type;
open wordsSyntax;

(*

SIMP_CONV (srw_ss()) [] “w2s 112w”
ASCIInumbersTheory.num_to_dec_string_def
SPEC exp (Thm.INST_TYPE [alpha |-> (type_of exp)] EQ_REFL)
EQ_TRANS
val original_theorem =
  <<[∃b. BExp_Const (Imm64 112w) = BExp_Const b ∧
        translate_Imm_to_string b = v]
    ⊢ const_name_from_str "112" = Name PubName "112">>;

val simplified_theorem =
  let
    val (_, ex_eq) = dest_exists (concl thm7);
    val (b_eq, _) = dest_conj ex_eq;
    val (lhs_eq, rhs_eq) = dest_eq b_eq;
    val b = rhs_eq
  in
    PROVE_HYP (EXISTS_ELIM_TAC original_theorem) (CONJUNCT1 (EQT_INTRO thm10))
  end;

fun trans_n2w_w2n exp =
    let val (arg_1, n2w_ty) = wordsSyntax.dest_n2w exp
	val _::w2n_ty::[] = snd( dest_type(type_of(wordsSyntax.dest_w2n arg_1)))
    in
	SIMP_CONV (srw_ss()) [GSYM (Thm.INST_TYPE [alpha |-> w2n_ty, beta |->  n2w_ty] w2w_def)] exp
    end;
(dest_type o hd o snd o dest_type o type_of) exp
val exp = “"str"”
val exp = “(12:int)”
val is_word_op = can dim_of;
val exp = “112w”;
val exp = “n2w (w2n 2w)”
fun n2w_plus_handler exp =
    let 
	val (n2w_exp,ty) = wordsSyntax.dest_n2w exp
	val (plus_1, plus_2) = numSyntax.dest_plus n2w_exp
	val thm_1 = (Thm.INST [ ``a:num`` |-> plus_1 , ``b:num`` |-> plus_2 ] 
			      (Thm.INST_TYPE [ alpha |-> ty](SPEC_ALL Bword_add_thm)))
	val thm_2 = (SIMP_RULE (srw_ss()) [GSYM w2w_def] thm_1)
	val (f_plus_1, f_plus_2) = wordsSyntax.dest_word_add (rhs (concl thm_2))
	val plus_1_lift_thm = worker_exp2il f_plus_1
	val plus_2_lift_thm = worker_exp2il f_plus_2 
	val add_1r_f_arg = rhs(concl plus_1_lift_thm)
	val add_2r_f_arg = rhs(concl plus_2_lift_thm)
	val add_1l_f_arg = lhs(concl plus_1_lift_thm)
	val add_2l_f_arg = lhs(concl plus_2_lift_thm)
	val thm_3 =  MP(MP(SPECL [ add_1l_f_arg, add_1r_f_arg ,add_2l_f_arg, add_2r_f_arg, (Term.inst[alpha |-> ty] word_add_tm)] 
				 (Thm.INST_TYPE[alpha |-> type_of(add_1r_f_arg) ,beta |-> type_of(add_2r_f_arg), gamma |-> type_of(add_2l_f_arg)] two_arg_fun_thm)) plus_1_lift_thm) plus_2_lift_thm
	val a = lhs (concl thm_2)
	val b = rhs (concl thm_2)
	val c = rhs (concl thm_3)
	val t3 = SPECL [a,b,c] (Thm.INST_TYPE [ alpha |-> (type_of a)] EQ_TRANS)
	val t4 = CONJ thm_2 thm_3
    in
	MP t3 t4
    end

fun trans_n2w_w2n exp =
    let val (arg_1, n2w_ty) = wordsSyntax.dest_n2w exp
	val _::w2n_ty::[] = snd( dest_type(type_of(wordsSyntax.dest_w2n arg_1)))
    in
	SIMP_CONV (srw_ss()) [GSYM (Thm.INST_TYPE [alpha |-> w2n_ty, beta |->  n2w_ty] w2w_def)] exp
    end;

val thm0 = SPEC exp (Thm.INST_TYPE [alpha |-> (type_of exp)] EQ_REFL);
	    val thm1 = SIMP_CONV (srw_ss()) [b2n_def,translate_Imm_to_string_def] “translate_Imm_to_string ^imm”;
val tm2 = (rhs o concl) thm4;
val thm5 = SIMP_CONV (srw_ss()) [b2n_def,translate_Imm_to_string_def] tm2;
 
SPEC exp (Thm.INST_TYPE [alpha |-> (type_of exp)] EQ_REFL);

val thm1 = Thm.INST [``x:bir_exp_t`` |-> exp] (bir_exp_t_case_eq); 
val thm2 = Thm.INST_TYPE [alpha |-> “:string”] thm1;
val thm3 = Thm.INST [``f:bir_imm_t -> string`` |-> “translate_Imm_to_string”] thm2;
val tm1 = (fst o boolSyntax.dest_disj o boolSyntax.rhs o Thm.concl) thm3;
val thm4 = ASSUME tm1;
val thm4 = SIMP_CONV (srw_ss()) [b2n_def,translate_Imm_to_string_def] tm1;
    val thm5 = (SIMP_RULE (srw_ss()) [b2n_def,translate_Imm_to_string_def] thm0);
val tm2 = (fst o dest_eq o (rhs o concl) thm5;
val thm5 = Thm.INST [ ``str:string`` |-> tm2] (SPEC_ALL const_name_from_str_def);
val thm6 =  CONJ thm4 thm5;
val tm3 = (snd o dest_eq o rhs o concl) thm4;
val thm7 = Thm.INST [ ``str:string`` |-> tm3] (SPEC_ALL const_name_from_str_def);
val tm4 =  concl thm7;
val thm8 = SIMP_CONV (srw_ss()) [thm6] tm4;


val thm1 = Thm.INST [``x:bir_exp_t`` |-> exp] (bir_exp_t_case_eq); 
val thm2 = Thm.INST_TYPE [alpha |-> “:string”] thm1;
val thm3 = Thm.INST [``f:bir_imm_t -> string`` |-> “translate_Imm_to_string”] thm2;
val thm4 = SIMP_RULE (pure_ss) [bir_exp_t_distinct] thm3;

val tm1 = (fst o boolSyntax.dest_disj o boolSyntax.rhs o Thm.concl) thm2;
val thm4 = ASSUME tm1;
val thm5 = (SIMP_RULE (srw_ss()) [b2n_def,translate_Imm_to_string_def] thm4);
val tm2 = (lhs o concl) thm5;
val thm6 = Thm.INST [ ``str:string`` |-> tm2] (SPEC_ALL const_name_from_str_def);
val thm7 =  CONJ thm5 thm6;  
val tm3 = (rhs o concl) thm5;
val thm8 = Thm.INST [ ``str:string`` |-> tm3] (SPEC_ALL const_name_from_str_def);
val thm9 = CONJ thm7 thm8;
    
val tm4 =  concl thm7;
val thm8 = SIMP_CONV (srw_ss()) [thm6] tm4;
val thm9 =  CONJ thm7 thm8;
    Thm.TRANS thm7 thm8
    val thm8 = Thm.INST [ ``v:string`` |-> tm3] thm7;
val tm3 = (rhs o concl) thm6;
val thm1 = SIMP_CONV (srw_ss()) [] tm7

	SIMP_RULE (pure_ss) []
	     EVAL (concl thm5)
    EXISTS (``b:bir_imm_t``,imm) thm7
    CHOOSE (imm,)
	    val thm7 = Thm.INST [ ``b:bir_imm_t`` |-> imm] thm6;
 SIMP_RULE (pure_ss) [AND_INTRO_THM] thm5  


(*working well
 val thm1 = Thm.INST [``bb:bir_exp_t`` |-> exp] (SPEC_ALL bir_exp_t_nchotomy); 
	    val thm2 = SIMP_RULE (bool_ss) [bir_exp_t_distinct,AND_CLAUSES,OR_CLAUSES,EXISTS_OR_THM] thm1;
	    val thm3 = SIMP_RULE (pure_ss) [bir_exp_t_11] thm2;
	    val thm4 = if ((Teq o concl) (SIMP_RULE (srw_ss()) [] thm3)) then ASSUME (concl thm2) else raise ERR "thm is not true" ""; 
	    val tm1 = (lhs o snd o dest_exists o concl) thm3;    
	    val tm2 = (rand o concl) (SPEC_ALL Name_t_nchotomy);    
	    val tm3 = mk_comb(tm2,PubName_tm);
	    val tm4	= (rand o rhs o concl) (SIMP_CONV std_ss [] tm3);
	    val tm5 = mk_comb(tm4,“(toString ∘ b2n) ^tm1”);
	    val tm6	= (rhs o rhs o concl) (SIMP_CONV (srw_ss()) [w2n_def,b2n_def] tm5);
	    val tm7 = mk_comb(Con_tm, tm6);
	    val thm5 = Thm.INST [``SS:SapicTerm_t`` |-> tm7] (SPEC_ALL SapicTerm_t_nchotomy);
	    val thm6 = SIMP_RULE (bool_ss) [ SapicTerm_t_distinct,AND_CLAUSES,OR_CLAUSES,EXISTS_OR_THM] thm5;
	    val thm7 = PROVE_HYP thm4 thm6;

also working well 

   val imm = dest_BExp_Const exp;
val thm1 = Thm.INST [``x:bir_exp_t`` |-> exp] (bir_exp_t_case_eq); 
val thm2 = Thm.INST_TYPE [alpha |-> “:string”] thm1;
val thm3 = Thm.INST [``f:bir_imm_t -> string`` |-> “translate_Imm_to_string”] thm2;
val thm4 = SIMP_RULE (bool_ss) [bir_exp_t_distinct,AND_CLAUSES,OR_CLAUSES,EXISTS_OR_THM] thm3;
val (lthm,rthm) =  EQ_IMP_RULE thm4;
val thm5 = IMP_TRANS rthm lthm;
val thm6 =  UNDISCH thm5;
val thm7 = SIMP_RULE (pure_ss) [bir_exp_t_11] thm4;
val thm8 = (SIMP_RULE (srw_ss()) [b2n_def,translate_Imm_to_string_def] thm7);
val tm2 = (lhs o concl) thm8;   
val thm9 = Thm.INST [ ``str:string`` |-> tm2] (SPEC_ALL const_name_from_str_def);
val thm10 =  REWRITE_RULE [thm8] thm9;

also working well

val thm1 = Thm.INST [``x:bir_exp_t`` |-> exp] (bir_exp_t_case_eq); 
val thm2 = Thm.INST_TYPE [alpha |-> “:SapicTerm_t”] thm1;
val thm3 = Thm.INST [``f:bir_imm_t -> SapicTerm_t`` |-> “translate_imm_to_sapic_term”] thm2;
val thm4 = SIMP_RULE (bool_ss) [bir_exp_t_distinct,AND_CLAUSES,OR_CLAUSES,EXISTS_OR_THM] thm3;
val (lthm,rthm) = EQ_IMP_RULE thm4;
val thm5 = IMP_TRANS rthm lthm;
val thm6 =  UNDISCH thm5;
val thm7 = SIMP_RULE (pure_ss) [bir_exp_t_11] thm6;
val thm8 = (SIMP_RULE (srw_ss()) [b2n_def,translate_imm_to_sapic_term_def] thm7);


UNDISCH (SIMP_CONV (srw_ss()) [] ((rand o concl) thm3))
SapicTerm_t_case_def
			tm0 = (rand o concl) Name_t_nchotomy										   mk_comb((concl translate_imm_to_sapic_term_def),tm1)
Name_t_nchotomy											   val thm10 =   SIMP_RULE (bool_ss) [] thm3;
UNDISCH thm4
val thm4 = Thm.INST [ ``imm:α word -> string`` |-> tm1] (SPEC_ALL translate_imm_to_sapic_term_def);
    
val thm8 = (SIMP_RULE (srw_ss()) [b2n_def,translate_imm_to_sapic_term_def] thm7);

val thm10 =  REWRITE_RULE [thm8] thm9;



    REWRITE_RULE [] thm4
val tm3 = (rhs o concl) thm5;
val thm8 = Thm.INST [ ``str:string`` |-> tm3] (SPEC_ALL const_name_from_str_def);
val thm9 = CONJ thm7 thm8;
    
val tm4 =  concl thm7;
val thm8 = SIMP_CONV (srw_ss()) [thm6] tm4;
val thm9 =  CONJ thm7 thm8;
    Thm.TRANS thm7 thm8
    val thm8 = Thm.INST [ ``v:string`` |-> tm3] thm7;
val tm3 = (rhs o concl) thm6;
val thm1 = SIMP_CONV (srw_ss()) [] tm7;
    (snd o EQ_IMP_RULE) thm6

 Thm.TRANS ((fst o EQ_IMP_RULE) thm4) ((fst o EQ_IMP_RULE) thm5)
   EXISTS
   val tm3 = (snd o dest_eq o rhs o concl) thm6;  
   val thm7 = SIMP_CONV (srw_ss()) [b2n_def,translate_Imm_to_string_def] (concl thm4);
    SNOC_CASES thm4
	       (ASM_SIMP_RULE (srw_ss()) [] thm4)
	       ASM_SIMP_RULE bool_ss [] (ASSUME (Term `x = 3`))
    
 SIMP_RULE (pure_ss) [bir_exp_t_distinct] thm3
 CONJ thm0 thm1
 MP bir_exp_t_distinct thm3
  val thm0 =  SIMP_CONV (srw_ss())  [bir_exp_t_distinct] (concl thm3)
  val thm = ASSUME exp

val patch_thms_m0modft_a202 = mk_patch_thms [
``(* copied an modified accordingly, based on "aa02" *)
  (bmr_ms_mem_contains (m0_mod_bmr (F,T)) ms
       (ms.base.REG RName_PC,[2w; 162w])) ==>
  (ms.countw <=+ 0xFFFFFFFFFFFFFFFEw) ==>
  ((m0_mod_bmr (F,T)).bmr_extra ms) ==>
  (aligned 1 (ms.base.REG RName_PC)) ==>
  (NextStateM0_mod ms =
      SOME
        <|base :=
          ms.base with
          <|REG :=
              (RName_PC =+ ms.base.REG RName_PC + 2w)
                ((RName_2 =+ ms.base.REG RName_PC + 8w) ms.base.REG);
            count := w2n ms.countw + 1; pcinc := 2w|>;
        countw := ms.countw + 1w|>)
``];

	    val tm8 = (lhs o snd o dest_exists o concl) thm6;
		val StepPatchThm = mk_oracle_thm "BirExptoSapicTerm";
val mk_patch_thms = List.map (fn tm => UNDISCH_ALL (StepPatchThm ([], tm)));
	    val thmls = mk_patch_thms [
``^exp ==>
  ^tm8
``];
ASSUME exp

val imm = dest_BExp_Const exp;
 val thm1 = Thm.INST [``x:bir_exp_t`` |-> exp] (bir_exp_t_case_eq); 
 val thm2 = Thm.INST_TYPE [alpha |-> “:string”] thm1;
 val thm3 = Thm.INST [``f:bir_imm_t -> string`` |-> “translate_Imm_to_string”] thm2;
 val thm4 = SIMP_RULE (bool_ss) [bir_exp_t_distinct,AND_CLAUSES,OR_CLAUSES,EXISTS_OR_THM] thm3;
 val (lthm,rthm) = EQ_IMP_RULE thm4;
 val thm5 = IMP_TRANS rthm lthm;
 val thm6 =  UNDISCH thm5;
 val thm7 = SIMP_RULE (pure_ss) [bir_exp_t_11] thm6;
 val thm8 = (SIMP_RULE (srw_ss()) [b2n_def,translate_Imm_to_string_def] thm7);
 val tm2 = (lhs o concl) thm8;   
 val thm9 = Thm.INST [ ``str:string`` |-> tm2] (SPEC_ALL const_name_from_str_def);
 val thm10 =  REWRITE_RULE [thm8] thm9;

val exp1 = “Con (Name PubName "112")”;
dest_type(type_of exp)
identical exp exp1

val imm = dest_BExp_Const exp
val tm0 = (rand o concl) w2n_def
val exp = “12w”
val tm1 = mk_comb(tm0,exp)
(SIMP_CONV std_ss [] tm1)
val thm1 = SIMP_CONV (srw_ss()) [b2n_def] “(num_to_dec_string ∘ b2n) ^imm”
SimpRHS thm1
SIMPR_RULE (srw_ss()) 
REWRITE_RULE [n2s_def,ASCIInumbersTheory.num_to_dec_string_def,w2n_def] thm

DB.find "ADD_CLAUSES"
*)*)

  in

 (* SIMP_RULE (srw_ss()) [b2n_def,translate_BinPred_to_string_def,translate_UnaryExp_to_string_def,size_of_bir_immtype_def,translate_BinExp_to_string_def,translate_Endian_to_string_def] to_st_thm *) 
fun bir_exp_to_sapic_term exp =
let
	val _ = ()
in
    (* Constants *)
    (* Manual tests
        val exp = ``BExp_Const (Imm64 112w)``;
		    bir_exp_to_sapic_term exp 
     *)
    if is_BExp_Const exp then
	let
	    val imm = dest_BExp_Const exp;
	    val thm0 = SIMP_CONV (srw_ss()) [b2n_def] “(num_to_dec_string ∘ b2n) ^imm”;
	    val cons = (snd o dest_eq o concl) thm0;
	    val sp_name = mk_Con (mk_Name (PubName_tm, cons));
	in
	    (sp_name,thm0)
	end
    (* Den *)
    (*
	val exp = ``(BExp_Den (BVar "MEM" (BType_Mem Bit32 Bit8)))``;
	val exp = “BExp_Den (BVar "oracle" (BType_Imm Bit32))”
     *)
    else if is_BExp_Den exp then
	let
          val (name,bir_type) = (dest_BVar o dest_BExp_Den) exp
          val thm0 = SPEC name (Thm.INST_TYPE [alpha |-> (type_of name)] EQ_REFL);
	  val sp_var = mk_TVar (mk_Var (name,(“0:int”)));
    in   
          (sp_var,thm0)
	end

    (* Memory constants *)
    (* val exp = ``BExp_MemConst Bit64 Bit8 abcd``; 
		   ``BExp_MemConst Bit128 Bit16 amap``,
    ``amap :128 |-> 16``
*)
    else if is_BExp_MemConst exp then
	
        let 
            val (addr_bir_ty, val_bir_ty, tm_map) = dest_BExp_MemConst exp;
	    val thm0 = SIMP_CONV (srw_ss()) [size_of_bir_immtype_def] “toString (((size_of_bir_immtype) ^addr_bir_ty) + ((size_of_bir_immtype) ^val_bir_ty))”; 
            val cons = (snd o dest_eq o concl) thm0;
            val sp_name = mk_Con (mk_Name (PubName_tm, cons));
	in
	    (sp_name,thm0)
        end
        handle e => raise wrap_exn "bir_exp_to_sapic_term::MemConst" e 
    (* Casts *)
    (* 
     val exp = ``BExp_Cast BIExp_LowCast
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32``;
     *)
    else if is_BExp_Cast exp then
        let
            val (casttyp, ex, sz) = (dest_BExp_Cast) exp;
	    val thm1 = (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def]) “(toString o size_of_bir_immtype) ^sz”;
            val cast_sz = (snd o dest_eq o concl) thm1;
	    val cast_sz_st = mk_Con (mk_Name (PubName_tm, cast_sz));
            val (val_st,thm2) = bir_exp_to_sapic_term ex;
	    val thm3 =  (SIMP_CONV (srw_ss()) [translate_Cast_to_string_def]) “translate_Cast_to_string ^casttyp”;
            val cast_ty = (snd o dest_eq o concl) thm3;
	    val trm_list = (listSyntax.mk_list ([val_st,cast_sz_st],SapicTerm_t_ty));
	    val fun_sig = pairSyntax.list_mk_pair [cast_ty,“(2:int)”,Public_tm, Constructor_tm];
	    val sp_fun = mk_FAPP (fun_sig,trm_list);
 	    val to_st_thm = CONJ (CONJ thm1 thm2) thm3;
        in
          (sp_fun,to_st_thm)
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
          val (exp_sap_tr,thm1) = bir_exp_to_sapic_term bir_exp
          val thm0 = (SIMP_CONV (srw_ss()) [translate_UnaryExp_to_string_def]) ``translate_UnaryExp_to_string ^uop``
          val uop_str = (snd o dest_eq o concl) thm0;
	  val trm_list = (listSyntax.mk_list ([exp_sap_tr],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair [uop_str,“(1:int)”,Public_tm, Constructor_tm];
	  val sp_fun = mk_FAPP (fun_sig,trm_list);
 	  val to_st_thm = CONJ thm1 thm0;
        in
          (sp_fun,to_st_thm)
        end
          handle e => raise wrap_exn "bir_exp_to_sapic_term::unary_exp" e

      (* Binary expressions *)
      else if is_BExp_BinExp exp then
        (* 
        val exp = ``(BExp_BinExp BIExp_Plus (BExp_Const (Imm64 112w)) (BExp_Const (Imm64 11w)))``;
        *)
        let
          val (bop, bir_exp1, bir_exp2) = (dest_BExp_BinExp) exp
          val (st_exp1,thm1) =  bir_exp_to_sapic_term bir_exp1
          val (st_exp2,thm2) =  bir_exp_to_sapic_term bir_exp2
          val thm0 = SIMP_CONV (srw_ss()) [translate_BinExp_to_string_def] ``translate_BinExp_to_string ^bop``;
          val st_bop = (snd o dest_eq o concl) thm0;
          val trm_list = (listSyntax.mk_list ([st_exp1,st_exp2],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair [st_bop,“(2:int)”,Public_tm, Constructor_tm];
	  val sp_fun = mk_FAPP (fun_sig,trm_list);
 	  val to_st_thm = CONJ (CONJ thm1 thm2) thm0;
        in
          (sp_fun,to_st_thm)
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
              val (st_exp1,thm1) =  bir_exp_to_sapic_term bir_exp1
              val (st_exp2,thm2) =  bir_exp_to_sapic_term bir_exp2
	      val thm0 = SIMP_CONV (srw_ss()) [translate_BinPred_to_string_def] ``translate_BinPred_to_string ^bpred``;
              val st_bp = (snd o dest_eq o concl) thm0;
	      val trm_list = (listSyntax.mk_list ([st_exp1,st_exp2],SapicTerm_t_ty));
	      val fun_sig = pairSyntax.list_mk_pair [st_bp,“(2:int)”,Public_tm, Constructor_tm];
	      val sp_fun = mk_FAPP (fun_sig,trm_list);
 	      val to_st_thm = CONJ (CONJ thm1 thm2) thm0;
          in
              (sp_fun,to_st_thm)
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
          val (lhs,lthm) = bir_exp_to_sapic_term bir_lhs
          val (rhs,rthm) = bir_exp_to_sapic_term bir_rhs
          val trm_list = (listSyntax.mk_list ([lhs,rhs],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"MemEq"”,“(2:int)”,Public_tm, Constructor_tm]
	  val sp_fun = mk_FAPP (fun_sig,trm_list);
 	  val to_st_thm = (CONJ lthm rthm)
          in
              (sp_fun,to_st_thm)
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
          val (st_cond_exp,thm1) = bir_exp_to_sapic_term bir_cond_exp
          val (st_then_exp,thm2) = bir_exp_to_sapic_term bir_then_exp
          val (st_else_exp,thm3) = bir_exp_to_sapic_term bir_else_exp
          val trm_list = (listSyntax.mk_list ([st_cond_exp,st_then_exp,st_else_exp],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"IfThenElse"”,“(3:int)”,Public_tm, Destructor_tm]
          val sp_fun = mk_FAPP (fun_sig,trm_list);
 	  val to_st_thm = CONJ (CONJ thm3 thm2) thm1
          in
              (sp_fun,to_st_thm)
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
          val (mem_st,thm1) = bir_exp_to_sapic_term bir_mem;
          val (base_addr_st,thm2) = bir_exp_to_sapic_term bir_addr;
	  val thm3 =  (SIMP_CONV (srw_ss()) [translate_Endian_to_string_def]) ``translate_Endian_to_string ^bir_endi``;
	  val ld_endi = (snd o dest_eq o concl) thm3
	  val ld_endi_st = mk_TVar (mk_Var (ld_endi,(“0:int”)));
	  val thm4 = (SIMP_CONV (srw_ss()) [size_of_bir_immtype_def]) “(toString o size_of_bir_immtype) ^bir_val_ty”;
	  val ld_sz = (snd o dest_eq o concl) thm4; 
	  val ld_sz_st = mk_Con (mk_Name (PubName_tm, ld_sz)); 
          val trm_list = (listSyntax.mk_list ([mem_st,base_addr_st,ld_endi_st,ld_sz_st],SapicTerm_t_ty));
	  val fun_sig = pairSyntax.list_mk_pair[“"Load"”,“(4:int)”,Public_tm, Constructor_tm];
	  val sp_fun = mk_FAPP (fun_sig,trm_list);
 	  val to_st_thm =  CONJ (CONJ (CONJ thm1 thm2) thm3) thm4
        in
              (sp_fun,to_st_thm)
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
              val (mem_st,thm1) = bir_exp_to_sapic_term bir_mem;
              val (base_addr_st,thm2) = bir_exp_to_sapic_term bir_addr;
              val (val_st,thm3) = bir_exp_to_sapic_term bir_val;
	      val thm4 = (SIMP_CONV (srw_ss()) [translate_Endian_to_string_def]) ``translate_Endian_to_string ^bir_endi``;
	      val st_endi = (snd o dest_eq o concl) thm4; 
	      val st_endi_st = mk_TVar (mk_Var (st_endi,(“0:int”)));
              val trm_list = (listSyntax.mk_list ([ mem_st,base_addr_st,st_endi_st,val_st],SapicTerm_t_ty));
	      val fun_sig = pairSyntax.list_mk_pair[“"Store"”,“(4:int)”,Public_tm, Destructor_tm]
              val sp_fun = mk_FAPP (fun_sig,trm_list);
 	      val to_st_thm =  CONJ (CONJ (CONJ thm1 thm2) thm3) thm4;
        in
              (sp_fun,to_st_thm)
          end
          handle e => raise wrap_exn "bir_exp_to_sapic_term::mem_store" e
      else
          raise ERR "bir_exp_to_sapic_term" ("Don't know BIR expression: " ^ (term_to_string exp))
end; 


(*

val exp = “BExp_Store
                        (BExp_Store
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Minus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 48w))) BEnd_LittleEndian
                           (BExp_Den (BVar "R29" (BType_Imm Bit64))))
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 40w))) BEnd_LittleEndian
                        (BExp_Den (BVar "R30" (BType_Imm Bit64)))”;

val (sp_term,main_thm) = bir_exp_to_sapic_term exp;

SIMP_RULE (srw_ss()) [b2n_def,translate_BinPred_to_string_def,translate_UnaryExp_to_string_def,size_of_bir_immtype_def,translate_BinExp_to_string_def,translate_Endian_to_string_def,translate_Cast_to_string_def] main_thm
*)    
    
  end (* local *)

end (* translate_to_sapicLib *)


