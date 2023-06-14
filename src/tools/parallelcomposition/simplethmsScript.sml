open HolKernel Parse boolLib bossLib;
open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;

val _ = new_theory "simplethms";

val TRANSITION_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
  "TRANSITION"
  ‘TRANSITION C t C'  =
     if t = [] then
        C = C'
     else C ≠ C'’;
(*

val transition_def =
Define`
      transition C t C'  = if t = [] then
        C = C'
     else C ≠ C'
                         `;      
val TRANSITION_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
                         "TRANSITION"
                         ‘TRANSITION C t C'  =
                          case t of
                            []      => (C = C')
                          | [e] => (C ≠ C')
                          | (e::ev) => (∃C''. (TRANSITION C [e] C'') ∧ (TRANSITION C'' ev C'))’;   *)  
     
val relEq_thm = store_thm(
  "relEq_thm", ``
∀M1 M2 C t C'. (M1 = M2) ⇒ ((M1 C t C') = (M2 C t C'))
                                       ``,
  REPEAT GEN_TAC >> REPEAT STRIP_TAC >> rw[]
  );


val transempty_thm = store_thm(
  "transempty_thm", ``
∀C t C'. ((TRANSITION C t C') ∧ (t = []))  ⇒ (C = C')
                                       ``,
 REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );

val eqconfig_thm = store_thm(
  "eqconfig_thm", ``
∀C t. (TRANSITION C t C)  ⇒ (t = [])
                                       ``,
 REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );

val transnonempty_thm = store_thm(
  "transnonempty_thm", ``
∀C t C'. ((TRANSITION C t C') ∧ (t ≠ []))  ⇒ (C ≠ C')
                                       ``,
 REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );

val noneqconfig_thm = store_thm(
  "noneqconfig_thm", ``
∀C t C'. ((TRANSITION C t C') ∧ (C ≠ C'))  ⇒ (t ≠ [])
                                       ``,
 REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  ); 


val traces_def =
Define`
      traces C t C'  =   if ((TRANSITION C t C') ∧ t ≠ []) then {t} else {}
                         `;


(*  
val tracesubsetempty_thm = store_thm(
  "tracesubsetempty_thm", ``
∀C1 t1 C1' C2 C2'. ((traces C1 t1 C1') ⊆ (traces C2 [] C2'))  ⇒ (t1 = [])
                                       ``,

REWRITE_TAC[traces_def,SUBSET_EMPTY] >>
REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
                                               
  );
  

REWRITE_TAC[SUBSET_EMPTY]
val TRACES_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
  "TRACES"
  ‘TRACES C t C'  =
   if (TRANSITION C t C') then {t}
   else {}
  ’;          
    REWRITE_TAC[EMPTY_DEF]
∀M1 M2 C1 C2. (((M1 C1 [] C1) = T) ∧ ((M2 C2 [] C2) = T) ∧ (C1 = C2)) ⇒ (M1 = M2)
∀M1 M2 C1 C2. ((M1 C1 [] C1) = (M2 C2 [] C2)) ⇒ (C1 = C2)
∀M1 M2 C1 C2 t. ((t = []) ∧ (M1 C1 t C1 ⇒ M2 C2 t C2)) ⇒ ((M1 C1 []) ⊆ (M2 C2 []))

   map DISCH_ALL (Defn.eqns_of N_aux_defn)     
REPEAT GEN_TAC >>
REPEAT STRIP_TAC >>
EQ_TAC
rw[] >>   
 ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
 RSUBSET
Induct_on `x`
 Cases_on `M1 = M2` >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
ASM_REWRITE_TAC [SUBSET_DEF]>>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []>>
*)
val _ = export_theory();
