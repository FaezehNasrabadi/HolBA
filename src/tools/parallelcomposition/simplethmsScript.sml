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

val TRANFUN_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
  "TRANFUN"
  ‘TRANFUN (C: 'config) (t: 'event list) = {C'| (TRANSITION C t C')}’;

  
val trans_def =
Define`
      trans C t C'  = if t = [] then
        C = C'
     else C ≠ C'
            `;
            
val transfunc_def =
Define`
      transfunc (C: 'config) (t: 'event list) = {C'| (trans C t C')}
                         `;      
(*  
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
      traces C t C'  =   {t| TRANSITION C t C'}
                         `;


 
val traceempty_thm = store_thm(
  "traceempty_thm", ``
∀C C1 C2. ((TRANSITION C [] C1) ∧ (TRANSITION C [] C2)) ⇒ ((traces C [] C1) ⊆ (traces C [] C2))
                                       ``,
REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]                                                                      
  );


val traceeq_thm = store_thm(
  "traceeq_thm", ``
∀C1 t1 C1' C2 t2 C2'. ((TRANSITION C1 t1 C1') ∧ (TRANSITION C2 t2 C2') ∧ (t1 = t2)) ⇒ ((traces C1 t1 C1') = (traces C2 t2 C2'))
                                       ``,
 REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );

val traceunion_thm = store_thm(
  "traceunion_thm", ``
∀C t1 C' C'' t2. ((TRANSITION C t1 C') ∧ (TRANSITION C' t2 C'') ∧ (TRANSITION C (APPEND t1 t2) C'') ∧ (t1 ≠ []) ∧ (t2 ≠ [])) ⇒ (((traces C t1 C') ∪ (traces C' t2 C'')) = (traces C (APPEND t1 t2) C''))
                                       ``,
 REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );

  
val tracesubset1_thm = store_thm(
  "tracesubset1_thm", ``
∀C t1 C' C'' t2. ((TRANSITION C t1 C') ∧ (TRANSITION C' t2 C'') ∧ (TRANSITION C (APPEND t1 t2) C'') ∧ (t1 ≠ []) ∧ (t2 ≠ [])) ⇒ ((traces C t1 C') ⊆ (traces C (APPEND t1 t2) C''))
                                       ``,
 REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );

val tracesubset2_thm = store_thm(
  "tracesubset2_thm", ``
∀C t1 C' C'' t2. ((TRANSITION C t1 C') ∧ (TRANSITION C' t2 C'') ∧ (TRANSITION C (APPEND t1 t2) C'') ∧ (t1 ≠ []) ∧ (t2 ≠ [])) ⇒ ((traces C' t2 C'') ⊆ (traces C (APPEND t1 t2) C''))
                                       ``,
 REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );
 (* 
val tracesubset_thm = store_thm(
  "tracesubset_thm", ``
∀C t1 C' C'' t2. ((TRANSITION C t1 C') ∧ (TRANSITION C' t2 C'') ∧ (t1 ≠ []) ∧ (t2 ≠ [])) ⇒ (TRANSITION C (APPEND t1 t2) C'')
                                       ``,
                            REWRITE_TAC[transfunc_def]   REWRITE_TAC[trans_def]         REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >>
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
 Induct_on `t2`
                 rw[]
                 REWRITE_TAC[UNION_DEF]
                 rw[]
                        PAT_X_ASSUM ``!C C1. A`` (ASSUME_TAC o (Q.SPECL [`C`,`C1`]))
                                                                                                                 REWRITE_TAC[LENGTH]
                                                                                                                 REWRITE_TAC[LENGTH_CONS]
                                                                                                                 Cases_on `(t1 = [] ∧ t2 = [])`
                                                                                                                          Cases_on `C = C'`
  );  

METIS_TAC(Defn.eqns_of TRANSITION_defn)
ASM_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) []
             Induct_on `t`
                       Q.EXISTS_TAC `C'` 
                 rw[]
                 REWRITE_TAC[TL_DEF]
                 rw[]
                        PAT_X_ASSUM ``!C C1. A`` (ASSUME_TAC o (Q.SPECL [`C`,`C1`]))
                                                                                                                 REWRITE_TAC[LENGTH]
                                                                                                                 REWRITE_TAC[LENGTH_CONS]
                                                                                                                        Cases_on `t1 = t2`
REWRITE_TAC[SUBSET_EMPTY]
val TRACES_defn = Lib.with_flag (Defn.def_suffix, "") Defn.Hol_defn
  "TRACES"
  ‘TRACES C t C'  =
   if (TRANSITION C t C') then {t}
   else {}
  ’;          DB.find "SET_DEF";
    REWRITE_TAC[DISCH_ALL]
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

             DB.find_in "LESS" (DB.find "LENGTH");

             

val traces_def =
Define`
      traces C t C'  =   if ((TRANSITION C t C') ∧ t ≠ []) then {t} else {}
                         `;

                         val traceempty_thm = store_thm(
  "traceempty_thm", ``
∀C C1 C2. ((TRANSITION C [] C1) ∧ (TRANSITION C [] C2)) ⇒ ((traces C [] C1) ⊆ (traces C [] C2))
                                       ``,
REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> REWRITE_TAC[traces_def,SUBSET_EMPTY]                                                                       
  );


val traceeq_thm = store_thm(
  "traceeq_thm", ``
∀C1 t1 C1' C2 t2 C2'. ((TRANSITION C1 t1 C1') ∧ (TRANSITION C2 t2 C2') ∧ (t1 = t2)) ⇒ ((traces C1 t1 C1') = (traces C2 t2 C2'))
                                       ``,
 REWRITE_TAC[traces_def] >> REWRITE_TAC(Defn.eqns_of TRANSITION_defn) >> rw[]
  );
*)
val _ = export_theory();
