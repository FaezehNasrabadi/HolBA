open HolKernel Parse boolLib bossLib;
open messagesTheory;
open synceventsTheory;

val _ = new_theory "dolevyao";

    
(* Predicates *)
val _ = Datatype `DYpred =
K SapicTerm_t (* Adversary can deduce term *)
| Fr SapicTerm_t (* Term is fresh *)
| Equ (SapicTerm_t # SapicTerm_t) (* both terms *)
      `;
    

      
(* Dolev-Yao deduction relation *)
val (DYdeduction_rules, DYdeduction_ind, DYdeduction_cases)
= Hol_reln
  `(∀(p:DYpred) (Pi: DYpred set). (p ∈ Pi) ==> (DYdeduction Pi p)) ∧
(∀(k:SapicTerm_t) (m:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (K k)) ∧ (DYdeduction Pi (K m))) ==> (DYdeduction Pi (K (FAPP  ("Enc", (2, Public, Constructor)) [m;k])))) ∧
(∀(k:SapicTerm_t) (m:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (K k)) ∧ (DYdeduction Pi (K (FAPP  ("Enc", (2, Public, Constructor)) [m;k])))) ==> (DYdeduction Pi (K m))) ∧
(∀(t1:SapicTerm_t) (t2:SapicTerm_t) (Pi: DYpred set). ((DYdeduction Pi (K t1)) ∧ (DYdeduction Pi (Equ (t1,t2)))) ==> (DYdeduction Pi (K t2))) 
`;
  
(* Dolev-Yao transition as a function *)


(* Dolev-Yao transition relation based on its function *)

val _ = export_theory();
