open HolKernel Parse boolLib bossLib;
open bagTheory;

val _ = new_theory "messages";

    
(* Names *)
    
val _ = Datatype `NameTag_t = FreshName | PubName | NodeName`;    


val _ = Datatype `Name_t = Name NameTag_t string`;


(* Variables*)

val _ = Datatype `Var_t = Var string int`;
    
    
(* Function symbols *)

val _ = Datatype `Privacy_t = Private | Public`;

    
val _ = Datatype `Constructability_t = Constructor | Destructor`;



(* Terms *)	      

val _ = Datatype `SapicTerm_t =
	      Con   Name_t
	    | TVar  Var_t
	    | FAPP  (string # (int # Privacy_t # Constructability_t)) (SapicTerm_t list)`;

(*
val Tlist_Axiom = TypeBase.axiom_of “:SapicTerm_t list”;

val TMAP = new_recursive_definition
      {name = "TMAP",
       rec_axiom = Tlist_Axiom,
       def = “(!f:'a->'b. TMAP f [] = []) /\
                   (!f h t. TMAP f (h::t) = f h::TMAP f t)”};
val _ = export_rewrites ["TMAP"]
DB.find "lambda";
DB.find_in "SUM" (DB.find "MEM");

DB.find_in "APPEND" (DB.find "DROP");
DB.find "DROP";

*)

val TExist_def = Define`
(TExist t (FAPP n []) <=> F) /\
(TExist t' (FAPP n (t::ts)) <=> (t' = t) \/ TExist t' (FAPP n ts))`; 

                        
(* set of variables inside a term *)
                              
val fv_defn = Hol_defn "fv"
  `
                   (fv (Con _) = {}) /\
(fv (TVar v) = {v}) /\
(fv (FAPP n ts) = BIGUNION (IMAGE fv (set ts)))`;

val (fv_eqn0, fv_ind) =
 Defn.tprove (fv_defn,
   WF_REL_TAC `measure (CARD o FST)` THEN 
   PROVE_TAC [TExist_def]);                                                  


                                                
(* Detect ground term *)

val is_ground_term_def = Define `
                                (is_ground_term t =
(case t of
   (Con _) => T
 | (TVar _) => F
 | (FAPP n []) => T
 | (FAPP n ts) => (is_ground_term (HD ts) ∧ AND_EL(MAP is_ground_term (TL ts)))))

                                `;

                                        

(*val sapic_FV = 
 Define 
    `( sapic_FV (Con n) A      = if MEM (Con n) A then A else (Con n)::A) 
 /\  ( sapic_FV (TVar v) A     = if MEM (TVar v) A then A else (TVar v)::A)
 /\  ( sapic_FV (FAPP n ts) A  = (∀x∈ts. MEM x ts ∧ Asapic_FV x A))`;
                                                                        
(* Subset SapicTerm *)
(*TODO*)

val sapic_substn_def = Define`
  (sapic_substn x y (Con n) = if x = (Con n) then y else (Con n))
  `;


val sapic_substv_def = Define`
  (sapic_substv x y (TVar v) = if x = (TVar v) then y else (TVar v))
  `;
  
val sapic_substnv_def = Define`
                              (sapic_substnv x y t = (case t of
                                                        (Con n) => sapic_substn x y (Con n)
                                                      | (TVar v) => sapic_substv x y (TVar v)
                                                      | (FAPP n ts) => (if ts = [] then (FAPP n ts)
                                                                        else FAPP n (MAP (sapic_substnv x y) ts))

                                                     ))
                              `;*)

                                             



val _ = export_theory();
