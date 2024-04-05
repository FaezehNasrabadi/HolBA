open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavinggeneraldeductionTheory;
open parallelcompositiongeneraldeductionTheory;
open translate_to_sapicTheory;
open derived_rules_generaldeductionTheory;
open sbir_treeTheory;
open sapicplusTheory;
open messagesTheory;
open dolevyaoTheory;

val _ = new_theory "sapic_comp_DY_sapicplus";

     
val compose_sapic_vs_DY_spaicplus_thm = store_thm(
  "compose_sapic_vs_DY_spaicplus_thm",
  ``∀Re0 NRe0 i Re NRe Sym Sym' P P' (MTrn:('event1 + (Name_t, Var_t) sync_event, 'pred1, sapic_position_configuration_t, Var_t) mtrel) (Ded:('pred1) tded) (ded3:('pred1 + DYpred) tded).
(comptraces (MTrn,Ded) (DYmultranrel,DYdeduction) (Sym,P,(Pconfig (P0,0,Re0,NRe0)),ESt) (Sym',P',(Pconfig (P,i,Re,NRe)),ESt)) = (sapic_plus_traces sapic_plus_position_multi_transitions (Pconfig_plus (P0,0,Re0,NRe0)) (Pconfig_plus (P,i,Re,NRe)))``,
rewrite_tac[binterleave_composition_generaldeduction,binterleave_ts,symbtree_to_sapic_trace_inclusion_thm] >>
FULL_SIMP_TAC (list_ss++pred_setSimps.PRED_SET_ss++boolSimps.LIFT_COND_ss++boolSimps.EQUIV_EXTRACT_ss) [SUBSET_DEF] >>
     metis_tac[]
              );




val _ = export_theory();
