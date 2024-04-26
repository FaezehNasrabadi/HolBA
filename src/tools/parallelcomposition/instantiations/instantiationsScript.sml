open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open parallelcompositionconcreteTheory;
open interleavingconcreteTheory;
open parallelcompositiongeneraldeductionTheory;
open interleavinggeneraldeductionTheory;
open derived_rules_generaldeductionTheory;
open bir_comp_attacker_vs_sbir_comp_DYTheory;
open arm8_vs_bir_comp_attackerTheory;
open sapic_comp_DY_sapicplusTheory;
open sbir_sapic_comp_DYTheory;
open traceinclusionTheory;
open XORexampleTheory;
val _ = new_theory "instantiations";






    
  
val _ = export_theory();

