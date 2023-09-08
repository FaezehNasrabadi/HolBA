open HolKernel Parse boolLib bossLib;
open sumTheory;
open pred_setTheory;
open parallelcompositionemptydeductionTheory;
open propertyTheory;
open sigma_algebraTheory;
open listTheory;
open tautLib;
open interleavingTheory;
val _ = new_theory "derived_rules_emptydeduction";






























val _ = export_theory();
