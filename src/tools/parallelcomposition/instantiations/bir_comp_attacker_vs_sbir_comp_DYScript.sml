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
open arm8_vs_bir_comp_attackerTheory;
open traceinclusionTheory;
val _ = new_theory "bir_comp_attacker_vs_sbir_comp_DY";

val bir_traces_def =
INST_TYPE [``:'cstate`` |-> ``:bir_state_t``,``:'cevent`` |-> ``:('a + 'ceventS)``] interleavingconcreteTheory.traces_def;
val bir_traces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) bir_traces_def;


    
val att_traces_def =
INST_TYPE [``:'cevent`` |-> ``:('cevent + 'ceventS)``] interleavingconcreteTheory.traces_def;
val att_traces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) att_traces_def;

    
val sbir_traces_def =
INST_TYPE [``:'symb`` |-> ``:Var_t``,``:'pred`` |-> ``:'SPpred``,``:'state`` |-> ``:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree``,``:'event`` |-> ``:(sbir_event + (Name_t, Var_t) sync_event)``] derived_rules_generaldeductionTheory.traces_def;
val sbir_traces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) sbir_traces_def;

    
val DY_traces_def =
INST_TYPE [``:'symb`` |-> ``:Var_t``,``:'pred`` |-> ``:DYpred``,``:'state`` |-> ``:DYstate``,``:'event`` |-> ``:(DYnsyc_event + (Name_t, Var_t) sync_event)``] derived_rules_generaldeductionTheory.traces_def;
val DY_traces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) DY_traces_def;


val bir_att_comptraces_def =
INST_TYPE [``:'cevent1`` |-> ``:'a``,``:'cevent2`` |-> ``:'cevent``,``:'cstate1`` |-> ``:bir_state_t``,``:'cstate2`` |-> ``:'cstate``] interleavingconcreteTheory.comptraces_def;
val bir_att_comptraces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) bir_att_comptraces_def;


val sbir_DY_comptraces_def =
INST_TYPE [``:'symb`` |-> ``:Var_t``,``:'pred1`` |-> ``:'SPpred``,``:'state1`` |-> ``:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree``,``:'event1`` |-> ``:sbir_event``,``:'pred2`` |-> ``:DYpred``,``:'state2`` |-> ``:DYstate``,``:'event2`` |-> ``:DYnsyc_event``,``:'eventS`` |-> ``:(Name_t, Var_t) sync_event``] derived_rules_generaldeductionTheory.comptraces_def;
val sbir_DY_comptraces_t = (fst o strip_comb o fst o dest_eq o snd o strip_forall o concl) sbir_DY_comptraces_def;

val compose_bir_attacker_vs_sbir_DY_thm = store_thm(
  "compose_bir_attacker_vs_sbir_DY_thm",
  ``
  ∀(T0:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree) (Tre:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree) (Sym:(Var_t -> bool)) (Sym':(Var_t -> bool)) (P:('SPpred + DYpred -> bool)) (P':('SPpred + DYpred -> bool)) (SBIR:((sbir_event + (Name_t, Var_t) sync_event), 'SPpred, (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree, Var_t) mtrel) (sbir_Ded:('SPpred) tded) (ded3:('SPpred + DYpred) tded).

        (
     (subset_one
      (^bir_traces_t ((InterpretRelOne:(((sbir_event + (Name_t, Var_t) sync_event), 'SPpred, (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree, Var_t) mtrel # ('SPpred) tded) -> ('a + 'ceventS, bir_state_t) mctrel) (SBIR,sbir_Ded)) ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0) ((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) Tre))
      (^sbir_traces_t (SBIR,sbir_Ded) (Sym,(IMAGE OUTL P),T0) (Sym',(IMAGE OUTL P'),Tre))) ∧
     (subset_two
      (^att_traces_t ((InterpretRelTwo:(( DYnsyc_event + (Name_t, Var_t) sync_event, DYpred, DYstate, Var_t) mtrel # (DYpred) tded) -> ( 'cevent + 'ceventS, 'cstate) mctrel) (DYmultranrel,DYdeduction)) ((InterpretStTwo:DYstate -> 'cstate) ESt) ((InterpretStTwo:DYstate -> 'cstate) ESt))
      (^DY_traces_t (DYmultranrel,DYdeduction) (Sym,(IMAGE OUTR P),ESt) (Sym',(IMAGE OUTR P'),ESt)))
) ==>
(subset_comp
   (^bir_att_comptraces_t (composeMuRe ((InterpretRelOne:(((sbir_event + (Name_t, Var_t) sync_event), 'SPpred, (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree, Var_t) mtrel # ('SPpred) tded) -> ('a + 'ceventS, bir_state_t) mctrel) (SBIR,sbir_Ded)) ((InterpretRelTwo:(( DYnsyc_event + (Name_t, Var_t) sync_event, DYpred, DYstate, Var_t) mtrel # (DYpred) tded) -> ( 'cevent + 'ceventS, 'cstate) mctrel) (DYmultranrel,DYdeduction))) (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) T0),((InterpretStTwo:DYstate -> 'cstate) ESt)) (((InterpretStOne:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree -> bir_state_t) Tre),((InterpretStTwo:DYstate -> 'cstate) ESt)))
   (^sbir_DY_comptraces_t (SBIR,sbir_Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,T0,ESt) (Sym',P',Tre,ESt))
)
``,
metis_tac[compose_vs_modules_conc_symb_thm]
);




(*


val compose_bir_attacker_vs_sbir_DY_thm = store_thm(
  "compose_bir_attacker_vs_sbir_DY_thm",
  ``∀(T0:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree) (Tre:(sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree) (birprog:'observation_type bir_program_t) (AMTrn:('cevent + 'ceventS, 'cstate) mctrel) (as: 'cstate) (as': 'cstate) (bs: bir_state_t) (bs': bir_state_t) (Sym:(Var_t -> bool)) (Sym':(Var_t -> bool)) (P:('SPpred + DYpred -> bool)) (P':('SPpred + DYpred -> bool)) (SBIR:((sbir_event + (Name_t, Var_t) sync_event), 'SPpred, (sbir_event, real,(bir_var_t, bir_exp_t) symb_interpret_t) stree, Var_t) mtrel) (sbir_Ded:('SPpred) tded) (ded3:('SPpred + DYpred) tded).

        (
        (subset_one
         ((bir_traces ((bir_mrel birprog):('a + 'ceventS, bir_state_t) mctrel) bs bs'):('a + 'cevetS) list -> bool)
         ((sbir_traces (SBIR,sbir_Ded) (Sym,(IMAGE OUTL P),T0) (Sym',(IMAGE OUTL P'),Tre)):(sbir_event + (Name_t, Var_t) sync_event) option list -> bool)) ∧
        (subset_two
         (att_traces AMTrn as as')
         (DY_traces (DYmultranrel,DYdeduction) (Sym,(IMAGE OUTR P),ESt) (Sym',(IMAGE OUTR P'),ESt)))
        ) ==> (
      subset_comp
      (bir_att_comptraces ((bir_mrel (birprog:'observation_type bir_program_t)) || AMTrn) (bs,as) (bs',as'))
      (sbir_DY_comptraces (SBIR,sbir_Ded) (DYmultranrel,DYdeduction) ded3 (Sym,P,T0,ESt) (Sym',P',Tre,ESt))
      ) ``,




  );

*)

val _ = export_theory();
