open HolKernel Parse boolLib bossLib;

open pred_setTheory;

open bir_symbTheory;

open HolBACoreSimps;



val _ = new_theory "birs_eventstep";


    

val birs_exec_event_step_def = Define `
    birs_exec_event_step p state event states =
  case event of
    | NONE => (birs_exec_step p state states)
    | SOME stm => (birs_exec_step p state states)(*need to be fix*)
`;


val _ = export_theory();
