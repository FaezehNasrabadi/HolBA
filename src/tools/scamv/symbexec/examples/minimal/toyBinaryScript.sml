<<<<<<< HEAD
open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib;
=======
open HolKernel Parse;
open PPBackEnd;
open bir_inst_liftingHelpersLib;

open bir_inst_liftingLib;
open gcc_supportLib
>>>>>>> 24a6f6f2aba3708ecd62e9f1b7ba9b6ecc72edcc

val _ = Parse.current_backend := PPBackEnd.vt100_terminal
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style [Bold, Underline] "Lifting toy-aarch64.da\n";

val (region_map, minimal_sections) = read_disassembly_file_regions
        "toy-aarch64.da";

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen 
            ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000)) minimal_sections

val _ = new_theory "toyBinary";
val _ = save_thm ("toy_arm8_THM", thm_arm8);
val _ = export_theory();
