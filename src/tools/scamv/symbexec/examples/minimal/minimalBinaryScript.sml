open HolKernel Parse

open bir_inst_liftingLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = print_with_style [Bold, Underline] "Lifting minimal-aarch64.da\n";

val (region_map, minimal_sections) = read_disassembly_file_regions
        "minimal-aarch64.da";

val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen ((Arbnum.fromInt 0),
 (Arbnum.fromInt 0x1000000)) minimal_sections

val _ = new_theory "minimalBinary";
val _ = save_thm ("minimal_arm8_THM", thm_arm8);
val _ = export_theory();

