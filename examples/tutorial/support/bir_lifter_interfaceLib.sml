structure bir_lifter_interfaceLib =
struct

local

open HolKernel Parse;
open bir_inst_liftingLib;
open gcc_supportLib;

in

(*
val da_name = "../1-code/src/add_reg.da"
val prog_name = "add_reg"
val prog_interval = ((Arbnum.fromInt 0), (Arbnum.fromInt 0x1000000))
*)
fun lift_da_and_store prog_name da_name prog_interval =
  let
    val _ = print_with_style_ [Bold, Underline] ("Lifting "^da_name^"\n");

    val (region_map, aes_sections) = read_disassembly_file_regions da_name

    val (thm_arm8, errors) = bmil_arm8.bir_lift_prog_gen
			       prog_interval
			       aes_sections

    val (lift_app_1_tm, bir_prog_tm) = (dest_comb o concl) thm_arm8;
    val (_, bir_progbin_tm) = dest_comb lift_app_1_tm;

    val _ = print "\n\n";

    (* now save the definitions *)
    val bir_x_prog_var = mk_var("bir_"^prog_name^"_prog", type_of bir_prog_tm)
    val bir_x_prog_def = Define `^bir_x_prog_var = ^bir_prog_tm`;
    val bir_x_progbin_var = mk_var("bir_"^prog_name^"_progbin", type_of bir_progbin_tm)
    val bir_x_progbin_def = Define `^bir_x_progbin_var = ^bir_progbin_tm`;

    (* now save the lifter theorem using the definitions *)
    val bir_x_arm8_lift_THM = save_thm ("bir_"^prog_name^"_arm8_lift_THM",
	   REWRITE_RULE [GSYM bir_x_prog_def,
			 GSYM bir_x_progbin_def] thm_arm8);
  in
    ()
  end;

end

end
