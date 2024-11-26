open HolKernel Parse
open PPBackEnd;
open boolLib pairLib;
open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "Alice";

val arch_str         = "arm8";

val dafilename = "alice.da";

val prog_range       =  ((Arbnum.fromInt 0x0), (Arbnum.fromInt 0x65));

val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ dafilename ^ " (" ^ arch_str ^ ")\n");

val (region_map, sections) = read_disassembly_file_regions  dafilename;
                            
val (thm, errors) = bmil_arm8.bir_lift_prog_gen prog_range sections;

val _ = save_thm ("Alice_thm", thm);

val (_, _, _, prog_tm) =
  (dest_bir_is_lifted_prog o concl)
  (DB.fetch "Alice" "Alice_thm");
(*
fun add_obs_to_bir embexp_params_memory current_prog =
    let 
	open bir_obs_modelTheory;

	fun add_obs mb t = rand (concl (EVAL ``add_obs_mem_addr_pc_armv8 ^mb ^t``));
	fun proginst_fun prog = inst [Type`:'observation_type` |-> Type`:bir_val_t`] prog;
	fun embexp_params_cacheable x = Arbnum.+ (Arbnum.fromInt 0x80000000, x);
	
	val mem_bounds =
	    let
		val (mem_base, mem_len) = embexp_params_memory;
		val mem_end = (Arbnum.- (Arbnum.+ (mem_base, mem_len), Arbnum.fromInt 128));
	    in
		pairSyntax.mk_pair
		    (wordsSyntax.mk_wordi (embexp_params_cacheable mem_base, 64),
		     wordsSyntax.mk_wordi (embexp_params_cacheable mem_end, 64))
	    end;
	val lifted_prog_w_obs = add_obs mem_bounds (proginst_fun (current_prog));

    in
	lifted_prog_w_obs
        end;
        

val prog_w_obs = add_obs_to_bir prog_range prog_tm;
*)

val _ = export_theory();



