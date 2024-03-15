open HolKernel Parse
open PPBackEnd;
open boolLib pairLib;
open bir_inst_liftingLib;
open bir_inst_liftingHelpersLib;
open gcc_supportLib;

val _ = Parse.current_backend := PPBackEnd.vt100_terminal;
val _ = set_trace "bir_inst_lifting.DEBUG_LEVEL" 2;

val _ = new_theory "WhatsApp";

val arch_str         = "arm8";

val dafilename = "disassembly_withname_whatsappDesktop.da";
(* val dafilename = "whatsappDesktop_registration.da"; *)
(* val dafilename = "test_iphone.da"; *)
 
val prog_range       = ((Arbnum.fromInt 0x000000010000505c), (Arbnum.fromInt 0x0000000102cf9bf3));                     

val _ = print_with_style_ [Bold, Underline] ("Lifting " ^ dafilename ^ " (" ^ arch_str ^ ")\n");

val symbs_sec_text = [
    "initWithPhoneNumber:language:locale:fbUUID:waUUID:chatPrivateKey:e2eKeyBundle:smbClientSignedVNameCertData:",
    "FUN_102aee9e4",
    "FUN_102b2fba0",
    "FUN_102aedbc0",
    "FUN_102aedbf4",
    "FUN_102aedc9c",
    "FUN_102aee2bc",
    "FUN_102aedf98",
    "FUN_102aede18",
    "FUN_102aee634",
    "FUN_102b23100",
    "FUN_102af3544",
    "_objc_retain",
    "_objc_msgSendSuper2",
    "FUN_102bf1680",
    "_objc_msgSend",
    "FUN_102aeec90",
    "_objc_storeStrong",
    "FUN_102c00600",
    "FUN_102aedbc8",
    "_objc_release",
    "FUN_102c5eeco",
    "_objc_retainAutoreleasedReturnValue",
    "FUN_102cd9660",
    "FUN_102b0f8b8",
    "FUN_102c8b160",
    "FUN_102cf4e40",
    "FUN_102cf4e60",
    "FUN_102c2c900",
    "FUN 102c597c0",
    "FUN_102c8a800",
    "FUN_102af6cac",
    "FUN_102aeed00",
    "FUN_102bec000",
    "FUN_102aedb7c",
    "FUN_102aedb98",
    "FUN_102c599a0",
    "FUN_102c39180",
    "FUN_102c12ea0",
    "FUN_102af516c",
    "FUN_102c0d940",
    "FUN_102aff6bc",
    "FUN_102c59840",
    "FUN_102cd1360",
    "FUN_102c59840",
    "FUN_102aedb6c",
    "FUN_102cd1380",
    "FUN_102c12da0",
    "FUN_102cf2420",
    "FUN_102b07884",
    "FUN 102c862e0",
    "FUN_102aef5f0",
    "FUN_102bec000",
    "FUN_102aedb74",
    "FUN_102be2ba0",
    "FUN_102b0af4c",
    "_objc_opt_class",
    "FUN_102c20c80",
    "FUN_102aef2bc",
    "FUN_102afd32c",
    "FUN_102aedbec",
    "_objc_release",
    "FUN_102aeddOc",
    "FUN_102aeec80",
    "FUN_102aeecco",
    "FUN_102aedc34",
    "FUN_102aedbe4",
    "FUN_102aedb90",
    "FUN_102aee0d4",
    "FUN_102af3544",
    "_WAHandleFailureInFunction",
    "___stack_chk_fail"
  ];
        
val symb_filter_lift = fn secname =>
  case secname of
    ".text" => (fn symbname => List.exists (fn x => x = symbname) symbs_sec_text)
  | _       => (K false);

val (region_map, sections) = read_disassembly_file_regions_filter symb_filter_lift  dafilename;

(* val (region_map, sections) = read_disassembly_file_regions  dafilename; *)
                            
val (thm, errors) = bmil_arm8.bir_lift_prog_gen prog_range sections;

val _ = save_thm ("WhatsApp_thm", thm);



val _ = export_theory();



