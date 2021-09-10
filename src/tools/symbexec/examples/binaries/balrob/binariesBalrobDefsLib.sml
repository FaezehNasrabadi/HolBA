structure binariesBalrobDefsLib =
struct


(* val symbs_sec_text = [ *)
(*     "imu_handler_pid_entry", *)
(*     "motor_set_f", *)
(*     "motor_set", *)
(*     "motor_set_l", *)
(*     "motor_set_r", *)
(*     "motor_prep_input", *)
(*     "motor_prep_input_ct", *)
(*     "timer_read", *)
(*     "atan2f_own", *)
(*     "abs_own", *)
(*     "pid_msg_write", *)
(*     "__aeabi_f2iz", *)
(*     "__aeabi_fmul", *)
(*     "__aeabi_i2f", *)
(*     "__aeabi_fadd", *)
(*     "__aeabi_fcmplt", *)
(*     "__aeabi_fsub", *)
(*     "__aeabi_fdiv", *)
(*     "__lesf2", *)
(*     "__clzsi2" *)
(*   ]; *)
(*
val symbs_sec_text = [
    "increment_iv",
    "PKCS11_initialize",
    "PKCS11_generate_key",
    "PKCS11_wrap_key",
    "PKCS11_unwrap_key",
    "PKCS11_encrypt_init",
    "PKCS11_decrypt_init",
    "PKCS11_encrypt",
    "PKCS11_decrypt",
    "add_key",
    "set_iv"
    ];


val symbs_sec_text = [
    "SSL_Initialize",
    "SSL_AddRootCertificate",
    "SSL_AddCRL",
    "SSL_Reset",
    "SSL_Create",
    "SSL_Destroy",
    "SSL_Process",
    "SSL_Cleanup",
    "DigestInit",
    "DigestMsg",
    "DigestInit1",
    "DigestInit2",
    "DigestBlock",
    "DigestMsg2",
    "DigestPad2",
    "DigestOut2",
    "ParseServerMsg",
    "ParseHandshake",
    "ParseChangeCipherSpec",
    "ParseServerHello",
    "ParseServerHelloDone",
    "VerifyServerFinished",
    "ParseCertificateMsg",
    "ParseCertificateRequest",
    "ParseAppData",
    "CreateFinishedMsg",
    "CalculateMAC",
    "EncryptWithMAC",
    "CreateNetMsg",
    "ParseAlertMsg",
    "CreateAlertMsg"
];
 *)
(*







val symbs_sec_text = [
    "_IO_puts",
    "strlen",
    "__lll_lock_wait_private",
    "__overflow",
    "_Unwind_Resume",
    "BIO_new_connect",
    "BIO_new_accept",
    "malloc",
    "HMAC",
    "my_load_buf",
    "my_LoadBuf",
    "my_store_buf",
    "my_StoreBuf",
    "load_buf",
    "BIO_free",
    "EVP_sha1",
    "BIO_ctrl",
    "fprintf",
    "BIO_write",
    "ERR_print_errors_f",
    "BIO_pop",
    "client",
    "BIO_read",
    "socket_connect",
    "store_buf",
    "exit",
    "strlen",
    "get_key",
    "vfprintf",
    "my_memcpy_proxy",
    "client",
    "main",
    "get_payload",
    "get_key",
    "fail",
    "socket_listen",
    "socket_connect",
    "send",
    "recv",
    "wait_close"
];*)

val symbs_sec_text = [
    "server",
    "fail",
    "socket_listen",
    "__stack_chk_fail",
    "__libc_malloc",
    "EVP_sha1",
    "HMAC",
    "memcpy",
    "memcmp",
    "get_key",
    "main"
];
val arch_str         = "arm8";
val prog_range       = ((Arbnum.fromInt 0x00000000), (Arbnum.fromInt 0xffffffff));

(* val configs          = [("balrob", *)
(*                            ("balrob.elf.da", "balrob/balrob.elf.da.plus", "balrob/balrob.elf.mem"), *)
(*                            "balrob_program_THM", *)
(*                            ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003564), *)
(*                             (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)), *)
(*                             (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0)) *)
(*                         ), *)
(*                         ("balrob_opt", *)
(*                            ("balrob_opt.elf.da", "balrob/balrob_opt.elf.da.plus", "balrob/balrob_opt.elf.mem"), *)
(*                            "balrob_opt_program_THM", *)
(*                            ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003414), *)
(*                             (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x310)), *)
(*                             (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0)) *)
(*                         ), *)
(*                         ("balrob_ct", *)
(*                            ("balrob_ct.elf.da", "balrob/balrob_ct.elf.da.plus", "balrob/balrob_ct.elf.mem"), *)
(*                            "balrob_ct_program_THM", *)
(*                            ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0x00003564), *)
(*                             (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)), *)
(*                             (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0)) *)
(*                         )]; *)
(*val configs              = [ ("pkcs11",
                           ("pkcs11_guest.da", "balrob/pkcs11_guest.elf.da.plus", "balrob/pkcs11_guest.elf.mem"),
                           "pkcs11_THM",
                           ((Arbnum.fromInt 0xd0000000, Arbnum.fromInt 0xd0004dac),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
			     ) ];   

    val configs              = [ ("client",
                           ("client.da", "balrob/client.da.plus", "balrob/client.mem"),
                           "client_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0xffffffff),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
			     ) ];
 

 val configs              = [ ("simple",
                           ("simple.da", "balrob/simple.da.plus", "balrob/simple.mem"),
                           "simple_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0xffffffff),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
			     ) ];  *)  
    

 val configs              = [ ("server",
                           ("server.da", "balrob/server.da.plus", "balrob/server.mem"),
                           "server_THM",
                           ((Arbnum.fromInt 0x00000000, Arbnum.fromInt 0xffffffff),
                            (Arbnum.fromInt 0x10000000, Arbnum.fromInt (0x00000018 + 0x30d)),
                            (Arbnum.fromInt 0x10001000, Arbnum.fromInt 0x00000ff0))
			      ) ];



val symb_filter_lift = fn secname =>
  case secname of
      ".text" => (fn symbname => List.exists (fn x => x = symbname) symbs_sec_text)
    | _       => (K false);


end (* struct *)
