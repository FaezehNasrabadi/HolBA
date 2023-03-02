(* You need to add the following code to bir_cfgLib *)
(*   fun toString t = *)
(*       case t of CFGNT_Jump     => "CFGNT_Jump" *)
(*               | CFGNT_CondJump => "CFGNT_CondJump" *)
(*               | CFGNT_Halt     => "CFGNT_Halt" *)
(*               | CFGNT_Basic    => "CFGNT_Basic" *)
(* 	      | CFGNT_Call lst => "CFGNT_Call" *)
(*               | CFGNT_Return   => "CFGNT_Return" *)

(* cfg tests
 ****************************************************************************)
    
open bir_gccLib;
open bir_prog_genLib;
open gcc_supportLib;



  fun bir_gcc_disassemble binfilename =
    let
	fun gcc_prefix () =
	    case Option.mapPartial (fn p => if p <> "" then SOME p else NONE)
				   (OS.Process.getEnv("HOLBA_GCC_ARM8_CROSS")) of
		NONE => raise ERR "scamv_gcc_prefix" "the environment variable HOLBA_GCC_ARM8_CROSS is not set"
              | SOME p => p;

      val gcc_prefix = gcc_prefix ();
      val path_asm_da = (binfilename ^ ".da");

      val commandline = (gcc_prefix ^ "objdump -d " ^ binfilename ^ " > " ^ path_asm_da);
      val _ = if OS.Process.isSuccess (OS.Process.system commandline) then ()
              else raise ERR "bir_gcc_disassemble" "disassembly failed somehow";
    in
      path_asm_da
    end;
  fun process_binary binfilename =
      let
	val da_file = bir_gcc_disassemble binfilename

	val (region_map, sections) = read_disassembly_file_regions da_file;
      in
	  (region_map, sections)
      end      

fun mk_key_from_address64 i addr = (mk_BL_Address o bir_immSyntax.mk_Imm64 o wordsSyntax.mk_word) (addr, Arbnum.fromInt i);
val infile = "/home/faezeh/Desktop/indirectjumpsexp/example.o";
val disasm = bir_gcc_disassemble infile;

val (region_map, sections) = process_binary infile;
val lifted_prog = bir_prog_genLib.lift_program_from_sections sections;

val lifted_prog =
   “BirProgram
      [<|bb_label := BL_Address_HC (Imm64 0w) "D10083FF (sub sp, sp, #0x20)";
         bb_statements :=
           [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Minus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 32w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 4w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 4w)
             "528000A0 (mov w0, #0x5                    // #5)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 5w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 8w)))|>;
       <|bb_label := BL_Address_HC (Imm64 8w) "B90017E0 (str w0, [sp, #20])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 20w))) 4);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 20w))) BEnd_LittleEndian
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 12w)))|>;
       <|bb_label := BL_Address_HC (Imm64 12w) "90000000 (adrp x0, 0 <main>)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 0w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 16w)))|>;
       <|bb_label := BL_Address_HC (Imm64 16w) "91000000 (add x0, x0, #0x0)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 20w)))|>;
       <|bb_label := BL_Address_HC (Imm64 20w) "910003E2 (mov x2, sp)";
         bb_statements :=
           [BStmt_Assign (BVar "R2" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 24w)))|>;
       <|bb_label := BL_Address_HC (Imm64 24w) "AA0003E3 (mov x3, x0)";
         bb_statements :=
           [BStmt_Assign (BVar "R3" (BType_Imm Bit64))
              (BExp_Den (BVar "R0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 28w)))|>;
       <|bb_label := BL_Address_HC (Imm64 28w) "A9400460 (ldp x0, x1, [x3])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_Den (BVar "R3" (BType_Imm Bit64))) BEnd_LittleEndian
                 Bit64);
            BStmt_Assign (BVar "R1" (BType_Imm Bit64))
              (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R3" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 32w)))|>;
       <|bb_label := BL_Address_HC (Imm64 32w) "A9000440 (stp x0, x1, [x2])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 3 (BExp_Den (BVar "R2" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_Den (BVar "R2" (BType_Imm Bit64))) 16);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store
                 (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                    BEnd_LittleEndian
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                 (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 36w)))|>;
       <|bb_label := BL_Address_HC (Imm64 36w) "B9401060 (ldr w0, [x3, #16])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2 (BExp_Den (BVar "R3" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R3" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 16w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 40w)))|>;
       <|bb_label := BL_Address_HC (Imm64 40w) "B9001040 (str w0, [x2, #16])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2 (BExp_Den (BVar "R2" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 16w))) 4);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R2" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 16w))) BEnd_LittleEndian
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 44w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 44w)
             "52800060 (mov w0, #0x3                    // #3)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 3w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 48w)))|>;
       <|bb_label := BL_Address_HC (Imm64 48w) "B9001FE0 (str w0, [sp, #28])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 28w))) 4);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 52w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 52w) "B9001BFF (str wzr, [sp, #24])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 24w))) 4);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                 (BExp_Const (Imm32 0w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 56w)))|>;
       <|bb_label := BL_Address_HC (Imm64 56w) "1400000D (b 6c <main+0x6c>)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 108w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 60w) "B9801BE0 (ldrsw x0, [sp, #24])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_SignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 24w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 64w)))|>;
       <|bb_label := BL_Address_HC (Imm64 64w) "D37EF400 (lsl x0, x0, #2)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_And (BExp_Const (Imm64 0xFFFFFFFFFFFFFFFFw))
                 (BExp_BinExp BIExp_LeftShift
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 2w))))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 68w)))|>;
       <|bb_label := BL_Address_HC (Imm64 68w) "910003E1 (mov x1, sp)";
         bb_statements :=
           [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 72w)))|>;
       <|bb_label := BL_Address_HC (Imm64 72w) "B8606820 (ldr w0, [x1, x0])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                    (BExp_Den (BVar "R1" (BType_Imm Bit64)))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                       (BExp_Den (BVar "R1" (BType_Imm Bit64))))
                    BEnd_LittleEndian Bit32) Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 76w)))|>;
       <|bb_label := BL_Address_HC (Imm64 76w) "7100041F (cmp w0, #0x1)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 1w)));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit32
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 1w)));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit32
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 1w)));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 1w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 80w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 80w)
             "54000081 (b.ne 60 <main+0x60>  // b.any)"; bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp (BExp_Den (BVar "ProcState_Z" BType_Bool))
             (BLE_Label (BL_Address (Imm64 84w)))
             (BLE_Label (BL_Address (Imm64 96w)))|>;
       <|bb_label := BL_Address_HC (Imm64 84w) "B9401FE0 (ldr w0, [sp, #28])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 28w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 88w)))|>;
       <|bb_label := BL_Address_HC (Imm64 88w) "11000400 (add w0, w0, #0x1)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_BinExp BIExp_Plus
                    (BExp_Cast BIExp_LowCast
                       (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                    (BExp_Const (Imm32 1w))) Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 92w)))|>;
       <|bb_label := BL_Address_HC (Imm64 92w) "B9001FE0 (str w0, [sp, #28])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 28w))) 4);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 96w)))|>;
       <|bb_label := BL_Address_HC (Imm64 96w) "B9401BE0 (ldr w0, [sp, #24])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 24w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 100w)))|>;
       <|bb_label := BL_Address_HC (Imm64 100w) "11000400 (add w0, w0, #0x1)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_BinExp BIExp_Plus
                    (BExp_Cast BIExp_LowCast
                       (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                    (BExp_Const (Imm32 1w))) Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 104w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 104w) "B9001BE0 (str w0, [sp, #24])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assert
              (BExp_unchanged_mem_interval_distinct Bit64 0 156
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 24w))) 4);
            BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
              (BExp_Store (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                 (BExp_BinExp BIExp_Plus
                    (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                    (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 108w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 108w) "B9401BE1 (ldr w1, [sp, #24])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R1" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 24w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 112w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 112w) "B94017E0 (ldr w0, [sp, #20])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 20w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 116w)))|>;
       <|bb_label := BL_Address_HC (Imm64 116w) "6B00003F (cmp w1, w0)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit32
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit32
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit32)
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 120w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 120w)
             "54FFFE2B (b.lt 3c <main+0x3c>  // b.tstop)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinPred BIExp_Equal
                (BExp_Den (BVar "ProcState_N" BType_Bool))
                (BExp_Den (BVar "ProcState_V" BType_Bool)))
             (BLE_Label (BL_Address (Imm64 124w)))
             (BLE_Label (BL_Address (Imm64 60w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 124w) "B9401FE0 (ldr w0, [sp, #28])";
         bb_statements :=
           [BStmt_Assert
              (BExp_Aligned Bit64 2
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
            BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Cast BIExp_UnsignedCast
                 (BExp_Load (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                    (BExp_BinExp BIExp_Plus
                       (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                       (BExp_Const (Imm64 28w))) BEnd_LittleEndian Bit32)
                 Bit64)];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 128w)))|>;
       <|bb_label := BL_Address_HC (Imm64 128w) "7100301F (cmp w0, #0xc)";
         bb_statements :=
           [BStmt_Assign (BVar "ProcState_C" BType_Bool)
              (BExp_nzcv_SUB_C
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 12w)));
            BStmt_Assign (BVar "ProcState_N" BType_Bool)
              (BExp_nzcv_SUB_N Bit32
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 12w)));
            BStmt_Assign (BVar "ProcState_V" BType_Bool)
              (BExp_nzcv_SUB_V Bit32
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 12w)));
            BStmt_Assign (BVar "ProcState_Z" BType_Bool)
              (BExp_nzcv_SUB_Z
                 (BExp_Cast BIExp_LowCast
                    (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                 (BExp_Const (Imm32 12w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 132w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 132w) "5400006D (b.le 90 <main+0x90>)";
         bb_statements := [];
         bb_last_statement :=
           BStmt_CJmp
             (BExp_BinExp BIExp_And
                (BExp_BinPred BIExp_Equal
                   (BExp_Den (BVar "ProcState_N" BType_Bool))
                   (BExp_Den (BVar "ProcState_V" BType_Bool)))
                (BExp_UnaryExp BIExp_Not
                   (BExp_Den (BVar "ProcState_Z" BType_Bool))))
             (BLE_Label (BL_Address (Imm64 136w)))
             (BLE_Label (BL_Address (Imm64 144w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 136w)
             "52800000 (mov w0, #0x0                    // #0)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 0w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 140w)))|>;
       <|bb_label := BL_Address_HC (Imm64 140w) "14000002 (b 94 <main+0x94>)";
         bb_statements := [];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 148w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 144w)
             "52800020 (mov w0, #0x1                    // #1)";
         bb_statements :=
           [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
              (BExp_Const (Imm64 1w))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 148w)))|>;
       <|bb_label :=
           BL_Address_HC (Imm64 148w) "910083FF (add sp, sp, #0x20)";
         bb_statements :=
           [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
              (BExp_BinExp BIExp_Plus
                 (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                 (BExp_Const (Imm64 32w)))];
         bb_last_statement := BStmt_Jmp (BLE_Label (BL_Address (Imm64 152w)))|>;
       <|bb_label := BL_Address_HC (Imm64 152w) "D65F03C0 (ret)";
         bb_statements := [];
         bb_last_statement :=
         BStmt_Jmp (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>]”;
(*   val lifted_prog =
   “BirProgram
   [
<|bb_label :=
                  BL_Address_HC (Imm64 65536w)
                    "D10043FF (sub sp, sp, #0x10)";
                bb_statements :=
                  [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 16w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 65540w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 65540w)
                    "F90007E0 (str x0, [sp, #8])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 3
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assert
                     (BExp_unchanged_mem_interval_distinct Bit64 0
                        4294967295
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 8w))) 8);
                   BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                     (BExp_Store
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 8w))) BEnd_LittleEndian
                        (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 65544w)))|>;
              <|bb_label := BL_Address_HC (Imm64 65544w) "D503201F (nop)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 65548w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 65548w)
                    "910043FF (add sp, sp, #0x10)";
                bb_statements :=
                  [BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 16w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 65552w)))|>;
              <|bb_label := BL_Address_HC (Imm64 65552w) "D65F03C0 (ret)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp
                      (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
		<|bb_label :=
                  BL_Address_HC (Imm64 66228w)
                    "A9BE7BFD (stp x29, x30, [sp, #-32]!)";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 3
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assert
                     (BExp_unchanged_mem_interval_distinct Bit64 0
                        4294967295
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 32w))) 16);
                   BStmt_Assign (BVar "tmp_SP_EL0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Minus
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 32w)));
                   BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                     (BExp_Store
                        (BExp_Store
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Minus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 32w))) BEnd_LittleEndian
                           (BExp_Den (BVar "R29" (BType_Imm Bit64))))
                        (BExp_BinExp BIExp_Minus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 24w))) BEnd_LittleEndian
                        (BExp_Den (BVar "R30" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                     (BExp_Den (BVar "tmp_SP_EL0" (BType_Imm Bit64)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66232w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66232w) "910003FD (mov x29, sp)";
                bb_statements :=
                  [BStmt_Assign (BVar "R29" (BType_Imm Bit64))
                     (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66236w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66236w)
                    "D2802000 (mov x0, #0x100                  // #256)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Const (Imm64 256w))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66240w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66240w)
                    "97FFFF50 (bl 10000 <malloc>)";
                bb_statements :=
                  [BStmt_Assign (BVar "R30" (BType_Imm Bit64))
                     (BExp_Const (Imm64 66244w))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 65536w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66244w) "AA0003E1 (mov x1, x0)";
                bb_statements :=
                  [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                     (BExp_Den (BVar "R0" (BType_Imm Bit64)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66248w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66248w)
                    "90000000 (adrp x0, 10000 <malloc>)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Const (Imm64 65536w))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66252w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66252w)
                    "911E4000 (add x0, x0, #0x790)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 1936w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66256w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66256w) "F9000001 (str x1, [x0])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 3
                        (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                   BStmt_Assert
                     (BExp_unchanged_mem_interval_distinct Bit64 0
                        4294967295 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        8);
                   BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                     (BExp_Store
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        BEnd_LittleEndian
                        (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66260w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66260w)
                    "B9001FFF (str wzr, [sp, #28])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assert
                     (BExp_unchanged_mem_interval_distinct Bit64 0
                        4294967295
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 28w))) 4);
                   BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                     (BExp_Store
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                        (BExp_Const (Imm32 0w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66264w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66264w)
                    "14000010 (b 10318 <build_decoding_table+0x64>)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66328w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66268w)
                    "90000000 (adrp x0, 10000 <malloc>)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Const (Imm64 65536w))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66272w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66272w)
                    "911E4000 (add x0, x0, #0x790)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 1936w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66276w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66276w) "F9400001 (ldr x1, [x0])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 3
                        (BExp_Den (BVar "R0" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                     (BExp_Load
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        BEnd_LittleEndian Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66280w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66280w)
                    "90000000 (adrp x0, 10000 <malloc>)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Const (Imm64 65536w))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66284w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66284w)
                    "911D0002 (add x2, x0, #0x740)";
                bb_statements :=
                  [BStmt_Assign (BVar "R2" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 1856w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66288w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66288w)
                    "B9801FE0 (ldrsw x0, [sp, #28])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Cast BIExp_SignedCast
                        (BExp_Load
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66292w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66292w)
                    "38606840 (ldrb w0, [x2, x0])";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                              (BExp_Den (BVar "R2" (BType_Imm Bit64))))
                           BEnd_LittleEndian Bit8) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66296w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66296w)
                    "92401C00 (and x0, x0, #0xff)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_And (BExp_Const (Imm64 255w))
                        (BExp_Den (BVar "R0" (BType_Imm Bit64))))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66300w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66300w) "8B000020 (add x0, x1, x0)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        (BExp_Den (BVar "R1" (BType_Imm Bit64))))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66304w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66304w)
                    "B9401FE1 (ldr w1, [sp, #28])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66308w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66308w)
                    "12001C21 (and w1, w1, #0xff)";
                bb_statements :=
                  [BStmt_Assign (BVar "R1" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_BinExp BIExp_And (BExp_Const (Imm32 255w))
                           (BExp_Cast BIExp_LowCast
                              (BExp_Den (BVar "R1" (BType_Imm Bit64)))
                              Bit32)) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66312w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66312w) "39000001 (strb w1, [x0])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_unchanged_mem_interval_distinct Bit64 0
                        4294967295 (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        1);
                   BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                     (BExp_Store
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                        BEnd_LittleEndian
                        (BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R1" (BType_Imm Bit64))) Bit8))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66316w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66316w)
                    "B9401FE0 (ldr w0, [sp, #28])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66320w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66320w)
                    "11000400 (add w0, w0, #0x1)";
                bb_statements :=
                  [BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_BinExp BIExp_Plus
                           (BExp_Cast BIExp_LowCast
                              (BExp_Den (BVar "R0" (BType_Imm Bit64)))
                              Bit32) (BExp_Const (Imm32 1w))) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66324w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66324w)
                    "B9001FE0 (str w0, [sp, #28])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assert
                     (BExp_unchanged_mem_interval_distinct Bit64 0
                        4294967295
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 28w))) 4);
                   BStmt_Assign (BVar "MEM" (BType_Mem Bit64 Bit8))
                     (BExp_Store
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                        (BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66328w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66328w)
                    "B9401FE0 (ldr w0, [sp, #28])";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 2
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R0" (BType_Imm Bit64))
                     (BExp_Cast BIExp_UnsignedCast
                        (BExp_Load
                           (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                           (BExp_BinExp BIExp_Plus
                              (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                              (BExp_Const (Imm64 28w))) BEnd_LittleEndian
                           Bit32) Bit64)];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66332w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66332w) "7100FC1F (cmp w0, #0x3f)";
                bb_statements :=
                  [BStmt_Assign (BVar "ProcState_C" BType_Bool)
                     (BExp_nzcv_SUB_C
                        (BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                        (BExp_Const (Imm32 63w)));
                   BStmt_Assign (BVar "ProcState_N" BType_Bool)
                     (BExp_nzcv_SUB_N Bit32
                        (BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                        (BExp_Const (Imm32 63w)));
                   BStmt_Assign (BVar "ProcState_V" BType_Bool)
                     (BExp_nzcv_SUB_V Bit32
                        (BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                        (BExp_Const (Imm32 63w)));
                   BStmt_Assign (BVar "ProcState_Z" BType_Bool)
                     (BExp_nzcv_SUB_Z
                        (BExp_Cast BIExp_LowCast
                           (BExp_Den (BVar "R0" (BType_Imm Bit64))) Bit32)
                        (BExp_Const (Imm32 63w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66336w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66336w)
                    "54FFFDED (b.le 102dc <build_decoding_table+0x28>)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_CJmp
                    (BExp_BinExp BIExp_And
                       (BExp_BinPred BIExp_Equal
                          (BExp_Den (BVar "ProcState_N" BType_Bool))
                          (BExp_Den (BVar "ProcState_V" BType_Bool)))
                       (BExp_UnaryExp BIExp_Not
                          (BExp_Den (BVar "ProcState_Z" BType_Bool))))
                    (BLE_Label (BL_Address (Imm64 66340w)))
                    (BLE_Label (BL_Address (Imm64 66268w)))|>;
              <|bb_label := BL_Address_HC (Imm64 66340w) "D503201F (nop)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66344w)))|>;
              <|bb_label := BL_Address_HC (Imm64 66344w) "D503201F (nop)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66348w)))|>;
              <|bb_label :=
                  BL_Address_HC (Imm64 66348w)
                    "A8C27BFD (ldp x29, x30, [sp], #32)";
                bb_statements :=
                  [BStmt_Assert
                     (BExp_Aligned Bit64 3
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64))));
                   BStmt_Assign (BVar "R29" (BType_Imm Bit64))
                     (BExp_Load
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        BEnd_LittleEndian Bit64);
                   BStmt_Assign (BVar "R30" (BType_Imm Bit64))
                     (BExp_Load
                        (BExp_Den (BVar "MEM" (BType_Mem Bit64 Bit8)))
                        (BExp_BinExp BIExp_Plus
                           (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                           (BExp_Const (Imm64 8w))) BEnd_LittleEndian Bit64);
                   BStmt_Assign (BVar "SP_EL0" (BType_Imm Bit64))
                     (BExp_BinExp BIExp_Plus
                        (BExp_Den (BVar "SP_EL0" (BType_Imm Bit64)))
                        (BExp_Const (Imm64 32w)))];
                bb_last_statement :=
                  BStmt_Jmp (BLE_Label (BL_Address (Imm64 66352w)))|>;
              <|bb_label := BL_Address_HC (Imm64 66352w) "D65F03C0 (ret)";
                bb_statements := [];
                bb_last_statement :=
                  BStmt_Jmp
                    (BLE_Exp (BExp_Den (BVar "R30" (BType_Imm Bit64))))|>;
    ]”;*)
(* build the dictionaries using the library under test *)
val _ = print "Building dictionaries.\n";
open bir_block_collectionLib;
val bl_dict = gen_block_dict lifted_prog;
val lbl_tms = get_block_dict_keys bl_dict;

(* build the cfg and update the basic blocks *)
val _ = print "Building node dict.\n";
open bir_cfgLib;
val n_dict = cfg_build_node_dict bl_dict lbl_tms;
 (* val entries = [``BL_Address (Imm64 66228w)``];   *) 
val entries = [mk_key_from_address64 64 (Arbnum.fromHexString "0")];
val _ = print "Building cfg.\n";
val g1 = cfg_create "toy" entries n_dict bl_dict;

;; (* display the cfg *)
;; val _ = print "Display cfg.\n";
;; open bir_cfg_vizLib;
;; val ns = List.map (valOf o (lookup_block_dict (#CFGG_node_dict g1))) (#CFGG_nodes g1);
;; val _ = cfg_display_graph_ns ns;


fun print_list lst =
    List.map (fn x => print_term x) lst;


(* val loop_pattern = "CFGNT_Jump"^"CFGNT_Basic"^"CFGNT_Basic"^"CFGNT_CondJump"; *)
val node_type =  ref ([]: (string * term) list);
val loop_pattern = ["CFGNT_Jump","CFGNT_Basic","CFGNT_Basic","CFGNT_CondJump"];

fun detect_loop (g:cfg_graph) entry visited =
  let
    val n = lookup_block_dict_value (#CFGG_node_dict g) entry "traverse_graph" "n";
    val targets = #CFGN_targets n;
    val n_type  = #CFGN_type n;
    val s_type = bir_cfgLib.toString n_type
    val _ = node_type:= !node_type@[(s_type, (#CFGN_lbl_tm n))];
    
    val targets_to_visit = List.filter (fn x => List.all (fn y => not (identical x y)) visited) targets;
    val result = List.foldr (fn (entry', visited') => detect_loop g entry' visited') (entry::visited) targets_to_visit;
  in result end;

val _ = node_type := [];
val _ =  detect_loop  g1 (hd (#CFGG_entries g1)) [];
!node_type;

fun get_range(trace, pattern) =
    let fun toChar t =
	  case t of "CFGNT_Jump"     => "J"
		  | "CFGNT_CondJump" => "C"
		  | "CFGNT_Halt"     => "H"
		  | "CFGNT_Basic"    => "B"
		  | "CFGNT_Call"     => "L"
		  | "CFGNT_Return"   => "R"

	fun index (str: string, substr: string) : int option =
	    let
		fun loop  (i: int) =
		    let val subt = ((String.size str) - (String.size substr))
		    in
			if (i > subt) then
			    NONE
			else if String.isSubstring (String.substring(str, i, (String.size substr))) substr then
			    SOME i
			else
			    loop (i + 1)
		    end
	    in
		loop 0
	    end
	val tc = List.foldr (fn (x, y) => x^y ) "" (map (fn x => toChar (fst x)) trace)
	val _ = print tc
	val _ = print "\n"
	val pc = List.foldr (fn (x, y) => x^y ) "" (map (fn x => toChar x) pattern)
	val _ = print pc
	val _ = print "\n"
    in
	index(tc, pc)
    end      
get_range(!node_type, loop_pattern);
