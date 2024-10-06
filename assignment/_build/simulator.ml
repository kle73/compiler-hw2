(* X86lite Simulator *)

(* See the documentation in the X86lite specification, available on the 
   course web pages, for a detailed explanation of the instruction
   semantics.
*)

open X86

(* simulator machine state -------------------------------------------------- *)

let mem_bot = 0x400000L          (* lowest valid address *)
let mem_top = 0x410000L          (* one past the last byte in memory *)
let mem_size = Int64.to_int (Int64.sub mem_top mem_bot)
let nregs = 17                   (* including Rip *)
let ins_size = 8L                (* assume we have a 8-byte encoding *)
let exit_addr = 0xfdeadL         (* halt when m.regs(%rip) = exit_addr *)

(* Your simulator should raise this exception if it tries to read from or
   store to an address not within the valid address space. *)
exception X86lite_segfault

(* The simulator memory maps addresses to symbolic bytes.  Symbolic
   bytes are either actual data indicated by the Byte constructor or
   'symbolic instructions' that take up eight bytes for the purposes of
   layout.

   The symbolic bytes abstract away from the details of how
   instructions are represented in memory.  Each instruction takes
   exactly eight consecutive bytes, where the first byte InsB0 stores
   the actual instruction, and the next seven bytes are InsFrag
   elements, which aren't valid data.

   For example, the two-instruction sequence:
        at&t syntax             ocaml syntax
      movq %rdi, (%rsp)       Movq,  [~%Rdi; Ind2 Rsp]
      decq %rdi               Decq,  [~%Rdi]

   is represented by the following elements of the mem array (starting
   at address 0x400000):

       0x400000 :  InsB0 (Movq,  [~%Rdi; Ind2 Rsp])
       0x400001 :  InsFrag
       0x400002 :  InsFrag
       0x400003 :  InsFrag
       0x400004 :  InsFrag
       0x400005 :  InsFrag
       0x400006 :  InsFrag
       0x400007 :  InsFrag
       0x400008 :  InsB0 (Decq,  [~%Rdi])
       0x40000A :  InsFrag
       0x40000B :  InsFrag
       0x40000C :  InsFrag
       0x40000D :  InsFrag
       0x40000E :  InsFrag
       0x40000F :  InsFrag
       0x400010 :  InsFrag
*)
type sbyte = InsB0 of ins       (* 1st byte of an instruction *)
           | InsFrag            (* 2nd - 8th bytes of an instruction *)
           | Byte of char       (* non-instruction byte *)

(* memory maps addresses to symbolic bytes *)
type mem = sbyte array

(* Flags for condition codes *)
type flags = { mutable fo : bool
             ; mutable fs : bool
             ; mutable fz : bool
             }

(* Register files *)
type regs = int64 array

(* Complete machine state *)
type mach = { flags : flags
            ; regs : regs
            ; mem : mem
            }

(* simulator helper functions ----------------------------------------------- *)

(* The index of a register in the regs array *)
let rind : reg -> int = function
  | Rip -> 16
  | Rax -> 0  | Rbx -> 1  | Rcx -> 2  | Rdx -> 3
  | Rsi -> 4  | Rdi -> 5  | Rbp -> 6  | Rsp -> 7
  | R08 -> 8  | R09 -> 9  | R10 -> 10 | R11 -> 11
  | R12 -> 12 | R13 -> 13 | R14 -> 14 | R15 -> 15

(* Helper functions for reading/writing sbytes *)

(* Convert an int64 to its sbyte representation *)
let sbytes_of_int64 (i:int64) : sbyte list =
  let open Char in 
  let open Int64 in
  List.map (fun n -> Byte (shift_right i n |> logand 0xffL |> to_int |> chr))
           [0; 8; 16; 24; 32; 40; 48; 56]

(* Convert an sbyte representation to an int64 *)
let int64_of_sbytes (bs:sbyte list) : int64 =
  let open Char in
  let open Int64 in
  let f b i = match b with
    | Byte c -> logor (shift_left i 8) (c |> code |> of_int)
    | _ -> 0L
  in
  List.fold_right f bs 0L

(* Convert a string to its sbyte representation *)
let sbytes_of_string (s:string) : sbyte list =
  let rec loop acc = function
    | i when i < 0 -> acc
    | i -> loop (Byte s.[i]::acc) (pred i)
  in
  loop [Byte '\x00'] @@ String.length s - 1

(* Serialize an instruction to sbytes *)
let sbytes_of_ins (op, args:ins) : sbyte list =
  let check = function
    | Imm (Lbl _) | Ind1 (Lbl _) | Ind3 (Lbl _, _) -> 
      invalid_arg "sbytes_of_ins: tried to serialize a label!"
    | o -> ()
  in
  List.iter check args;
  [InsB0 (op, args); InsFrag; InsFrag; InsFrag;
   InsFrag; InsFrag; InsFrag; InsFrag]

(* Serialize a data element to sbytes *)
let sbytes_of_data : data -> sbyte list = function
  | Quad (Lit i) -> sbytes_of_int64 i
  | Asciz s -> sbytes_of_string s
  | Quad (Lbl _) -> invalid_arg "sbytes_of_data: tried to serialize a label!"


(* It might be useful to toggle printing of intermediate states of your 
   simulator. Our implementation uses this mutable flag to turn on/off
   printing.  For instance, you might write something like:

     [if !debug_simulator then print_endline @@ string_of_ins u; ...]

*)
let debug_simulator = ref true

(* Interpret a condition code with respect to the given flags. *)
let interp_cnd {fo; fs; fz} : cnd -> bool = fun x -> 
  begin match x with
    | Eq -> fz
    | Neq -> not fz
    | Lt -> fs <> fo
    | Le -> fz || (fs <> fo)
    | Gt -> not (fz || (fs <> fo))
    | Ge -> fs = fo
  end

(* Maps an X86lite address into Some OCaml array index,
   or None if the address is not within the legal address space. *)
let map_addr (addr:quad) : int option =
  if (addr < mem_bot) || (addr >= mem_top) then None
  else Some (Int64.to_int (Int64.sub addr 0x400000L))

(*reads and writes OCaml int64 type integer into sbyte array *)

(* interpretation of operands *)
let interp_imm (i:imm) : int64 = 
  begin match i with
   | Lit n -> n
   | Lbl lbl -> 0L (* we can assume labels have been resolved by assembler *)
  end



let write_to_mem (mem:mem) (i:int) (n:int64) : unit = 
  let byte_list = (sbytes_of_int64 n) in
    for k = 0 to 7 do
      mem.(i+k) <- List.nth byte_list k
    done

let rec read_aux (k:int) (m:mem) (i:int) : sbyte list =
    if k > 7 then [] else m.(i+k)::(read_aux (k+1) m i) 
  
let read_from_mem (mem:mem) (i:int) : int64 = 
    int64_of_sbytes (read_aux 0 mem i)


let interp_src_operand (opd:operand) (regs:regs) (mem:mem) : int64 = 
  begin match opd with
    | Imm i -> interp_imm i
    | Reg r -> regs.(rind r)
    | Ind1 i -> interp_imm i
    | Ind2 r -> read_from_mem mem (Option.get (map_addr regs.(rind r)))
    | Ind3 (i, r) -> read_from_mem mem ((Int64.to_int (interp_imm i)) + (Option.get (map_addr regs.(rind r))))
  end

let set_dest (opd:operand) (regs:regs) (mem:mem) (src:int64) : unit = 
  begin match opd with
    | Imm i -> () (* invalid destination *)
    | Ind1 i -> () (* invalid destination *)
    | Reg r -> regs.(rind r) <- src 
    | Ind2 r -> write_to_mem mem (Option.get (map_addr regs.(rind r))) src
    | Ind3 (i, r) -> write_to_mem mem ((Int64.to_int (interp_imm i)) + (Option.get (map_addr regs.(rind r)))) src
  end

(* sign helper *)
let sign64 (n:int64) : bool = if n < Int64.zero then false else true

(* HELPERS for step *)

(* 
   These functions take the list of operands and the mach
   as an input and perform the operation they are designed for
   operate on mach in place
*)

(* ARITHMETIC INSTRUCTIONS *)

(* Negq *)
let interp_negq (opl:operand list) (m:mach) : unit = 
  let src = interp_src_operand (List.hd opl) m.regs m.mem in
    let set_fo = if src = Int64.min_int then m.flags.fo <- true else m.flags.fo <- false in
    set_fo;
    set_dest (List.hd opl) m.regs m.mem (Int64.neg src)



(* Addq *)
let interp_addq (opl:operand list) (m:mach) : unit = 
  print_endline @@ string_of_operand (List.hd opl);
  print_endline @@ string_of_operand (List.nth opl 1);
  let s64 = interp_src_operand (List.hd opl) m.regs m.mem in
    let d64 = interp_src_operand (List.nth opl 1) m.regs m.mem in
      let r64 = (Int64.add s64 d64) in
      let set_fo = if ((sign64 s64) = (sign64 d64)) && ((sign64 r64) <> (sign64 s64)) 
                   then m.flags.fo <- true 
                   else m.flags.fo <- false in
        set_fo;
        set_dest (List.nth opl 1) m.regs m.mem r64
        
(* Subq *)
let interp_subq (opl:operand list) (m:mach) : unit = 
  let s64 = interp_src_operand (List.hd opl) m.regs m.mem in
    let d64 = interp_src_operand (List.nth opl 1) m.regs m.mem in
      let r64 = (Int64.sub d64 s64) in
      let set_fo = if ((sign64 (Int64.neg s64)) = (sign64 d64)) && 
                      ((sign64 r64) <> (sign64 (Int64.neg s64))) || 
                      s64 = Int64.min_int 
                   then m.flags.fo <- true 
                   else m.flags.fo <- false in
        set_fo;
        set_dest (List.nth opl 1) m.regs m.mem r64

        
(* Imulq *)
let interp_imulq (opl:operand list) (m:mach) : unit = 
  let s64 = interp_src_operand (List.hd opl) m.regs m.mem in
    let d64 = interp_src_operand (List.nth opl 1) m.regs m.mem in
      let r64 = (Int64.mul d64 s64) in
        (* TODO: set of flag *)
        set_dest (List.nth opl 1) m.regs m.mem r64
        

(* Incq *)
let interp_incq (opl:operand list) (m:mach) : unit = 
  let s64 = interp_src_operand (List.hd opl) m.regs m.mem in
    let r64 = (Int64.add s64 Int64.one) in
      let set_fo = if ((sign64 s64) = true) && ((sign64 r64) <> (sign64 s64)) 
                   then m.flags.fo <- true 
                   else m.flags.fo <- false in
        set_fo;
        set_dest (List.nth opl 1) m.regs m.mem r64

(* Decq *)
let interp_decq (opl:operand list) (m:mach) : unit = 
  let s64 = interp_src_operand (List.hd opl) m.regs m.mem in
      let r64 = (Int64.sub s64 Int64.minus_one) in
      let set_fo = if ((sign64 (Int64.neg s64)) = false) && 
                      ((sign64 r64) <> (sign64 (Int64.neg s64))) || 
                      s64 = Int64.min_int 
                   then m.flags.fo <- true 
                   else m.flags.fo <- false in
        set_fo;
        set_dest (List.nth opl 1) m.regs m.mem r64

(* DATA MOVEMENT *)      

(* Leaq *)

(* Movq *)
let interp_movq (opl:operand list) (m:mach) : unit = 
  let src = interp_src_operand (List.hd opl) m.regs m.mem in
    print_endline @@ string_of_operand (List.hd opl);
    set_dest (List.nth opl 1) m.regs m.mem src

    

(* Simulates one step of the machine:
    - fetch the instruction at %rip
    - compute the source and/or destination information from the operands
    - simulate the instruction semantics
    - update the registers and/or memory appropriately
    - set the condition flags
*)
let step (m:mach) : unit =
  let sb = m.mem.(Option.get (map_addr (m.regs.(rind Rip)))) in 
    begin match sb with
    | InsB0 (opc, opl) -> (* case that at mem(rip) is actually an instruction *)
        begin match opc with
         | Negq -> interp_negq opl m
         | Addq -> interp_addq opl m
         | Imulq -> interp_imulq opl m
         | Subq -> interp_subq opl m
         | Incq -> interp_incq opl m
         | Decq -> interp_decq opl m
         | Movq -> interp_movq opl m
        end
    | InsFrag -> ()
    | Byte c -> ()
  end

(* Runs the machine until the rip register reaches a designated
   memory address. Returns the contents of %rax when the 
   machine halts. *)
let run (m:mach) : int64 = 
  while m.regs.(rind Rip) <> exit_addr do step m done;
  m.regs.(rind Rax)

(* assembling and linking --------------------------------------------------- *)

(* A representation of the executable *)
type exec = { entry    : quad              (* address of the entry point *)
            ; text_pos : quad              (* starting address of the code *)
            ; data_pos : quad              (* starting address of the data *)
            ; text_seg : sbyte list        (* contents of the text segment *)
            ; data_seg : sbyte list        (* contents of the data segment *)
            }

(* Assemble should raise this when a label is used but not defined *)
exception Undefined_sym of lbl

(* Assemble should raise this when a label is defined more than once *)
exception Redefined_sym of lbl

(* Convert an X86 program into an object file:
   - separate the text and data segments
   - compute the size of each segment
      Note: the size of an Asciz string section is (1 + the string length)
            due to the null terminator

   - resolve the labels to concrete addresses and 'patch' the instructions to 
     replace Lbl values with the corresponding Imm values.

   - the text segment starts at the lowest address
   - the data segment starts after the text segment

  HINT: List.fold_left and List.fold_right are your friends.
 *)
let assemble (p:prog) : exec =
failwith "assemble unimplemented"

(* Convert an object file into an executable machine state. 
    - allocate the mem array
    - set up the memory state by writing the symbolic bytes to the 
      appropriate locations 
    - create the inital register state
      - initialize rip to the entry point address
      - initializes rsp to the last word in memory 
      - the other registers are initialized to 0
    - the condition code flags start as 'false'

  Hint: The Array.make, Array.blit, and Array.of_list library functions 
  may be of use.
*)
let load {entry; text_pos; data_pos; text_seg; data_seg} : mach = 
failwith "load unimplemented"
