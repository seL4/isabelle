(*  Title:      Admin/Benchmarks/HOL-datatype/Instructions.thy
    ID:         $Id$
*)

theory Instructions = Main:

(* ------------------------------------------------------------------------- *)
(* Example from Konrad: 68000 instruction set.                               *)
(* ------------------------------------------------------------------------- *)

datatype Size = Byte | Word | Long

datatype DataRegister
              = RegD0
              | RegD1
              | RegD2
              | RegD3
              | RegD4
              | RegD5
              | RegD6
              | RegD7

datatype AddressRegister
              = RegA0
              | RegA1
              | RegA2
              | RegA3
              | RegA4
              | RegA5
              | RegA6
              | RegA7

datatype DataOrAddressRegister
              = data DataRegister
              | address AddressRegister

datatype Condition
              = Hi
              | Ls
              | Cc
              | Cs
              | Ne
              | Eq
              | Vc
              | Vs
              | Pl
              | Mi
              | Ge
              | Lt
              | Gt
              | Le

datatype AddressingMode
        = immediate nat
        | direct DataOrAddressRegister
        | indirect AddressRegister
        | postinc AddressRegister
        | predec AddressRegister
        | indirectdisp nat AddressRegister
        | indirectindex nat AddressRegister DataOrAddressRegister Size
        | absolute nat
        | pcdisp nat
        | pcindex nat DataOrAddressRegister Size

datatype M68kInstruction
    = ABCD AddressingMode AddressingMode
    | ADD Size AddressingMode AddressingMode
    | ADDA Size AddressingMode AddressRegister
    | ADDI Size nat AddressingMode
    | ADDQ Size nat AddressingMode
    | ADDX Size AddressingMode AddressingMode
    | AND Size AddressingMode AddressingMode
    | ANDI Size nat AddressingMode
    | ANDItoCCR nat
    | ANDItoSR nat
    | ASL Size AddressingMode DataRegister
    | ASLW AddressingMode
    | ASR Size AddressingMode DataRegister
    | ASRW AddressingMode
    | Bcc Condition Size nat
    | BTST Size AddressingMode AddressingMode
    | BCHG Size AddressingMode AddressingMode
    | BCLR Size AddressingMode AddressingMode
    | BSET Size AddressingMode AddressingMode
    | BRA Size nat
    | BSR Size nat
    | CHK AddressingMode DataRegister
    | CLR Size AddressingMode
    | CMP Size AddressingMode DataRegister
    | CMPA Size AddressingMode AddressRegister
    | CMPI Size nat AddressingMode
    | CMPM Size AddressRegister AddressRegister
    | DBT DataRegister nat
    | DBF DataRegister nat
    | DBcc Condition DataRegister nat
    | DIVS AddressingMode DataRegister
    | DIVU AddressingMode DataRegister
    | EOR Size DataRegister AddressingMode
    | EORI Size nat AddressingMode
    | EORItoCCR nat
    | EORItoSR nat
    | EXG DataOrAddressRegister DataOrAddressRegister
    | EXT Size DataRegister
    | ILLEGAL
    | JMP AddressingMode
    | JSR AddressingMode
    | LEA AddressingMode AddressRegister
    | LINK AddressRegister nat
    | LSL Size AddressingMode DataRegister
    | LSLW AddressingMode
    | LSR Size AddressingMode DataRegister
    | LSRW AddressingMode
    | MOVE Size AddressingMode AddressingMode
    | MOVEtoCCR AddressingMode
    | MOVEtoSR AddressingMode
    | MOVEfromSR AddressingMode
    | MOVEtoUSP AddressingMode
    | MOVEfromUSP AddressingMode
    | MOVEA Size AddressingMode AddressRegister
    | MOVEMto Size AddressingMode "DataOrAddressRegister list"
    | MOVEMfrom Size "DataOrAddressRegister list" AddressingMode
    | MOVEP Size AddressingMode AddressingMode
    | MOVEQ nat DataRegister
    | MULS AddressingMode DataRegister
    | MULU AddressingMode DataRegister
    | NBCD AddressingMode
    | NEG Size AddressingMode
    | NEGX Size AddressingMode
    | NOP
    | NOT Size AddressingMode
    | OR Size AddressingMode AddressingMode
    | ORI Size nat AddressingMode
    | ORItoCCR nat
    | ORItoSR nat
    | PEA AddressingMode
    | RESET
    | ROL Size AddressingMode DataRegister
    | ROLW AddressingMode
    | ROR Size AddressingMode DataRegister
    | RORW AddressingMode
    | ROXL Size AddressingMode DataRegister
    | ROXLW AddressingMode
    | ROXR Size AddressingMode DataRegister
    | ROXRW AddressingMode
    | RTE
    | RTR
    | RTS
    | SBCD AddressingMode AddressingMode
    | ST AddressingMode
    | SF AddressingMode
    | Scc Condition AddressingMode
    | STOP nat
    | SUB Size AddressingMode AddressingMode
    | SUBA Size AddressingMode AddressingMode
    | SUBI Size nat AddressingMode
    | SUBQ Size nat AddressingMode
    | SUBX Size AddressingMode AddressingMode
    | SWAP DataRegister
    | TAS AddressingMode
    | TRAP nat
    | TRAPV
    | TST Size AddressingMode
    | UNLK AddressRegister

end
