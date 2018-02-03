(*  Title:      HOL/Tools/string_code.ML
    Author:     Florian Haftmann, TU Muenchen

Code generation for character and string literals.
*)

signature STRING_CODE =
sig
  val add_literal_list_string: string -> theory -> theory
  val add_literal_char: string -> theory -> theory
  val add_literal_string: string -> theory -> theory
end;

structure String_Code : STRING_CODE =
struct

open Basic_Code_Thingol;

fun decode_char_nonzero t =
  case Numeral.dest_num t of
    SOME n => if 0 < n andalso n < 256 then SOME n else NONE
  | _ => NONE;

fun decode_char (IConst { sym = Code_Symbol.Constant @{const_name String.zero_char_inst.zero_char}, ... }) =
     SOME 0
  | decode_char (IConst { sym = Code_Symbol.Constant @{const_name Char}, ... } `$ t) =
      decode_char_nonzero t
  | decode_char _ = NONE

fun implode_string literals ts =
  let
    val is = map_filter decode_char ts;
  in if length ts = length is
    then (SOME o Code_Printer.str o Code_Printer.literal_string literals o implode o map chr) is
    else NONE
  end;

fun add_literal_list_string target =
  let
    fun pretty literals pr _ vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (List_Code.implode_list t2)
       of SOME ts => (case implode_string literals ts
             of SOME p => p
              | NONE =>
                  Code_Printer.literal_list literals (map (pr vars Code_Printer.NOBR) ts))
        | NONE =>
            List_Code.default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in
    Code_Target.set_printings (Code_Symbol.Constant (@{const_name Cons},
      [(target, SOME (Code_Printer.complex_const_syntax (2, pretty)))]))
  end;

fun add_literal_char target thy =
  let
    fun pr literals =
      Code_Printer.str o Code_Printer.literal_char literals o chr;
    fun pretty_zero literals _ _ _ _ [] =
      pr literals 0
    fun pretty_Char literals _ thm _ _ [(t, _)] =
      case decode_char_nonzero t
       of SOME i => pr literals i
        | NONE => Code_Printer.eqn_error thy thm "Illegal character expression";
  in
    thy
    |> Code_Target.set_printings (Code_Symbol.Constant (@{const_name String.zero_char_inst.zero_char},
      [(target, SOME (Code_Printer.complex_const_syntax (0, pretty_zero)))]))
    |> Code_Target.set_printings (Code_Symbol.Constant (@{const_name Char},
      [(target, SOME (Code_Printer.complex_const_syntax (1, pretty_Char)))]))
  end;

fun add_literal_string target thy =
  let
    fun pretty literals _ thm _ _ [(t, _)] =
      case List_Code.implode_list t
       of SOME ts => (case implode_string literals ts
             of SOME p => p
              | NONE => Code_Printer.eqn_error thy thm "Illegal string literal expression")
        | NONE => Code_Printer.eqn_error thy thm "Illegal string literal expression";
  in
    thy
    |> Code_Target.set_printings (Code_Symbol.Constant (@{const_name STR},
      [(target, SOME (Code_Printer.complex_const_syntax (1, pretty)))]))
  end;

end;
