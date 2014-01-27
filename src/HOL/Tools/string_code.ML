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

val cs_nibbles = [@{const_name Nibble0}, @{const_name Nibble1},
  @{const_name Nibble2}, @{const_name Nibble3},
  @{const_name Nibble4}, @{const_name Nibble5},
  @{const_name Nibble6}, @{const_name Nibble7},
  @{const_name Nibble8}, @{const_name Nibble9},
  @{const_name NibbleA}, @{const_name NibbleB},
  @{const_name NibbleC}, @{const_name NibbleD},
  @{const_name NibbleE}, @{const_name NibbleF}];

fun decode_char tt =
  let
    fun idx c = find_index (curry (op =) c) cs_nibbles;
    fun decode ~1 _ = NONE
      | decode _ ~1 = NONE
      | decode n m = SOME (chr (n * 16 + m));
  in case tt
   of (IConst { sym = Code_Symbol.Constant c1, ... }, IConst { sym = Code_Symbol.Constant c2, ... }) => decode (idx c1) (idx c2)
    | _ => NONE
  end;
   
fun implode_string literals ts =
  let
    fun implode_char (IConst { sym = Code_Symbol.Constant @{const_name Char}, ... } `$ t1 `$ t2) =
          decode_char (t1, t2)
      | implode_char _ = NONE;
    val ts' = map_filter implode_char ts;
  in if length ts = length ts'
    then (SOME o Code_Printer.str o Code_Printer.literal_string literals o implode) ts'
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

fun add_literal_char target =
  let
    fun pretty literals _ thm _ _ [(t1, _), (t2, _)] =
      case decode_char (t1, t2)
       of SOME c => (Code_Printer.str o Code_Printer.literal_char literals) c
        | NONE => Code_Printer.eqn_error thm "Illegal character expression";
  in
    Code_Target.set_printings (Code_Symbol.Constant (@{const_name Char},
      [(target, SOME (Code_Printer.complex_const_syntax (2, pretty)))]))
  end;

fun add_literal_string target =
  let
    fun pretty literals _ thm _ _ [(t, _)] =
      case List_Code.implode_list t
       of SOME ts => (case implode_string literals ts
             of SOME p => p
              | NONE => Code_Printer.eqn_error thm "Illegal string literal expression")
        | NONE => Code_Printer.eqn_error thm "Illegal string literal expression";
  in
    Code_Target.set_printings (Code_Symbol.Constant (@{const_name STR},
      [(target, SOME (Code_Printer.complex_const_syntax (1, pretty)))]))
  end;

end;
