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

fun decode_char nibbles' tt =
  let
    fun idx c = find_index (curry (op =) c) nibbles';
    fun decode ~1 _ = NONE
      | decode _ ~1 = NONE
      | decode n m = SOME (chr (n * 16 + m));
  in case tt
   of (IConst { name = c1, ... }, IConst { name = c2, ... }) => decode (idx c1) (idx c2)
    | _ => NONE
  end;
   
fun implode_string char' nibbles' mk_char mk_string ts =
  let
    fun implode_char (IConst { name = c, ... } `$ t1 `$ t2) =
          if c = char' then decode_char nibbles' (t1, t2) else NONE
      | implode_char _ = NONE;
    val ts' = map_filter implode_char ts;
  in if length ts = length ts'
    then (SOME o Code_Printer.str o mk_string o implode) ts'
    else NONE
  end;

val cs_nibbles = [@{const_name Nibble0}, @{const_name Nibble1},
  @{const_name Nibble2}, @{const_name Nibble3},
  @{const_name Nibble4}, @{const_name Nibble5},
  @{const_name Nibble6}, @{const_name Nibble7},
  @{const_name Nibble8}, @{const_name Nibble9},
  @{const_name NibbleA}, @{const_name NibbleB},
  @{const_name NibbleC}, @{const_name NibbleD},
  @{const_name NibbleE}, @{const_name NibbleF}];
val cs_summa = [@{const_name Nil}, @{const_name Cons}, @{const_name Char}] @ cs_nibbles;

fun add_literal_list_string target =
  let
    fun pretty literals (nil' :: cons' :: char' :: nibbles') pr thm vars fxy [(t1, _), (t2, _)] =
      case Option.map (cons t1) (List_Code.implode_list nil' cons' t2)
       of SOME ts => (case implode_string char' nibbles'
          (Code_Printer.literal_char literals) (Code_Printer.literal_string literals) ts
             of SOME p => p
              | NONE =>
                  Code_Printer.literal_list literals (map (pr vars Code_Printer.NOBR) ts))
        | NONE =>
            List_Code.default_list (Code_Printer.infix_cons literals) (pr vars) fxy t1 t2;
  in Code_Target.add_const_syntax target
    @{const_name Cons} (SOME (Code_Printer.complex_const_syntax (2, (cs_summa, pretty))))
  end;

fun add_literal_char target =
  let
    fun pretty literals nibbles' _ thm _ _ [(t1, _), (t2, _)] =
      case decode_char nibbles' (t1, t2)
       of SOME c => (Code_Printer.str o Code_Printer.literal_char literals) c
        | NONE => Code_Printer.eqn_error thm "Illegal character expression";
  in Code_Target.add_const_syntax target
    @{const_name Char} (SOME (Code_Printer.complex_const_syntax (2, (cs_nibbles, pretty))))
  end;

fun add_literal_string target =
  let
    fun pretty literals (nil' :: cons' :: char' :: nibbles') _ thm _ _ [(t, _)] =
      case List_Code.implode_list nil' cons' t
       of SOME ts => (case implode_string char' nibbles'
          (Code_Printer.literal_char literals) (Code_Printer.literal_string literals) ts
             of SOME p => p
              | NONE => Code_Printer.eqn_error thm "Illegal message expression")
        | NONE => Code_Printer.eqn_error thm "Illegal message expression";
  in Code_Target.add_const_syntax target 
    @{const_name STR} (SOME (Code_Printer.complex_const_syntax (1, (cs_summa, pretty))))
  end;

end;
