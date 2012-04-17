(*  Title:      HOL/Word/Tools/word_lib.ML
    Author:     Sascha Boehme, TU Muenchen and Thomas Sewell, NICTA

Helper routines for operating on the word type at the ML level.
*)


structure Word_Lib = struct

fun dest_binT T =
  (case T of
    Type (@{type_name "Numeral_Type.num0"}, _) => 0
  | Type (@{type_name "Numeral_Type.num1"}, _) => 1
  | Type (@{type_name "Numeral_Type.bit0"}, [T]) => 2 * dest_binT T
  | Type (@{type_name "Numeral_Type.bit1"}, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

fun is_wordT (Type (@{type_name word}, _)) = true
  | is_wordT _ = false

fun dest_wordT (Type (@{type_name word}, [T])) = dest_binT T
  | dest_wordT T = raise TYPE ("dest_wordT", [T], [])

local
  fun mk_bitT i T =
    if i = 0
    then Type (@{type_name "Numeral_Type.bit0"}, [T])
    else Type (@{type_name "Numeral_Type.bit1"}, [T])

  fun mk_binT size = 
    if size = 0 then @{typ "Numeral_Type.num0"}
    else if size = 1 then @{typ "Numeral_Type.num1"}
    else let val (q, r) = Integer.div_mod size 2 in mk_bitT r (mk_binT q) end
in
fun mk_wordT size =
  if size >= 0 then Type (@{type_name "word"}, [mk_binT size])
  else raise TYPE ("mk_wordT: " ^ quote (string_of_int size), [], [])
end

end
