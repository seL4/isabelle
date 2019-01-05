(*  Title:      HOL/Word/Tools/word_lib.ML
    Author:     Sascha Boehme, TU Muenchen and Thomas Sewell, NICTA

Helper routines for operating on the word type.
*)

signature WORD_LIB =
sig
  val dest_binT: typ -> int
  val is_wordT: typ -> bool
  val dest_wordT: typ -> int
  val mk_wordT: int -> typ
end

structure Word_Lib: WORD_LIB =
struct

fun dest_binT T =
  (case T of
    Type (\<^type_name>\<open>Numeral_Type.num0\<close>, _) => 0
  | Type (\<^type_name>\<open>Numeral_Type.num1\<close>, _) => 1
  | Type (\<^type_name>\<open>Numeral_Type.bit0\<close>, [T]) => 2 * dest_binT T
  | Type (\<^type_name>\<open>Numeral_Type.bit1\<close>, [T]) => 1 + 2 * dest_binT T
  | _ => raise TYPE ("dest_binT", [T], []))

fun is_wordT (Type (\<^type_name>\<open>word\<close>, _)) = true
  | is_wordT _ = false

fun dest_wordT (Type (\<^type_name>\<open>word\<close>, [T])) = dest_binT T
  | dest_wordT T = raise TYPE ("dest_wordT", [T], [])


fun mk_bitT i T =
  if i = 0
  then Type (\<^type_name>\<open>Numeral_Type.bit0\<close>, [T])
  else Type (\<^type_name>\<open>Numeral_Type.bit1\<close>, [T])

fun mk_binT size = 
  if size = 0 then \<^typ>\<open>Numeral_Type.num0\<close>
  else if size = 1 then \<^typ>\<open>Numeral_Type.num1\<close>
  else let val (q, r) = Integer.div_mod size 2 in mk_bitT r (mk_binT q) end

fun mk_wordT size =
  if size >= 0 then Type (\<^type_name>\<open>word\<close>, [mk_binT size])
  else raise TYPE ("mk_wordT: " ^ string_of_int size, [], [])

end
