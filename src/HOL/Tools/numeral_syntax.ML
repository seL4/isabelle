(*  Title:      HOL/Tools/numeral_syntax.ML
    Authors:    Markus Wenzel, TU Muenchen

Concrete syntax for generic numerals -- preserves leading zeros/ones.
*)

signature NUMERAL_SYNTAX =
sig
  val setup: theory -> theory
end;

structure Numeral_Syntax: NUMERAL_SYNTAX =
struct

(* parse translation *)

local

fun mk_bin num =
  let
    fun bit b bs = HOLogic.mk_bit b $ bs;
    fun mk 0 = Syntax.const @{const_name Int.Pls}
      | mk ~1 = Syntax.const @{const_name Int.Min}
      | mk i = let val (q, r) = Integer.div_mod i 2 in bit r (mk q) end;
  in mk (#value (Lexicon.read_xnum num)) end;

in

fun numeral_tr [(c as Const (@{syntax_const "_constrain"}, _)) $ t $ u] = c $ numeral_tr [t] $ u
  | numeral_tr [t as Const (num, _)] = Syntax.const @{const_syntax Int.number_of} $ mk_bin num
  | numeral_tr ts = raise TERM ("numeral_tr", ts);

end;


(* print translation *)

local

fun dest_bin (Const (@{const_syntax Int.Pls}, _)) = []
  | dest_bin (Const (@{const_syntax Int.Min}, _)) = [~1]
  | dest_bin (Const (@{const_syntax Int.Bit0}, _) $ bs) = 0 :: dest_bin bs
  | dest_bin (Const (@{const_syntax Int.Bit1}, _) $ bs) = 1 :: dest_bin bs
  | dest_bin _ = raise Match;

fun leading _ [] = 0
  | leading (i: int) (j :: js) = if i = j then 1 + leading i js else 0;

fun int_of [] = 0
  | int_of (b :: bs) = b + 2 * int_of bs;

fun dest_bin_str tm =
  let
    val rev_digs = dest_bin tm;
    val (sign, z) =
      (case rev rev_digs of
        ~1 :: bs => ("-", leading 1 bs)
      | bs => ("", leading 0 bs));
    val i = int_of rev_digs;
    val num = string_of_int (abs i);
  in
    if (i = 0 orelse i = 1) andalso z = 0 then raise Match
    else sign ^ implode (replicate z "0") ^ num
  end;

fun syntax_numeral t =
  Syntax.const @{syntax_const "_Numeral"} $
    (Syntax.const @{syntax_const "_numeral"} $ Syntax.free (dest_bin_str t));

in

fun numeral_tr' ctxt (Type (@{type_name fun}, [_, T])) (t :: ts) =
      let val t' =
        if not (Config.get ctxt show_types) andalso can Term.dest_Type T then syntax_numeral t
        else
          Syntax.const @{syntax_const "_constrain"} $ syntax_numeral t $
            Syntax_Phases.term_of_typ ctxt T
      in list_comb (t', ts) end
  | numeral_tr' _ T (t :: ts) =
      if T = dummyT then list_comb (syntax_numeral t, ts)
      else raise Match
  | numeral_tr' _ _ _ = raise Match;

end;


(* theory setup *)

val setup =
  Sign.add_trfuns ([], [(@{syntax_const "_Numeral"}, numeral_tr)], [], []) #>
  Sign.add_advanced_trfunsT [(@{const_syntax Int.number_of}, numeral_tr')];

end;
