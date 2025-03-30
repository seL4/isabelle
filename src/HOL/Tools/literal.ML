(*  Title:      HOL/Tools/literal.ML
    Author:     Florian Haftmann, TU Muenchen

Logical and syntactic operations on literals (see also HOL/Tools/hologic.ML).
*)

signature LITERAL =
sig
  val add_code: string -> theory -> theory
end

structure Literal: LITERAL =
struct

datatype character = datatype String_Syntax.character;

fun mk_literal_syntax [] = Syntax.const \<^const_syntax>\<open>String.empty_literal\<close>
  | mk_literal_syntax (c :: cs) =
      list_comb (Syntax.const \<^const_syntax>\<open>String.Literal\<close>, String_Syntax.mk_bits_syntax 7 c)
        $ mk_literal_syntax cs;

val dest_literal_syntax =
  let
    fun dest (Const (\<^const_syntax>\<open>String.empty_literal\<close>, _)) = []
      | dest (Const (\<^const_syntax>\<open>String.Literal\<close>, _) $ b0 $ b1 $ b2 $ b3 $ b4 $ b5 $ b6 $ t) =
          String_Syntax.classify_character (String_Syntax.dest_bits_syntax [b0, b1, b2, b3, b4, b5, b6]) :: dest t
      | dest t = raise Match;
  in dest end;

fun ascii_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
      c $ ascii_tr [t] $ u
  | ascii_tr [Const (num, _)] =
      (mk_literal_syntax o single o (fn n => n mod 128) o #value o Lexicon.read_num) num
  | ascii_tr ts = raise TERM ("ascii_tr", ts);

fun literal_tr [(c as Const (\<^syntax_const>\<open>_constrain\<close>, _)) $ t $ u] =
      c $ literal_tr [t] $ u
  | literal_tr [Free (str, _)] =
      (mk_literal_syntax o map String_Syntax.ascii_ord_of o String_Syntax.plain_strings_of) str
  | literal_tr ts = raise TERM ("literal_tr", ts);

fun ascii k = Syntax.const \<^syntax_const>\<open>_Ascii\<close>
  $ Syntax.free (String_Syntax.hex k);

fun literal cs = Syntax.const \<^syntax_const>\<open>_Literal\<close>
  $ Syntax.const (Lexicon.implode_str cs);

fun empty_literal_tr' _ = literal [];

fun literal_tr' [b0, b1, b2, b3, b4, b5, b6, t] =
      let
        val cs =
          dest_literal_syntax (list_comb (Syntax.const \<^const_syntax>\<open>String.Literal\<close>, [b0, b1, b2, b3, b4, b5, b6, t]))
        fun is_printable (Char _) = true
          | is_printable (Ord _) = false;
        fun the_char (Char c) = c;
        fun the_ascii [Ord i] = i;
      in
        if forall is_printable cs
        then literal (map the_char cs)
        else if length cs = 1
        then ascii (the_ascii cs)
        else raise Match
      end
  | literal_tr' _ = raise Match;

open Basic_Code_Thingol;

fun map_partial g f =
  let
    fun mapp [] = SOME []
      | mapp (x :: xs) =
          (case f x of
            NONE => NONE
          | SOME y => 
            (case mapp xs of
              NONE => NONE
            | SOME ys => SOME (y :: ys)))
  in Option.map g o mapp end;

fun implode_bit (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>False\<close>, ... }) = SOME 0
  | implode_bit (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>True\<close>, ... }) = SOME 1
  | implode_bit _ = NONE

fun implode_ascii (b0, b1, b2, b3, b4, b5, b6) =
  map_partial (chr o Integer.eval_radix 2) implode_bit [b0, b1, b2, b3, b4, b5, b6];

fun implode_literal b0 b1 b2 b3 b4 b5 b6 t =
  let
    fun dest_literal (IConst { sym = Code_Symbol.Constant \<^const_name>\<open>String.Literal\<close>, ... }
          `$ b0 `$ b1 `$ b2 `$ b3 `$ b4 `$ b5 `$ b6 `$ t) = SOME ((b0, b1, b2, b3, b4, b5, b6), t)
      | dest_literal _ = NONE;
    val (bss', t') = Code_Thingol.unfoldr dest_literal t;
    val bss = (b0, b1, b2, b3, b4, b5, b6) :: bss';
  in
    case t' of
      IConst { sym = Code_Symbol.Constant \<^const_name>\<open>String.zero_literal_inst.zero_literal\<close>, ... }
        => map_partial implode implode_ascii bss
    | _ => NONE
  end;

fun add_code target thy =
  let
    fun pretty literals _ thm _ _ [(b0, _), (b1, _), (b2, _), (b3, _), (b4, _), (b5, _), (b6, _), (t, _)] =
      case implode_literal b0 b1 b2 b3 b4 b5 b6 t of
        SOME s => (Pretty.str o Code_Printer.literal_string literals) s
      | NONE => Code_Printer.eqn_error thy thm "Illegal string literal expression";
  in
    thy
    |> Code_Target.set_printings (Code_Symbol.Constant (\<^const_name>\<open>String.Literal\<close>,
      [(target, SOME (Code_Printer.complex_const_syntax (8, pretty)))]))
  end;

val _ =
  Theory.setup
   (Sign.parse_translation
     [(\<^syntax_const>\<open>_Ascii\<close>, K ascii_tr),
      (\<^syntax_const>\<open>_Literal\<close>, K literal_tr)] #>
    Sign.print_translation
     [(\<^const_syntax>\<open>String.Literal\<close>, K literal_tr'),
      (\<^const_syntax>\<open>String.empty_literal\<close>, K empty_literal_tr')]);

end
