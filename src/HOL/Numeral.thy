(*  Title:      HOL/Numeral.thy
    ID:         $Id$
    Author:     Larry Paulson and Markus Wenzel

Generic numerals represented as twos-complement bit strings, and
selector function as ones-complement unit strings.
*)

theory Numeral = Datatype
files "Tools/numeral_syntax.ML":


(* numerals *)

datatype
  bin = Pls
      | Min
      | Bit bin bool    (infixl "BIT" 90)

axclass
  number < "term"      (*for numeric types: nat, int, real, ...*)

consts
  number_of :: "bin => 'a::number"

syntax
  "_Numeral" :: "xnum => 'a"    ("_")

setup NumeralSyntax.setup


(* selector functions *)

(*Note that type constraints on selector functons are not handled
  properly here*)

syntax
  "_selector" :: 'a
  "_op_selector" :: "xnum => 'a"            ("op _" [0] 1000)

translations
  "(_Numeral i) x" => "_selector i x"

parse_translation {*
  let
    val fstC = Syntax.const "fst";
    val sndC = Syntax.const "snd";
    fun ap_snd t = sndC $ t;
    fun comp_snd t = Syntax.const "op o" $ t $ sndC;

    fun selector_tr [Free (x, _), t] =
          let val i = Syntax.read_xnum x in
            if i = 0 orelse i = ~1 then t
            else if i > 0 then fstC $ funpow (i - 1) ap_snd t
            else funpow (~i - 1) ap_snd t
          end
      | selector_tr ts = raise TERM ("selector_tr", ts);

    fun op_selector_tr [Free (x, _)] =
          let val i = Syntax.read_xnum x in
            if i = 0 orelse i = ~1 then Abs ("x", dummyT, Bound 0)
            else if i > 0 then funpow (i - 1) comp_snd fstC
            else funpow (~i - 2) comp_snd sndC
          end
      | op_selector_tr ts = raise TERM ("op_selector_tr", ts);
  in [("_selector", selector_tr), ("_op_selector", op_selector_tr)] end
*}

print_translation {*
  let
    fun mk_xnum i =
      Syntax.free ("#" ^ (if i < 0 then "-" else "") ^ (string_of_int (abs i)));


    fun snds_tr' (i, Const ("snd", _) $ t) = snds_tr' (i + 1, t)
      | snds_tr' x = x;

    fun fst_tr' t = let val (i, t') = snds_tr' (0, t) in (i + 1, t') end;
    fun snd_tr' t = let val (i, t') = snds_tr' (0, t) in (~ (i + 2), t') end;

    fun selector_tr' f (t :: ts) =
          let val (i, u) = f t in
            if ~2 <= i andalso i <= 1 then raise Match
            else Term.list_comb (mk_xnum i $ u, ts) end
      | selector_tr' _ [] = raise Match;


    fun o_snd_tr' i (Const ("op o", _) $ t $ Const ("snd", _)) = o_snd_tr' (i + 1) t
      | o_snd_tr' i (Const ("fst", _)) = i + 1
      | o_snd_tr' i (Const ("snd", _)) = ~ (i + 2)
      | o_snd_tr' _ _ = raise Match;

    fun comp_tr' (t :: u :: ts) =
          Term.list_comb (Syntax.const "_op_selector" $
            mk_xnum (o_snd_tr' 0 (Syntax.const "op o" $ t $ u)), ts)
      | comp_tr' _ = raise Match;
  in [("fst", selector_tr' fst_tr'), ("snd", selector_tr' snd_tr'), ("op o", comp_tr')] end
*}

end
