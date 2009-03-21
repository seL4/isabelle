(*  Title:      Pure/ML-Systems/polyml_pp.ML

Toplevel pretty printing for Poly/ML before 5.3.
*)

fun ml_pprint (print, begin_blk, brk, end_blk) =
  let
    fun str "" = ()
      | str s = print s;
    fun pprint (ML_Pretty.Block ((bg, en), prts, ind)) =
          (str bg; begin_blk (ind, false); List.app pprint prts; end_blk (); str en)
      | pprint (ML_Pretty.String (s, _)) = str s
      | pprint (ML_Pretty.Break (false, wd)) = brk (wd, 0)
      | pprint (ML_Pretty.Break (true, _)) = brk (99999, 0);
  in pprint end;

fun toplevel_pp tune str_of_pos output (_: string list) pp =
  use_text tune str_of_pos ML_NameSpace.global (1, "pp") output false
    ("install_pp (fn args => fn _ => fn _ => ml_pprint args o Pretty.to_ML o (" ^ pp ^ "))");

