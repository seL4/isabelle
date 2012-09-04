(*  Title:      HOL/Codatatype/Tools/bnf_fp_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar for constructing LFPs and GFPs.
*)

signature BNF_FP_SUGAR =
sig
end;

structure BNF_FP_Sugar : BNF_FP_SUGAR =
struct

fun data_cmd gfp specs lthy =
  let
  in
    lthy
  end;

val parse_ctr_arg =
  Parse.$$$ "(" |-- Scan.option Parse.binding --| Parse.$$$ ":" -- Parse.typ --| Parse.$$$ ")" ||
  (Parse.typ >> pair NONE);

val parse_single_spec =
  Parse.type_args_constrained -- Parse.binding -- Parse.opt_mixfix --
  (@{keyword "="} |-- Parse.enum1 "|" (Parse.binding -- Scan.repeat parse_ctr_arg --
     Parse.opt_mixfix))
  >> (fn (((vs, t), mx), cons) => ((t, vs, mx), map Parse.triple1 cons));

val _ =
  Outer_Syntax.local_theory @{command_spec "data"} "define BNF-based inductive datatypes"
    (Parse.and_list1 parse_single_spec >> data_cmd false);

val _ =
  Outer_Syntax.local_theory @{command_spec "codata"} "define BNF-based coinductive datatypes"
    (Parse.and_list1 parse_single_spec >> data_cmd true);

end;
