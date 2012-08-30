(*  Title:      HOL/Codatatype/Tools/bnf_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar on top of a BNF.
*)

signature BNF_SUGAR =
sig
  val prepare_sugar : (Proof.context -> 'b -> term) ->
    (((typ * 'b list) * binding list) * binding list list) * 'b -> local_theory ->
    term list * local_theory
end;

structure BNF_Sugar : BNF_SUGAR =
struct

open BNF_Util

fun prepare_sugar prep_term ((((raw_T, raw_ctors), raw_dtors), raw_storss), raw_recur) lthy =
  let
    val ctors = map (prep_term lthy) raw_ctors;

    (* TODO: sanity checks on arguments *)
    val ctor_Tss = map (binder_types o fastype_of) ctors;
    val (ctor_argss, _) = lthy |>
      mk_Freess "x" ctor_Tss;

    val goal_distincts =
      let
        fun mk_goal t u = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (t, u)))
        fun mk_goals [] = []
          | mk_goals (t :: ts) = fold_rev (cons o mk_goal t) ts (mk_goals ts)
      in
        mk_goals (map2 (curry Term.list_comb) ctors ctor_argss)
      end;

    val goals = goal_distincts;
  in
    (goals, lthy)
  end;

val parse_binding_list = Parse.$$$ "[" |--  Parse.list Parse.binding --| Parse.$$$ "]";

val bnf_sugar_cmd = (fn (goals, lthy) =>
  Proof.theorem NONE (K I) (map (single o rpair []) goals) lthy) oo prepare_sugar Syntax.read_term;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "bnf_sugar"} "adds sugar on top of a BNF"
    ((Parse.typ -- (Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") --
      parse_binding_list -- (Parse.$$$ "[" |-- Parse.list parse_binding_list --| Parse.$$$ "]") --
      Parse.term) >> bnf_sugar_cmd);

end;
