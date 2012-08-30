(*  Title:      HOL/Codatatype/Tools/bnf_sugar.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2012

Sugar on top of a BNF.
*)

signature BNF_SUGAR =
sig
end;

structure BNF_Sugar : BNF_SUGAR =
struct

open BNF_Util
open BNF_FP_Util

val distinctN = "distinct";

fun prepare_sugar prep_typ prep_term ((((raw_T, raw_ctors), raw_dtors), raw_storss), raw_recur)
  lthy =
  let
    (* TODO: sanity checks on arguments *)

    val T as Type (T_name, _) = prep_typ lthy raw_T;
    val b = Binding.qualified_name T_name;

    val ctors = map (prep_term lthy) raw_ctors;
    val ctor_Tss = map (binder_types o fastype_of) ctors;

    val ((xss, yss), _) = lthy |>
      mk_Freess "x" ctor_Tss
      ||>> mk_Freess "y" ctor_Tss;

    val goal_injects =
      let
        fun mk_goal _ [] [] = NONE
          | mk_goal ctor xs ys =
            SOME (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (HOLogic.mk_eq (Term.list_comb (ctor, xs), Term.list_comb (ctor, ys)),
               Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys))));
      in
        map_filter I (map3 mk_goal ctors xss yss)
      end;

    val goal_half_distincts =
      let
        fun mk_goal t u = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (t, u)));
        fun mk_goals [] = []
          | mk_goals (t :: ts) = fold_rev (cons o mk_goal t) ts (mk_goals ts);
      in
        mk_goals (map2 (curry Term.list_comb) ctors xss)
      end;

    val goals = [goal_injects, goal_half_distincts];

    fun after_qed thmss lthy =
      let
        val [inject_thms, half_distinct_thms] = thmss;

        val other_half_distinct_thms = map (fn thm => thm RS not_sym) half_distinct_thms;

        fun note thmN thms =
          snd o Local_Theory.note
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms);
      in
        lthy
        |> note injectN inject_thms
        |> note distinctN (half_distinct_thms @ other_half_distinct_thms)
      end;
  in
    (goals, after_qed, lthy)
  end;

val parse_binding_list = Parse.$$$ "[" |--  Parse.list Parse.binding --| Parse.$$$ "]";

val bnf_sugar_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE after_qed (map (map (rpair [])) goalss) lthy) oo
  prepare_sugar Syntax.read_typ Syntax.read_term;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "bnf_sugar"} "adds sugar on top of a BNF"
    ((Parse.typ -- (Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") --
      parse_binding_list -- (Parse.$$$ "[" |-- Parse.list parse_binding_list --| Parse.$$$ "]") --
      Parse.term) >> bnf_sugar_cmd);

end;
