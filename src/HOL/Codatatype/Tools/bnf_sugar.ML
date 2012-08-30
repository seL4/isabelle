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
open BNF_Sugar_Tactics

val distinctN = "distinct";

fun prepare_sugar prep_term (((raw_ctors, raw_dtors), raw_storss), raw_recur)
  lthy =
  let
    (* TODO: sanity checks on arguments *)

    val ctors = map (prep_term lthy) raw_ctors;
    val ctor_Tss = map (binder_types o fastype_of) ctors;

    val T as Type (T_name, _) = body_type (fastype_of (hd ctors));
    val b = Binding.qualified_name T_name;

    val n = length ctors;

    val ((((xss, yss), (v, v')), p), _) = lthy |>
      mk_Freess "x" ctor_Tss
      ||>> mk_Freess "y" ctor_Tss
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") T
      ||>> yield_singleton (mk_Frees "P") HOLogic.boolT;

    val xs_ctors = map2 (curry Term.list_comb) ctors xss;
    val ys_ctors = map2 (curry Term.list_comb) ctors yss;

    val goal_exhaust =
      let
        fun mk_imp_p Q = Logic.list_implies (Q, HOLogic.mk_Trueprop p);
        fun mk_prem xs_ctor xs =
          fold_rev Logic.all xs
            (mk_imp_p [HOLogic.mk_Trueprop (HOLogic.mk_eq (v, xs_ctor))]);
      in
        mk_imp_p (map2 mk_prem xs_ctors xss)
      end;

    val goal_injects =
      let
        fun mk_goal _ _ [] [] = NONE
          | mk_goal xs_ctor ys_ctor xs ys =
            SOME (HOLogic.mk_Trueprop (HOLogic.mk_eq
              (HOLogic.mk_eq (xs_ctor, ys_ctor),
               Library.foldr1 HOLogic.mk_conj (map2 (curry HOLogic.mk_eq) xs ys))));
      in
        map_filter I (map4 mk_goal xs_ctors ys_ctors xss yss)
      end;

    val goal_half_distincts =
      let
        fun mk_goal t u = HOLogic.mk_Trueprop (HOLogic.mk_not (HOLogic.mk_eq (t, u)));
        fun mk_goals [] = []
          | mk_goals (t :: ts) = fold_rev (cons o mk_goal t) ts (mk_goals ts);
      in
        mk_goals xs_ctors
      end;

    val goals = [[goal_exhaust], goal_injects, goal_half_distincts];

    fun after_qed thmss lthy =
      let
        val [[exhaust_thm], inject_thms, half_distinct_thms] = thmss;

        val other_half_distinct_thms = map (fn thm => thm RS not_sym) half_distinct_thms;

        val nchotomy_thm =
          let
            fun mk_disjunct xs_ctor xs = list_exists_free xs (HOLogic.mk_eq (v, xs_ctor))
            val goal =
              HOLogic.mk_Trueprop
                (HOLogic.mk_all (fst v', snd v',
                   Library.foldr1 HOLogic.mk_disj (map2 mk_disjunct xs_ctors xss)));
          in
            Skip_Proof.prove lthy [] [] goal (fn _ => mk_nchotomy_tac n exhaust_thm)
          end;

        fun note thmN thms =
          snd o Local_Theory.note
            ((Binding.qualify true (Binding.name_of b) (Binding.name thmN), []), thms);
      in
        lthy
        |> note distinctN (half_distinct_thms @ other_half_distinct_thms)
        |> note exhaustN [exhaust_thm]
        |> note injectN inject_thms
        |> note nchotomyN [nchotomy_thm]
      end;
  in
    (goals, after_qed, lthy)
  end;

val parse_binding_list = Parse.$$$ "[" |--  Parse.list Parse.binding --| Parse.$$$ "]";

val bnf_sugar_cmd = (fn (goalss, after_qed, lthy) =>
  Proof.theorem NONE after_qed (map (map (rpair [])) goalss) lthy) oo
  prepare_sugar Syntax.read_term;

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "bnf_sugar"} "adds sugar on top of a BNF"
    (((Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") --
      parse_binding_list -- (Parse.$$$ "[" |-- Parse.list parse_binding_list --| Parse.$$$ "]") --
      Parse.term) >> bnf_sugar_cmd);

end;
