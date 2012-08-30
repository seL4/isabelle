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

fun prepare_sugar prep_term (((raw_ctors, raw_caseof), dtor_names), stor_namess) no_defs_lthy =
  let
    (* TODO: sanity checks on arguments *)

    val ctors = map (prep_term no_defs_lthy) raw_ctors;
    val ctor_Tss = map (binder_types o fastype_of) ctors;

    val caseof = prep_term no_defs_lthy raw_caseof;

    val T as Type (T_name, As) = body_type (fastype_of (hd ctors));
    val b = Binding.qualified_name T_name;

    val n = length ctors;
    val ks = 1 upto n;

    fun mk_caseof T =
      let
        val (binders, body) = strip_type (fastype_of caseof);
      in
        Term.subst_atomic_types ((body, T) :: (snd (dest_Type (List.last binders)) ~~ As)) caseof
      end;

    val ((((xss, yss), (v, v')), p), no_defs_lthy') = no_defs_lthy |>
      mk_Freess "x" ctor_Tss
      ||>> mk_Freess "y" ctor_Tss
      ||>> yield_singleton (apfst (op ~~) oo mk_Frees' "v") T
      ||>> yield_singleton (mk_Frees "P") HOLogic.boolT;

    val xs_ctors = map2 (curry Term.list_comb) ctors xss;
    val ys_ctors = map2 (curry Term.list_comb) ctors yss;

    val exist_xs_v_eq_ctors =
      map2 (fn xs_ctor => fn xs => list_exists_free xs (HOLogic.mk_eq (v, xs_ctor))) xs_ctors xss;

    fun dtor_spec b exist_xs_v_eq_ctor =
      HOLogic.mk_Trueprop
        (HOLogic.mk_eq (Free (Binding.name_of b, T --> HOLogic.boolT) $ v, exist_xs_v_eq_ctor));

    fun stor_spec b x xs xs_ctor k =
      let
        val T' = fastype_of x;
      in
        HOLogic.mk_Trueprop
          (HOLogic.mk_eq (Free (Binding.name_of b, T --> T') $ v,
            Term.list_comb (mk_caseof T', map2 (fn Ts => fn i =>
              if i = k then fold_rev lambda xs x else Const (@{const_name undefined}, Ts ---> T'))
              ctor_Tss ks) $ v))
      end;

    val ((dtor_defs, stor_defss), (lthy', lthy)) =
      no_defs_lthy
      |> fold_map2 (fn b => fn exist_xs_v_eq_ctor =>
        Specification.definition (SOME (b, NONE, NoSyn),
          ((Thm.def_binding b, []), dtor_spec b exist_xs_v_eq_ctor))) dtor_names exist_xs_v_eq_ctors
      ||>> fold_map4 (fn bs => fn xs => fn xs_ctor => fn k =>
        fold_map2 (fn b => fn x =>
          Specification.definition (SOME (b, NONE, NoSyn),
            ((Thm.def_binding b, []), stor_spec b x xs xs_ctor k))) bs xs) stor_namess xss xs_ctors
          ks
      ||> `Local_Theory.restore;

    val goal_exhaust =
      let
        fun mk_imp_p Q = Logic.list_implies (Q, HOLogic.mk_Trueprop p);
        fun mk_prem xs_ctor xs =
          fold_rev Logic.all xs (mk_imp_p [HOLogic.mk_Trueprop (HOLogic.mk_eq (v, xs_ctor))]);
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
            val goal =
              HOLogic.mk_Trueprop (HOLogic.mk_all (fst v', snd v',
                   Library.foldr1 HOLogic.mk_disj exist_xs_v_eq_ctors));
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
    (((Parse.$$$ "[" |-- Parse.list Parse.term --| Parse.$$$ "]") -- Parse.term --
      parse_binding_list -- (Parse.$$$ "[" |-- Parse.list parse_binding_list --| Parse.$$$ "]"))
      >> bnf_sugar_cmd);

end;
