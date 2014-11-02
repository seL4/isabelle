(*  Title:      HOL/Library/Code_Abstract_Nat.thy
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen
*)

section {* Avoidance of pattern matching on natural numbers *}

theory Code_Abstract_Nat
imports Main
begin

text {*
  When natural numbers are implemented in another than the
  conventional inductive @{term "0::nat"}/@{term Suc} representation,
  it is necessary to avoid all pattern matching on natural numbers
  altogether.  This is accomplished by this theory (up to a certain
  extent).
*}

subsection {* Case analysis *}

text {*
  Case analysis on natural numbers is rephrased using a conditional
  expression:
*}

lemma [code, code_unfold]:
  "case_nat = (\<lambda>f g n. if n = 0 then f else g (n - 1))"
  by (auto simp add: fun_eq_iff dest!: gr0_implies_Suc)


subsection {* Preprocessors *}

text {*
  The term @{term "Suc n"} is no longer a valid pattern.  Therefore,
  all occurrences of this term in a position where a pattern is
  expected (i.e.~on the left-hand side of a code equation) must be
  eliminated.  This can be accomplished -- as far as possible -- by
  applying the following transformation rule:
*}

lemma Suc_if_eq:
  assumes "\<And>n. f (Suc n) \<equiv> h n"
  assumes "f 0 \<equiv> g"
  shows "f n \<equiv> if n = 0 then g else h (n - 1)"
  by (rule eq_reflection) (cases n, insert assms, simp_all)

text {*
  The rule above is built into a preprocessor that is plugged into
  the code generator.
*}

setup {*
let

val Suc_if_eq = Thm.incr_indexes 1 @{thm Suc_if_eq};

fun remove_suc ctxt thms =
  let
    val thy = Proof_Context.theory_of ctxt;
    val vname = singleton (Name.variant_list (map fst
      (fold (Term.add_var_names o Thm.full_prop_of) thms []))) "n";
    val cv = cterm_of thy (Var ((vname, 0), HOLogic.natT));
    val lhs_of = snd o Thm.dest_comb o fst o Thm.dest_comb o cprop_of;
    val rhs_of = snd o Thm.dest_comb o cprop_of;
    fun find_vars ct = (case term_of ct of
        (Const (@{const_name Suc}, _) $ Var _) => [(cv, snd (Thm.dest_comb ct))]
      | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in 
          map (apfst (fn ct => Thm.apply ct ct2)) (find_vars ct1) @
          map (apfst (Thm.apply ct1)) (find_vars ct2)
        end
      | _ => []);
    val eqs = maps
      (fn thm => map (pair thm) (find_vars (lhs_of thm))) thms;
    fun mk_thms (thm, (ct, cv')) =
      let
        val thm' =
          Thm.implies_elim
           (Conv.fconv_rule (Thm.beta_conversion true)
             (Drule.instantiate'
               [SOME (ctyp_of_term ct)] [SOME (Thm.lambda cv ct),
                 SOME (Thm.lambda cv' (rhs_of thm)), NONE, SOME cv']
               Suc_if_eq)) (Thm.forall_intr cv' thm)
      in
        case map_filter (fn thm'' =>
            SOME (thm'', singleton
              (Variable.trade (K (fn [thm'''] => [thm''' RS thm']))
                (Variable.global_thm_context thm'')) thm'')
          handle THM _ => NONE) thms of
            [] => NONE
          | thmps =>
              let val (thms1, thms2) = split_list thmps
              in SOME (subtract Thm.eq_thm (thm :: thms1) thms @ thms2) end
      end
  in get_first mk_thms eqs end;

fun eqn_suc_base_preproc thy thms =
  let
    val dest = fst o Logic.dest_equals o prop_of;
    val contains_suc = exists_Const (fn (c, _) => c = @{const_name Suc});
  in
    if forall (can dest) thms andalso exists (contains_suc o dest) thms
      then thms |> perhaps_loop (remove_suc thy) |> (Option.map o map) Drule.zero_var_indexes
       else NONE
  end;

val eqn_suc_preproc = Code_Preproc.simple_functrans eqn_suc_base_preproc;

in

  Code_Preproc.add_functrans ("eqn_Suc", eqn_suc_preproc)

end;
*}

end
