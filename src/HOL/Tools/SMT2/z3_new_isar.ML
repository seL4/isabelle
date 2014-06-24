(*  Title:      HOL/Tools/SMT2/z3_new_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Z3 proofs as generic ATP proofs for Isar proof reconstruction.
*)

signature Z3_NEW_ISAR =
sig
  val atp_proof_of_z3_proof: Proof.context -> thm list -> term list -> term ->
    (string * term) list -> int list -> int -> (int * string) list -> Z3_New_Proof.z3_step list ->
    (term, string) ATP_Proof.atp_step list
end;

structure Z3_New_Isar: Z3_NEW_ISAR =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct

val z3_apply_def_rule = Z3_New_Proof.string_of_rule Z3_New_Proof.Apply_Def
val z3_hypothesis_rule = Z3_New_Proof.string_of_rule Z3_New_Proof.Hypothesis
val z3_intro_def_rule = Z3_New_Proof.string_of_rule Z3_New_Proof.Intro_Def
val z3_lemma_rule = Z3_New_Proof.string_of_rule Z3_New_Proof.Lemma

fun inline_z3_defs _ [] = []
  | inline_z3_defs defs ((name, role, t, rule, deps) :: lines) =
    if rule = z3_intro_def_rule then
      let val def = t |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> swap in
        inline_z3_defs (insert (op =) def defs)
          (map (replace_dependencies_in_line (name, [])) lines)
      end
    else if rule = z3_apply_def_rule then
      inline_z3_defs defs (map (replace_dependencies_in_line (name, [])) lines)
    else
      (name, role, Term.subst_atomic defs t, rule, deps) :: inline_z3_defs defs lines

fun add_z3_hypotheses [] = I
  | add_z3_hypotheses hyps =
    HOLogic.dest_Trueprop
    #> curry s_imp (Library.foldr1 s_conj (map HOLogic.dest_Trueprop hyps))
    #> HOLogic.mk_Trueprop

fun inline_z3_hypotheses _ _ [] = []
  | inline_z3_hypotheses hyp_names hyps ((name, role, t, rule, deps) :: lines) =
    if rule = z3_hypothesis_rule then
      inline_z3_hypotheses (name :: hyp_names) (AList.map_default (op =) (t, []) (cons name) hyps)
        lines
    else
      let val deps' = subtract (op =) hyp_names deps in
        if rule = z3_lemma_rule then
          (name, role, t, rule, deps') :: inline_z3_hypotheses hyp_names hyps lines
        else
          let
            val add_hyps = filter_out (null o inter (op =) deps o snd) hyps
            val t' = add_z3_hypotheses (map fst add_hyps) t
            val deps' = subtract (op =) hyp_names deps
            val hyps' = fold (AList.update (op =) o apsnd (insert (op =) name)) add_hyps hyps
          in
            (name, role, t', rule, deps') :: inline_z3_hypotheses hyp_names hyps' lines
          end
      end

fun simplify_bool ((all as Const (@{const_name All}, _)) $ Abs (s, T, t)) =
    let val t' = simplify_bool t in
      if loose_bvar1 (t', 0) then all $ Abs (s, T, t') else t'
    end
  | simplify_bool (@{const Not} $ t) = s_not (simplify_bool t)
  | simplify_bool (@{const conj} $ t $ u) = s_conj (simplify_bool t, simplify_bool u)
  | simplify_bool (@{const disj} $ t $ u) = s_disj (simplify_bool t, simplify_bool u)
  | simplify_bool (@{const implies} $ t $ u) = s_imp (simplify_bool t, simplify_bool u)
  | simplify_bool (@{const HOL.eq (bool)} $ t $ u) = s_iff (simplify_bool t, simplify_bool u)
  | simplify_bool (t as Const (@{const_name HOL.eq}, _) $ u $ v) =
    if u aconv v then @{const True} else t
  | simplify_bool (t $ u) = simplify_bool t $ simplify_bool u
  | simplify_bool (Abs (s, T, t)) = Abs (s, T, simplify_bool t)
  | simplify_bool t = t

(* It is not entirely clear why this should be necessary, especially for abstractions variables. *)
val unskolemize_names =
  Term.map_abs_vars (perhaps (try Name.dest_skolem))
  #> Term.map_aterms (perhaps (try (fn Free (s, T) => Free (Name.dest_skolem s, T))))

fun strip_alls (Const (@{const_name All}, _) $ Abs (s, T, body)) = strip_alls body |>> cons (s, T)
  | strip_alls t = ([], t)

fun push_skolem_all_under_iff t =
  (case strip_alls t of
    (qs as _ :: _,
     (t0 as Const (@{const_name HOL.eq}, _)) $ (t1 as Const (@{const_name Ex}, _) $ _) $ t2) =>
    t0 $ HOLogic.list_all (qs, t1) $ HOLogic.list_all (qs, t2)
  | _ => t)

fun atp_proof_of_z3_proof ctxt rewrite_rules hyp_ts concl_t fact_helper_ts prem_ids conjecture_id
    fact_helper_ids proof =
  let
    val thy = Proof_Context.theory_of ctxt

    fun steps_of (Z3_New_Proof.Z3_Step {id, rule, prems, concl, ...}) =
      let
        val sid = string_of_int id

        val concl' =
          concl
          |> Raw_Simplifier.rewrite_term thy rewrite_rules []
          |> Object_Logic.atomize_term thy
          |> simplify_bool
          |> unskolemize_names
          |> push_skolem_all_under_iff
          |> HOLogic.mk_Trueprop

        fun standard_step role =
          ((sid, []), role, concl', Z3_New_Proof.string_of_rule rule,
           map (fn id => (string_of_int id, [])) prems)
      in
        (case rule of
          Z3_New_Proof.Asserted =>
          let
            val ss = the_list (AList.lookup (op =) fact_helper_ids id)
            val name0 = (sid ^ "a", ss)

            val (role0, concl0) =
              (case ss of
                [s] => (Axiom, the (AList.lookup (op =) fact_helper_ts s))
              | _ =>
                if id = conjecture_id then
                  (Conjecture, concl_t)
                else
                  (Hypothesis,
                   (case find_index (curry (op =) id) prem_ids of
                     ~1 => concl
                   | i => nth hyp_ts i)))

            val normalize_prems =
              SMT2_Normalize.case_bool_entry :: SMT2_Normalize.special_quant_table @
              SMT2_Normalize.abs_min_max_table
              |> map_filter (fn (c, th) =>
                if exists_Const (curry (op =) c o fst) concl0 then
                  let val s = short_thm_name ctxt th in SOME (s, [s]) end
                else
                  NONE)
          in
            (if role0 = Axiom then []
             else [(name0, role0, concl0, Z3_New_Proof.string_of_rule rule, [])]) @
            [((sid, []), Plain, concl', Z3_New_Proof.string_of_rule Z3_New_Proof.Rewrite,
              name0 :: normalize_prems)]
          end
        | Z3_New_Proof.Rewrite => [standard_step Lemma]
        | Z3_New_Proof.Rewrite_Star => [standard_step Lemma]
        | Z3_New_Proof.Skolemize => [standard_step Lemma]
        | Z3_New_Proof.Th_Lemma _ => [standard_step Lemma]
        | _ => [standard_step Plain])
      end
  in
    proof
    |> maps steps_of
    |> inline_z3_defs []
    |> inline_z3_hypotheses [] []
  end

end;
