(*  Title:      HOL/Tools/SMT2/z3_new_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Z3 proofs as generic ATP proofs for Isar proof reconstruction.
*)

signature Z3_NEW_ISAR =
sig
  type ('a, 'b) atp_step = ('a, 'b) ATP_Proof.atp_step

  val atp_proof_of_z3_proof: theory -> thm list -> int -> (int * string) list ->
    Z3_New_Proof.z3_step list -> (term, string) atp_step list
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

fun simplify_bool (@{const Not} $ t) = s_not (simplify_bool t)
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

fun atp_proof_of_z3_proof thy rewrite_rules conjecture_id fact_ids proof =
  let
    fun step_of (Z3_New_Proof.Z3_Step {id, rule, prems, concl, ...}) =
      let
        fun step_name_of id = (string_of_int id, the_list (AList.lookup (op =) fact_ids id))

        val name as (_, ss) = step_name_of id

        val role =
          (case rule of
            Z3_New_Proof.Asserted =>
              if not (null ss) then Axiom
              else if id = conjecture_id then Negated_Conjecture
              else Hypothesis
          | Z3_New_Proof.Rewrite => Lemma
          | Z3_New_Proof.Rewrite_Star => Lemma
          | Z3_New_Proof.Skolemize => Lemma
          | Z3_New_Proof.Th_Lemma _ => Lemma
          | _ => Plain)

        val concl' = concl
          |> Raw_Simplifier.rewrite_term thy rewrite_rules []
          |> Object_Logic.atomize_term thy
          |> simplify_bool
          |> unskolemize_names
          |> HOLogic.mk_Trueprop
      in
        (name, role, concl', Z3_New_Proof.string_of_rule rule, map step_name_of prems)
      end
  in
    proof
    |> map step_of
    |> inline_z3_defs []
    |> inline_z3_hypotheses [] []
  end

end;
