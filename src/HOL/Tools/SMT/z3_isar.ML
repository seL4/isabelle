(*  Title:      HOL/Tools/SMT/z3_isar.ML
    Author:     Jasmin Blanchette, TU Muenchen

Z3 proofs as generic ATP proofs for Isar proof reconstruction.
*)

signature Z3_ISAR =
sig
  val atp_proof_of_z3_proof: Proof.context -> term list -> thm list -> term list -> term ->
    (string * term) list -> int list -> int -> (int * string) list -> Z3_Proof.z3_step list ->
    (term, string) ATP_Proof.atp_step list
end;

structure Z3_Isar: Z3_ISAR =
struct

open ATP_Util
open ATP_Problem
open ATP_Proof
open ATP_Proof_Reconstruct
open SMTLIB_Isar

val z3_apply_def_rule = Z3_Proof.string_of_rule Z3_Proof.Apply_Def
val z3_hypothesis_rule = Z3_Proof.string_of_rule Z3_Proof.Hypothesis
val z3_intro_def_rule = Z3_Proof.string_of_rule Z3_Proof.Intro_Def
val z3_lemma_rule = Z3_Proof.string_of_rule Z3_Proof.Lemma

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
            val hyps' = fold (AList.update (op =) o apsnd (insert (op =) name)) add_hyps hyps
          in
            (name, role, t', rule, deps') :: inline_z3_hypotheses hyp_names hyps' lines
          end
      end

fun dest_alls (Const (\<^const_name>\<open>Pure.all\<close>, _) $ Abs (abs as (_, T, _))) =
    let val (s', t') = Term.dest_abs abs in
      dest_alls t' |>> cons (s', T)
    end
  | dest_alls t = ([], t)

val reorder_foralls =
  dest_alls
  #>> sort_by fst
  #-> fold_rev (Logic.all o Free);

fun atp_proof_of_z3_proof ctxt ll_defs rewrite_rules hyp_ts concl_t fact_helper_ts prem_ids
    conjecture_id fact_helper_ids proof =
  let
    fun steps_of (Z3_Proof.Z3_Step {id, rule, prems, concl, ...}) : (term, string) ATP_Proof.atp_step list =
      let
        val sid = string_of_int id

        val concl' = concl
          |> reorder_foralls (* crucial for skolemization steps *)
          |> postprocess_step_conclusion ctxt rewrite_rules ll_defs
        fun standard_step role =
          ((sid, []), role, concl', Z3_Proof.string_of_rule rule,
           map (fn id => (string_of_int id, [])) prems)
      in
        (case rule of
          Z3_Proof.Asserted =>
          let val ss = the_list (AList.lookup (op =) fact_helper_ids id) in
            (case distinguish_conjecture_and_hypothesis ss id conjecture_id prem_ids fact_helper_ts
                hyp_ts concl_t of
              NONE => [] (* useless nontheory tautology *)
            | SOME (role0, concl00) =>
              let
                val name0 = (sid ^ "a", ss)
                val concl0 = unskolemize_names ctxt concl00
              in
                (if role0 = Axiom then []
                 else [(name0, role0, concl0, Z3_Proof.string_of_rule rule, [])]) @
                [((sid, []), Plain, concl', Z3_Proof.string_of_rule Z3_Proof.Rewrite,
                  name0 :: normalizing_prems ctxt concl0)]
              end)
          end
        | Z3_Proof.Rewrite => [standard_step Lemma]
        | Z3_Proof.Rewrite_Star => [standard_step Lemma]
        | Z3_Proof.Skolemize => [standard_step Lemma]
        | Z3_Proof.Th_Lemma _ => [standard_step Lemma]
        | _ => [standard_step Plain])
      end
  in
    proof
    |> maps steps_of
    |> inline_z3_defs []
    |> inline_z3_hypotheses [] []
  end

end;
