(*  Title:      Pure/tactic.ML
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Fundamental tactics.
*)

signature TACTIC =
sig
  val trace_goalno_tac: (int -> tactic) -> int -> tactic
  val rule_by_tactic: Proof.context -> tactic -> thm -> thm
  val assume_tac: Proof.context -> int -> tactic
  val eq_assume_tac: int -> tactic
  val compose_tac: Proof.context -> (bool * thm * int) -> int -> tactic
  val make_elim: thm -> thm
  val biresolve0_tac: (bool * thm) list -> int -> tactic
  val biresolve_tac: Proof.context -> (bool * thm) list -> int -> tactic
  val resolve0_tac: thm list -> int -> tactic
  val resolve_tac: Proof.context -> thm list -> int -> tactic
  val eresolve0_tac: thm list -> int -> tactic
  val eresolve_tac: Proof.context -> thm list -> int -> tactic
  val forward_tac: Proof.context -> thm list -> int -> tactic
  val dresolve0_tac: thm list -> int -> tactic
  val dresolve_tac: Proof.context -> thm list -> int -> tactic
  val ares_tac: Proof.context -> thm list -> int -> tactic
  val solve_tac: Proof.context -> thm list -> int -> tactic
  val bimatch_tac: Proof.context -> (bool * thm) list -> int -> tactic
  val match_tac: Proof.context -> thm list -> int -> tactic
  val ematch_tac: Proof.context -> thm list -> int -> tactic
  val dmatch_tac: Proof.context -> thm list -> int -> tactic
  val flexflex_tac: Proof.context -> tactic
  val distinct_subgoals_tac: tactic
  val cut_tac: thm -> int -> tactic
  val cut_rules_tac: thm list -> int -> tactic
  val cut_facts_tac: thm list -> int -> tactic
  val filter_thms: (term * term -> bool) -> int * term * thm list -> thm list
  val rename_tac: string list -> int -> tactic
  val rotate_tac: int -> int -> tactic
  val defer_tac: int -> tactic
  val prefer_tac: int -> tactic
  val filter_prems_tac: Proof.context -> (term -> bool) -> int -> tactic
end;

structure Tactic: TACTIC =
struct

(*Discover which goal is chosen:  SOMEGOAL(trace_goalno_tac tac) *)
fun trace_goalno_tac tac i st =
    case Seq.pull(tac i st) of
        NONE    => Seq.empty
      | seqcell => (tracing ("Subgoal " ^ string_of_int i ^ " selected");
                         Seq.make(fn()=> seqcell));

(*Makes a rule by applying a tactic to an existing rule*)
fun rule_by_tactic ctxt tac rl =
  let
    val thy = Proof_Context.theory_of ctxt;
    val ctxt' = Variable.declare_thm rl ctxt;
    val ((_, [st]), ctxt'') = Variable.import true [Thm.transfer thy rl] ctxt';
  in
    (case Seq.pull (tac st) of
      NONE => raise THM ("rule_by_tactic", 0, [rl])
    | SOME (st', _) => zero_var_indexes (singleton (Variable.export ctxt'' ctxt') st'))
  end;


(*** Basic tactics ***)

(*** The following fail if the goal number is out of range:
     thus (REPEAT (resolve_tac rules i)) stops once subgoal i disappears. *)

(*Solve subgoal i by assumption*)
fun assume_tac ctxt i = PRIMSEQ (Thm.assumption (SOME ctxt) i);

(*Solve subgoal i by assumption, using no unification*)
fun eq_assume_tac i = PRIMITIVE (Thm.eq_assumption i);


(** Resolution/matching tactics **)

(*The composition rule/state: no lifting or var renaming.
  The arg = (bires_flg, orule, m);  see Thm.bicompose for explanation.*)
fun compose_tac ctxt arg i =
  PRIMSEQ (Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = false} arg i);

(*Converts a "destruct" rule like P \<and> Q \<Longrightarrow> P to an "elimination" rule
  like \<lbrakk>P \<and> Q; P \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R *)
fun make_elim rl = zero_var_indexes (rl RS revcut_rl);

(*Attack subgoal i by resolution, using flags to indicate elimination rules*)
fun biresolve0_tac brules i = PRIMSEQ (Thm.biresolution NONE false brules i);
fun biresolve_tac ctxt brules i = PRIMSEQ (Thm.biresolution (SOME ctxt) false brules i);

(*Resolution: the simple case, works for introduction rules*)
fun resolve0_tac rules = biresolve0_tac (map (pair false) rules);
fun resolve_tac ctxt rules = biresolve_tac ctxt (map (pair false) rules);

(*Resolution with elimination rules only*)
fun eresolve0_tac rules = biresolve0_tac (map (pair true) rules);
fun eresolve_tac ctxt rules = biresolve_tac ctxt (map (pair true) rules);

(*Forward reasoning using destruction rules.*)
fun forward_tac ctxt rls = resolve_tac ctxt (map make_elim rls) THEN' assume_tac ctxt;

(*Like forward_tac, but deletes the assumption after use.*)
fun dresolve0_tac rls = eresolve0_tac (map make_elim rls);
fun dresolve_tac ctxt rls = eresolve_tac ctxt (map make_elim rls);

(*Use an assumption or some rules*)
fun ares_tac ctxt rules = assume_tac ctxt ORELSE' resolve_tac ctxt rules;

fun solve_tac ctxt rules = resolve_tac ctxt rules THEN_ALL_NEW assume_tac ctxt;

(*Matching tactics -- as above, but forbid updating of state*)
fun bimatch_tac ctxt brules i = PRIMSEQ (Thm.biresolution (SOME ctxt) true brules i);
fun match_tac ctxt rules = bimatch_tac ctxt (map (pair false) rules);
fun ematch_tac ctxt rules = bimatch_tac ctxt (map (pair true) rules);
fun dmatch_tac ctxt rls = ematch_tac ctxt (map make_elim rls);

(*Smash all flex-flex disagreement pairs in the proof state.*)
fun flexflex_tac ctxt = PRIMSEQ (Thm.flexflex_rule (SOME ctxt));

(*Remove duplicate subgoals.*)
fun distinct_subgoals_tac st =
  let
    val subgoals = Thm.cprems_of st;
    val (tab, n) =
      (subgoals, (Ctermtab.empty, 0)) |-> fold (fn ct => fn (tab, i) =>
        if Ctermtab.defined tab ct then (tab, i)
        else (Ctermtab.update (ct, i) tab, i + 1));
    val st' =
      if n = length subgoals then st
      else
        let
          val thy = Thm.theory_of_thm st;
          fun cert_prop i = Thm.global_cterm_of thy (Free (Name.bound i, propT));

          val As = map (cert_prop o the o Ctermtab.lookup tab) subgoals;
          val As' = map cert_prop (0 upto (n - 1));
          val C = cert_prop n;

          val template = Drule.list_implies (As, C);
          val inst =
            Frees.build
             (Frees.add (dest_Free (Thm.term_of C), Thm.cconcl_of st) #>
              Ctermtab.fold (fn (ct, i) => Frees.add ((Name.bound i, propT), ct)) tab);
        in
          Thm.assume template
          |> fold (Thm.elim_implies o Thm.assume) As
          |> fold_rev Thm.implies_intr As'
          |> Thm.implies_intr template
          |> Thm.instantiate_frees (TFrees.empty, inst)
          |> Thm.elim_implies st
        end;
  in Seq.single st' end;


(*** Applications of cut_rl ***)

(*The conclusion of the rule gets assumed in subgoal i,
  while subgoal i+1,... are the premises of the rule.*)
fun cut_tac rule i = resolve0_tac [cut_rl] i THEN resolve0_tac [rule] (i + 1);

(*"Cut" a list of rules into the goal.  Their premises will become new
  subgoals.*)
fun cut_rules_tac ths i = EVERY (map (fn th => cut_tac th i) ths);

(*As above, but inserts only facts (unconditional theorems);
  generates no additional subgoals. *)
fun cut_facts_tac ths = cut_rules_tac (filter Thm.no_prems ths);


(**** Indexing and filtering of theorems ****)

(*Returns the list of potentially resolvable theorems for the goal "prem",
        using the predicate  could(subgoal,concl).
  Resulting list is no longer than "limit"*)
fun filter_thms could (limit, prem, ths) =
  let val pb = Logic.strip_assums_concl prem;   (*delete assumptions*)
      fun filtr (limit, []) = []
        | filtr (limit, th::ths) =
            if limit=0 then  []
            else if could(pb, Thm.concl_of th)  then th :: filtr(limit-1, ths)
            else filtr(limit,ths)
  in  filtr(limit,ths)  end;


(*Renaming of parameters in a subgoal*)
fun rename_tac xs i =
  case find_first (not o Symbol_Pos.is_identifier) xs of
      SOME x => error ("Not an identifier: " ^ x)
    | NONE => PRIMITIVE (Thm.rename_params_rule (xs, i));

(*rotate_tac n i: rotate the assumptions of subgoal i by n positions, from
  right to left if n is positive, and from left to right if n is negative.*)
fun rotate_tac 0 i = all_tac
  | rotate_tac k i = PRIMITIVE (Thm.rotate_rule k i);

(*Rotate the given subgoal to be the last.*)
fun defer_tac i = PRIMITIVE (Thm.permute_prems (i - 1) 1);

(*Rotate the given subgoal to be the first.*)
fun prefer_tac i = PRIMITIVE (Thm.permute_prems (i - 1) 1 #> Thm.permute_prems 0 ~1);

(*Remove premises that do not satisfy pred; fails if all prems satisfy pred.*)
fun filter_prems_tac ctxt pred =
  let
    fun Then NONE tac = SOME tac
      | Then (SOME tac) tac' = SOME (tac THEN' tac');
    fun thins H (tac, n) =
      if pred H then (tac, n + 1)
      else (Then tac (rotate_tac n THEN' eresolve_tac ctxt [thin_rl]), 0);
  in
    SUBGOAL (fn (goal, i) =>
      let val Hs = Logic.strip_assums_hyp goal in
        (case fst (fold thins Hs (NONE, 0)) of
          NONE => no_tac
        | SOME tac => tac i)
      end)
  end;

end;

open Tactic;
