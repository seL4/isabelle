(*  Title:      Tools/Argo/argo_cdcl.ML
    Author:     Sascha Boehme

Propositional satisfiability solver in the style of conflict-driven
clause-learning (CDCL). It features:

 * conflict analysis and clause learning based on the first unique implication point
 * nonchronological backtracking
 * dynamic variable ordering (VSIDS)
 * restarting
 * polarity caching
 * propagation via two watched literals
 * special propagation of binary clauses 
 * minimizing learned clauses
 * support for external knowledge

These features might be added:

 * pruning of unnecessary learned clauses
 * rebuilding the variable heap
 * aligning the restart level with the decision heuristics: keep decisions that would
   be recovered instead of backjumping to level 0

The implementation is inspired by:

  Niklas E'en and Niklas S"orensson. An Extensible SAT-solver. In Enrico
  Giunchiglia and Armando Tacchella, editors, Theory and Applications of
  Satisfiability Testing. Volume 2919 of Lecture Notes in Computer
  Science, pages 502-518. Springer, 2003.

  Niklas S"orensson and Armin Biere. Minimizing Learned Clauses. In
  Oliver Kullmann, editor, Theory and Applications of Satisfiability
  Testing. Volume 5584 of Lecture Notes in Computer Science,
  pages 237-243. Springer, 2009.
*)

signature ARGO_CDCL =
sig
  (* types *)
  type 'a explain = Argo_Lit.literal -> 'a -> Argo_Cls.clause * 'a

  (* context *)
  type context
  val context: context
  val assignment_of: context -> Argo_Lit.literal -> bool option

  (* enriching the context *)
  val add_atom: Argo_Term.term -> context -> context
  val add_axiom: Argo_Cls.clause -> context -> int * context

  (* main operations *)
  val assume: 'a explain -> Argo_Lit.literal -> context -> 'a ->
    Argo_Cls.clause option * context * 'a
  val propagate: context -> Argo_Common.literal Argo_Common.implied * context
  val decide: context -> context option
  val analyze: 'a explain -> Argo_Cls.clause -> context -> 'a -> int * context * 'a
  val restart: context -> int * context
end

structure Argo_Cdcl: ARGO_CDCL =
struct

(* basic types and operations *)

type 'a explain = Argo_Lit.literal -> 'a -> Argo_Cls.clause * 'a

datatype reason =
  Level0 of Argo_Proof.proof |
  Decided of int * int * (bool * reason) Argo_Termtab.table |
  Implied of int * int * (Argo_Lit.literal * reason) list * Argo_Proof.proof |
  External of int

fun level_of (Level0 _) = 0
  | level_of (Decided (l, _, _)) = l
  | level_of (Implied (l, _, _, _)) = l
  | level_of (External l) = l

type justified = Argo_Lit.literal * reason

type watches = Argo_Cls.clause list * Argo_Cls.clause list

fun get_watches wts t = Argo_Termtab.lookup wts t
fun map_watches f t wts = Argo_Termtab.map_default (t, ([], [])) f wts

fun map_lit_watches f (Argo_Lit.Pos t) = map_watches (apsnd f) t
  | map_lit_watches f (Argo_Lit.Neg t) = map_watches (apfst f) t

fun watches_of wts (Argo_Lit.Pos t) = (case get_watches wts t of SOME (ws, _) => ws | NONE => [])
  | watches_of wts (Argo_Lit.Neg t) = (case get_watches wts t of SOME (_, ws) => ws | NONE => [])

fun attach cls lit = map_lit_watches (cons cls) lit
fun detach cls lit = map_lit_watches (remove Argo_Cls.eq_clause cls) lit


(* literal values *)

fun raw_val_of vals lit = Argo_Termtab.lookup vals (Argo_Lit.term_of lit)

fun val_of vals (Argo_Lit.Pos t) = Argo_Termtab.lookup vals t
  | val_of vals (Argo_Lit.Neg t) = Option.map (apfst not) (Argo_Termtab.lookup vals t)

fun value_of vals (Argo_Lit.Pos t) = Option.map fst (Argo_Termtab.lookup vals t)
  | value_of vals (Argo_Lit.Neg t) = Option.map (not o fst) (Argo_Termtab.lookup vals t)

fun justified vals lit = Option.map (pair lit o snd) (raw_val_of vals lit)
fun the_reason_of vals lit = snd (the (raw_val_of vals lit))

fun assign (Argo_Lit.Pos t) r = Argo_Termtab.update (t, (true, r))
  | assign (Argo_Lit.Neg t) r = Argo_Termtab.update (t, (false, r))


(* context *)

type trail = int * justified list (* the trail height and the sequence of assigned literals *)

type context = {
  units: Argo_Common.literal list, (* the literals that await propagation *)
  level: int, (* the decision level *)
  trail: int * justified list, (* the trail height and the sequence of assigned literals *)
  vals: (bool * reason) Argo_Termtab.table, (* mapping of terms to polarity and reason *)
  wts: watches Argo_Termtab.table, (* clauses watched by terms *)
  heap: Argo_Heap.heap, (* max-priority heap for decision heuristics *)
  clss: Argo_Cls.table, (* information about clauses *)
  prf: Argo_Proof.context} (* the proof context *)

fun mk_context units level trail vals wts heap clss prf: context =
  {units=units, level=level, trail=trail, vals=vals, wts=wts, heap=heap, clss=clss, prf=prf}

val context =
  mk_context [] 0 (0, []) Argo_Termtab.empty Argo_Termtab.empty Argo_Heap.heap
    Argo_Cls.table Argo_Proof.cdcl_context

fun drop_levels n (Decided (l, h, vals)) trail heap =
      if l = n + 1 then ((h, trail), vals, heap) else drop_literal n trail heap
  | drop_levels n _ tr heap = drop_literal n tr heap

and drop_literal n ((lit, r) :: trail) heap = drop_levels n r trail (Argo_Heap.insert lit heap)
  | drop_literal _ [] _ = raise Fail "bad trail"

fun backjump_to new_level (cx as {level, trail=(_, tr), wts, heap, clss, prf, ...}: context) =
  if new_level >= level then (0, cx)
  else
    let val (trail, vals, heap) = drop_literal (Integer.max 0 new_level) tr heap
    in (level - new_level, mk_context [] new_level trail vals wts heap clss prf) end


(* proofs *)

fun tag_clause (lits, p) prf = Argo_Proof.mk_clause lits p prf |>> pair lits

fun level0_unit_proof (lit, Level0 p') (p, prf) = Argo_Proof.mk_unit_res lit p p' prf
  | level0_unit_proof _ _ = raise Fail "bad reason"

fun level0_unit_proofs lrs p prf = fold level0_unit_proof lrs (p, prf)

fun unsat ({vals, prf, ...}: context) (lits, p) =
  let val lrs = map (fn lit => (lit, the_reason_of vals lit)) lits
  in Argo_Proof.unsat (fst (level0_unit_proofs lrs p prf)) end


(* literal operations *)

fun push lit p reason prf ({units, level, trail=(h, tr), vals, wts, heap, clss, ...}: context) =
  let val vals = assign lit reason vals
  in mk_context ((lit, p) :: units) level (h + 1, (lit, reason) :: tr) vals wts heap clss prf end

fun push_level0 lit p lrs (cx as {prf, ...}: context) =
  let val (p, prf) = level0_unit_proofs lrs p prf
  in push lit (SOME p) (Level0 p) prf cx end

fun push_implied lit p lrs (cx as {level, trail=(h, _), prf, ...}: context) =
  if level > 0 then push lit NONE (Implied (level, h, lrs, p)) prf cx
  else push_level0 lit p lrs cx

fun push_decided lit (cx as {level, trail=(h, _), vals, prf, ...}: context) =
  push lit NONE (Decided (level, h, vals)) prf cx

fun assignment_of ({vals, ...}: context) = value_of vals

fun replace_watches old new cls ({units, level, trail, vals, wts, heap, clss, prf}: context) =
  mk_context units level trail vals (attach cls new (detach cls old wts)) heap clss prf


(* clause operations *)

fun as_clause cls ({units, level, trail, vals, wts, heap, clss, prf}: context) =
  let val (cls, prf) = tag_clause cls prf
  in (cls, mk_context units level trail vals wts heap clss prf) end

fun note_watches ([_, _], _) _ clss = clss
  | note_watches cls lp clss = Argo_Cls.put_watches cls lp clss

fun attach_clause lit1 lit2 (cls as (lits, _)) cx =
  let
    val {units, level, trail, vals, wts, heap, clss, prf}: context = cx
    val wts = attach cls lit1 (attach cls lit2 wts)
    val clss = note_watches cls (lit1, lit2) clss
  in mk_context units level trail vals wts (fold Argo_Heap.count lits heap) clss prf end

fun change_watches _ (false, _, _) cx = cx
  | change_watches cls (true, l1, l2) ({units, level, trail, vals, wts, heap, clss, prf}: context) =
      mk_context units level trail vals wts heap (Argo_Cls.put_watches cls (l1, l2) clss) prf

fun add_asserting lit lit' (cls as (_, p)) lrs cx =
  attach_clause lit lit' cls (push_implied lit p lrs cx)

(*
  When learning a non-unit clause, the context is backtracked to the highest decision level
  of the assigned literals.
*)

fun learn_clause _ ([lit], p) cx = backjump_to 0 cx ||> push_level0 lit p []
  | learn_clause lrs (cls as (lits, _)) cx =
      let
        fun max_level (l, r) (ll as (_, lvl)) = if level_of r > lvl then (l, level_of r) else ll
        val (lit, lvl) = fold max_level lrs (hd lits, 0)
      in backjump_to lvl cx ||> add_asserting (hd lits) lit cls lrs end

(*
  An axiom with one unassigned literal and all remaining literals being assigned to
  false is asserting. An axiom with all literals assigned to false on level 0 makes the
  context unsatisfiable. An axiom with all literals assigned to false on higher levels
  causes backjumping before the highest level, and then the axiom might be asserting if
  only one literal is unassigned on that level.
*)

fun min lit i NONE = SOME (lit, i)
  | min lit i (SOME (lj as (_, j))) = SOME (if i < j then (lit, i) else lj)

fun level_ord ((_, r1), (_, r2)) = int_ord (level_of r2, level_of r1)
fun add_max lr lrs = Ord_List.insert level_ord lr lrs

fun part [] [] t us fs = (t, us, fs)
  | part (NONE :: vs) (l :: ls) t us fs = part vs ls t (l :: us) fs
  | part (SOME (true, r) :: vs) (l :: ls) t us fs = part vs ls (min l (level_of r) t) us fs
  | part (SOME (false, r) :: vs) (l :: ls) t us fs = part vs ls t us (add_max (l, r) fs)
  | part _ _ _ _ _ = raise Fail "mismatch between values and literals"

fun backjump_add (lit, r) (lit', r') cls lrs cx =
  let
    val add =
      if level_of r = level_of r' then attach_clause lit lit' cls
      else add_asserting lit lit' cls lrs
  in backjump_to (level_of r - 1) cx ||> add end

fun analyze_axiom vs (cls as (lits, p), cx) =
  (case part vs lits NONE [] [] of
    (SOME (lit, lvl), [], []) =>
      if lvl > 0 then backjump_to 0 cx ||> push_implied lit p [] else (0, cx)
  | (SOME (lit, lvl), [], (lit', _) :: _) => (0, cx |> (lvl > 0) ? attach_clause lit lit' cls)
  | (SOME (lit, lvl), lit' :: _, _) => (0, cx |> (lvl > 0) ? attach_clause lit lit' cls)
  | (NONE, [], (_, Level0 _) :: _) => unsat cx cls
  | (NONE, [], [(lit, _)]) => backjump_to 0 cx ||> push_implied lit p []
  | (NONE, [], lrs as (lr :: lr' :: _)) => backjump_add lr lr' cls lrs cx
  | (NONE, [lit], []) => backjump_to 0 cx ||> push_implied lit p []
  | (NONE, [lit], lrs as (lit', _) :: _) => (0, add_asserting lit lit' cls lrs cx)
  | (NONE, lit1 :: lit2 :: _, _) => (0, attach_clause lit1 lit2 cls cx)
  | _ => raise Fail "bad clause")


(* enriching the context *)

fun add_atom t ({units, level, trail, vals, wts, heap, clss, prf}: context) =
  let val heap = Argo_Heap.insert (Argo_Lit.Pos t) heap
  in mk_context units level trail vals wts heap clss prf end

fun add_axiom ([], p) _ = Argo_Proof.unsat p
  | add_axiom (cls as (lits, _)) (cx as {vals, ...}: context) =
      if has_duplicates Argo_Lit.eq_lit lits then raise Fail "clause with duplicate literals"
      else if has_duplicates Argo_Lit.dual_lit lits then (0, cx)
      else analyze_axiom (map (val_of vals) lits) (as_clause cls cx)


(* external knowledge *)

fun assume explain lit (cx as {level, vals, prf, ...}: context) x =
  (case value_of vals lit of
    SOME true => (NONE, cx, x)
  | SOME false => 
      let val (cls, x) = explain lit x
      in if level = 0 then unsat cx cls else (SOME cls, cx, x) end
  | NONE =>
      if level = 0 then
        let val ((lits, p), x) = explain lit x
        in (NONE, push_level0 lit p (map_filter (justified vals) lits) cx, x) end
      else (NONE, push lit NONE (External level) prf cx, x))


(* propagation *)

exception CONFLICT of Argo_Cls.clause * context

fun order_lits_by lit (l1, l2) =
  if Argo_Lit.eq_id (l1, lit) then (true, l2, l1) else (false, l1, l2)

fun prop_binary (_, implied_lit, other_lit) (cls as (_, p)) (cx as {level, vals, ...}: context) =
  (case value_of vals implied_lit of
    NONE => push_implied implied_lit p [(other_lit, the_reason_of vals other_lit)] cx
  | SOME true => cx
  | SOME false => if level = 0 then unsat cx cls else raise CONFLICT (cls, cx))

datatype next = Lit of Argo_Lit.literal | None of justified list

fun with_non_false f l (SOME (false, r)) lrs = f ((l, r) :: lrs)
  | with_non_false _ l _ _ = Lit l

fun first_non_false _ _ [] lrs = None lrs
  | first_non_false vals lit (l :: ls) lrs =
      if Argo_Lit.eq_lit (l, lit) then first_non_false vals lit ls lrs
      else with_non_false (first_non_false vals lit ls) l (val_of vals l) lrs

fun prop_nary (lp as (_, lit1, lit2)) (cls as (lits, p)) (cx as {level, vals, ...}: context) =
  let val v = value_of vals lit1
  in
    if v = SOME true then change_watches cls lp cx
    else
      (case first_non_false vals lit1 lits [] of
        Lit lit2' => change_watches cls (true, lit1, lit2') (replace_watches lit2 lit2' cls cx)
      | None lrs =>
          if v = NONE then push_implied lit1 p lrs (change_watches cls lp cx)
          else if level = 0 then unsat cx cls
          else raise CONFLICT (cls, change_watches cls lp cx))
  end

fun prop_cls lit (cls as ([l1, l2], _)) cx = prop_binary (order_lits_by lit (l1, l2)) cls cx
  | prop_cls lit cls (cx as {clss, ...}: context) =
      prop_nary (order_lits_by lit (Argo_Cls.get_watches clss cls)) cls cx

fun prop_lit (lp as (lit, _)) (lps, cx as {wts, ...}: context) =
  (lp :: lps, fold (prop_cls lit) (watches_of wts lit) cx)

fun prop lps (cx as {units=[], ...}: context) = (Argo_Common.Implied (rev lps), cx)
  | prop lps ({units, level, trail, vals, wts, heap, clss, prf}: context) =
      fold_rev prop_lit units (lps, mk_context [] level trail vals wts heap clss prf) |-> prop

fun propagate cx = prop [] cx
  handle CONFLICT (cls, cx) => (Argo_Common.Conflict cls, cx)


(* decisions *)

(*
  Decisions are based on an activity heuristics. The most active variable that is
  still unassigned is chosen.
*)

fun decide ({units, level, trail, vals, wts, heap, clss, prf}: context) =
  let
    fun check NONE = NONE
      | check (SOME (lit, heap)) =
          if Argo_Termtab.defined vals (Argo_Lit.term_of lit) then check (Argo_Heap.extract heap)
          else SOME (push_decided lit (mk_context units (level + 1) trail vals wts heap clss prf))
  in check (Argo_Heap.extract heap) end


(* conflict analysis and clause learning *)

(*
  Learned clauses often contain literals that are redundant, because they are
  subsumed by other literals of the clause. By analyzing the implication graph beyond
  the unique implication point, such redundant literals can be identified and hence
  removed from the learned clause. Only literals occurring in the learned clause and
  their reasons need to be analyzed.
*)

exception ESSENTIAL of unit

fun history_ord ((h1, lit1, _), (h2, lit2, _)) =
  if h1 < 0 andalso h2 < 0 then int_ord (apply2 Argo_Lit.signed_id_of (lit1, lit2))
  else int_ord (h2, h1)

fun rec_redundant stop (lit, Implied (lvl, h, lrs, p)) lps =
      if stop lit lvl then lps
      else fold (rec_redundant stop) lrs ((h, lit, p) :: lps)
  | rec_redundant stop (lit, Decided (lvl, _, _)) lps =
      if stop lit lvl then lps
      else raise ESSENTIAL ()
  | rec_redundant _ (lit, Level0 p) lps = ((~1, lit, p) :: lps)
  | rec_redundant _ _ _ = raise ESSENTIAL ()

fun redundant stop (lr as (lit, Implied (_, h, lrs, p))) (lps, essential_lrs) = (
      (fold (rec_redundant stop) lrs ((h, lit, p) :: lps), essential_lrs)
      handle ESSENTIAL () => (lps, lr :: essential_lrs))
  | redundant _ lr (lps, essential_lrs) = (lps, lr :: essential_lrs)

fun resolve_step (_, l, p') (p, prf) = Argo_Proof.mk_unit_res l p p' prf

fun reduce lrs p prf =
  let
    val lits = map fst lrs
    val levels = fold (insert (op =) o level_of o snd) lrs []
    fun stop lit level =
      if member Argo_Lit.eq_lit lits lit then true
      else if member (op =) levels level then false
      else raise ESSENTIAL ()

    val (lps, lrs) = fold (redundant stop) lrs ([], [])
  in (lrs, fold resolve_step (sort_distinct history_ord lps) (p, prf)) end

(*
  Literals that are candidates for the learned lemma are marked and unmarked while
  traversing backwards through the trail. The last remaining marked literal is the first
  unique implication point.
*)

fun unmark lit ms = remove Argo_Lit.eq_id lit ms
fun marked ms lit = member Argo_Lit.eq_id ms lit

(*
  Whenever an implication is recorded, the reason for the false literals of the
  asserting clause are known. It is reasonable to store this justification list as part
  of the implication reason. Consequently, the implementation of conflict analysis can
  benefit from this information, which does not need to be re-computed here.
*)

fun justification_for _ _ _ (Implied (_, _, lrs, p)) x = (lrs, p, x)
  | justification_for explain vals lit (External _) x =
      let val ((lits, p), x) = explain lit x
      in (map_filter (justified vals) lits, p, x) end
  | justification_for _ _ _ _ _ = raise Fail "bad reason"

fun first_lit pred ((lr as (lit, _)) :: lrs) = if pred lit then (lr, lrs) else first_lit pred lrs
  | first_lit _ _ = raise Empty

(*
  Beginning from the conflicting clause, the implication graph is traversed to the first
  unique implication point. This breadth-first search is controlled by the topological order of
  the trail, which is traversed backwards. While traversing through the trail, the conflict
  literals of lower levels are collected to form the conflict lemma together with the unique
  implication point. Conflict literals assigned on level 0 are excluded from the conflict lemma.
  Conflict literals assigned on the current level are candidates for the first unique
  implication point.
*)

fun analyze explain cls (cx as {level, trail, vals, wts, heap, clss, prf, ...}: context) x =
  let
    fun from_clause [] trail ms lrs h p prf x =
          from_trail (first_lit (marked ms) trail) ms lrs h p prf x
      | from_clause ((lit, r) :: clause_lrs) trail ms lrs h p prf x =
          from_reason r lit clause_lrs trail ms lrs h p prf x
 
    and from_reason (Level0 p') lit clause_lrs trail ms lrs h p prf x =
          let val (p, prf) = Argo_Proof.mk_unit_res lit p p' prf
          in from_clause clause_lrs trail ms lrs h p prf x end
      | from_reason r lit clause_lrs trail ms lrs h p prf x =
          if level_of r = level then
            if marked ms lit then from_clause clause_lrs trail ms lrs h p prf x
            else from_clause clause_lrs trail (lit :: ms) lrs (Argo_Heap.increase lit h) p prf x
          else
            let
              val (lrs, h) =
                if AList.defined Argo_Lit.eq_id lrs lit then (lrs, h)
                else ((lit, r) :: lrs, Argo_Heap.increase lit h)
            in from_clause clause_lrs trail ms lrs h p prf x end

    and from_trail ((lit, _), _) [_] lrs h p prf x =
          let val (lrs, (p, prf)) = reduce lrs p prf
          in (Argo_Lit.negate lit :: map fst lrs, lrs, h, p, prf, x) end
      | from_trail ((lit, r), trail) ms lrs h p prf x =
          let
            val (clause_lrs, p', x) = justification_for explain vals lit r x
            val (p, prf) = Argo_Proof.mk_unit_res lit p' p prf
          in from_clause clause_lrs trail (unmark lit ms) lrs h p prf x end

    val (ls, p) = cls
    val lrs = if level = 0 then unsat cx cls else map (fn l => (l, the_reason_of vals l)) ls
    val (lits, lrs, heap, p, prf, x) = from_clause lrs (snd trail) [] [] heap p prf x
    val heap = Argo_Heap.decay heap
    val (levels, cx) = learn_clause lrs (lits, p) (mk_context [] level trail vals wts heap clss prf)
  in (levels, cx, x) end


(* restarting *)

fun restart cx = backjump_to 0 cx

end
