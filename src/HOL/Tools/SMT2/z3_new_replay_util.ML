(*  Title:      HOL/Tools/SMT2/z3_new_replay_util.ML
    Author:     Sascha Boehme, TU Muenchen

Helper functions required for Z3 proof replay.
*)

signature Z3_NEW_REPLAY_UTIL =
sig
  (*theorem nets*)
  val thm_net_of: ('a -> thm) -> 'a list -> 'a Net.net
  val net_instances: (int * thm) Net.net -> cterm -> (int * thm) list

  (*proof combinators*)
  val under_assumption: (thm -> thm) -> cterm -> thm
  val discharge: thm -> thm -> thm

  (*a faster COMP*)
  type compose_data
  val precompose: (cterm -> cterm list) -> thm -> compose_data
  val precompose2: (cterm -> cterm * cterm) -> thm -> compose_data
  val compose: compose_data -> thm -> thm

  (*simpset*)
  val add_simproc: Simplifier.simproc -> Context.generic -> Context.generic
  val make_simpset: Proof.context -> thm list -> simpset
end

structure Z3_New_Replay_Util: Z3_NEW_REPLAY_UTIL =
struct



(* theorem nets *)

fun thm_net_of f xthms =
  let fun insert xthm = Net.insert_term (K false) (Thm.prop_of (f xthm), xthm)
  in fold insert xthms Net.empty end

fun maybe_instantiate ct thm =
  try Thm.first_order_match (Thm.cprop_of thm, ct)
  |> Option.map (fn inst => Thm.instantiate inst thm)

local
  fun instances_from_net match f net ct =
    let
      val lookup = if match then Net.match_term else Net.unify_term
      val xthms = lookup net (Thm.term_of ct)
      fun select ct = map_filter (f (maybe_instantiate ct)) xthms 
      fun select' ct =
        let val thm = Thm.trivial ct
        in map_filter (f (try (fn rule => rule COMP thm))) xthms end
    in (case select ct of [] => select' ct | xthms' => xthms') end
in

fun net_instances net =
  instances_from_net false (fn f => fn (i, thm) => Option.map (pair i) (f thm))
    net

end



(* proof combinators *)

fun under_assumption f ct =
  let val ct' = SMT2_Util.mk_cprop ct in Thm.implies_intr ct' (f (Thm.assume ct')) end

fun discharge p pq = Thm.implies_elim pq p



(* a faster COMP *)

type compose_data = cterm list * (cterm -> cterm list) * thm

fun list2 (x, y) = [x, y]

fun precompose f rule = (f (Thm.cprem_of rule 1), f, rule)
fun precompose2 f rule = precompose (list2 o f) rule

fun compose (cvs, f, rule) thm =
  discharge thm (Thm.instantiate ([], cvs ~~ f (Thm.cprop_of thm)) rule)



(* simpset *)

local
  val antisym_le1 = mk_meta_eq @{thm order_class.antisym_conv}
  val antisym_le2 = mk_meta_eq @{thm linorder_class.antisym_conv2}
  val antisym_less1 = mk_meta_eq @{thm linorder_class.antisym_conv1}
  val antisym_less2 = mk_meta_eq @{thm linorder_class.antisym_conv3}

  fun eq_prop t thm = HOLogic.mk_Trueprop t aconv Thm.prop_of thm
  fun dest_binop ((c as Const _) $ t $ u) = (c, t, u)
    | dest_binop t = raise TERM ("dest_binop", [t])

  fun prove_antisym_le ctxt t =
    let
      val (le, r, s) = dest_binop t
      val less = Const (@{const_name less}, Term.fastype_of le)
      val prems = Simplifier.prems_of ctxt
    in
      (case find_first (eq_prop (le $ s $ r)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ r $ s))) prems
          |> Option.map (fn thm => thm RS antisym_less1)
      | SOME thm => SOME (thm RS antisym_le1))
    end
    handle THM _ => NONE

  fun prove_antisym_less ctxt t =
    let
      val (less, r, s) = dest_binop (HOLogic.dest_not t)
      val le = Const (@{const_name less_eq}, Term.fastype_of less)
      val prems = Simplifier.prems_of ctxt
    in
      (case find_first (eq_prop (le $ r $ s)) prems of
        NONE =>
          find_first (eq_prop (HOLogic.mk_not (less $ s $ r))) prems
          |> Option.map (fn thm => thm RS antisym_less2)
      | SOME thm => SOME (thm RS antisym_le2))
  end
  handle THM _ => NONE

  val basic_simpset =
    simpset_of (put_simpset HOL_ss @{context}
      addsimps @{thms field_simps times_divide_eq_right times_divide_eq_left arith_special
        arith_simps rel_simps array_rules z3div_def z3mod_def}
      addsimprocs [@{simproc binary_int_div}, @{simproc binary_int_mod},
        Simplifier.simproc_global @{theory} "fast_int_arith" [
          "(m::int) < n", "(m::int) <= n", "(m::int) = n"] Lin_Arith.simproc,
        Simplifier.simproc_global @{theory} "antisym_le" ["(x::'a::order) <= y"] prove_antisym_le,
        Simplifier.simproc_global @{theory} "antisym_less" ["~ (x::'a::linorder) < y"]
          prove_antisym_less])

  structure Simpset = Generic_Data
  (
    type T = simpset
    val empty = basic_simpset
    val extend = I
    val merge = Simplifier.merge_ss
  )
in

fun add_simproc simproc context =
  Simpset.map (simpset_map (Context.proof_of context)
    (fn ctxt => ctxt addsimprocs [simproc])) context

fun make_simpset ctxt rules =
  simpset_of (put_simpset (Simpset.get (Context.Proof ctxt)) ctxt addsimps rules)

end

end
