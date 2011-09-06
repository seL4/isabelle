(*  Title:      HOL/Tools/monomorph.ML
    Author:     Sascha Boehme, TU Muenchen

Monomorphization of theorems, i.e., computation of all (necessary)
instances.  This procedure is incomplete in general, but works well for
most practical problems.

For a list of universally closed theorems (without schematic term
variables), monomorphization computes a list of theorems with schematic
term variables: all polymorphic constants (i.e., constants occurring both
with ground types and schematic type variables) are instantiated with all
(necessary) ground types; thereby theorems containing these constants are
copied.  To prevent nontermination, there is an upper limit for the number
of iterations involved in the fixpoint construction.

The search for instances is performed on the constants with schematic
types, which are extracted from the initial set of theorems.  The search
constructs, for each theorem with those constants, a set of substitutions,
which, in the end, is applied to all corresponding theorems.  Remaining
schematic type variables are substituted with fresh types.

Searching for necessary substitutions is an iterative fixpoint
construction: each iteration computes all required instances required by
the ground instances computed in the previous step and which haven't been
found before.  Computed substitutions are always nontrivial: schematic type
variables are never mapped to schematic type variables.
*)

signature MONOMORPH =
sig
  (* utility function *)
  val typ_has_tvars: typ -> bool
  val all_schematic_consts_of: term -> typ list Symtab.table
  val add_schematic_consts_of: term -> typ list Symtab.table ->
    typ list Symtab.table

  (* configuration options *)
  val max_rounds: int Config.T
  val max_new_instances: int Config.T
  val keep_partial_instances: bool Config.T

  (* monomorphization *)
  val monomorph: (term -> typ list Symtab.table) -> (int * thm) list ->
    Proof.context -> (int * thm) list list * Proof.context
end

structure Monomorph: MONOMORPH =
struct

(* utility functions *)

val typ_has_tvars = Term.exists_subtype (fn TVar _ => true | _ => false)

fun add_schematic_const (c as (_, T)) =
  if typ_has_tvars T then Symtab.insert_list (op =) c else I

fun add_schematic_consts_of t =
  Term.fold_aterms (fn Const c => add_schematic_const c | _ => I) t

fun all_schematic_consts_of t = add_schematic_consts_of t Symtab.empty



(* configuration options *)

val max_rounds = Attrib.setup_config_int @{binding monomorph_max_rounds} (K 5)
val max_new_instances =
  Attrib.setup_config_int @{binding monomorph_max_new_instances} (K 300)
val keep_partial_instances =
  Attrib.setup_config_bool @{binding monomorph_keep_partial_instances} (K true)



(* monomorphization *)

(** preparing the problem **)

datatype thm_info =
  Ground of thm |
  Schematic of {
    index: int,
    theorem: thm,
    tvars: (indexname * sort) list,
    schematics: typ list Symtab.table,
    initial_round: int }

fun prepare schematic_consts_of rthms =
  let
    val empty_sub = ((0, false, false), Vartab.empty)

    fun prep (r, thm) ((i, idx), (consts, subs)) =
      if not (Term.exists_type typ_has_tvars (Thm.prop_of thm)) then
        (Ground thm, ((i+1, idx + Thm.maxidx_of thm + 1), (consts, subs)))
      else
        let
          (* increase indices to avoid clashes of type variables *)
          val thm' = Thm.incr_indexes idx thm
          val idx' = Thm.maxidx_of thm' + 1
          val schematics = schematic_consts_of (Thm.prop_of thm')
          val consts' =
            Symtab.fold (fn (n, _) => Symtab.update (n, [])) schematics consts
          val subs' = Inttab.update (i, [empty_sub]) subs
          val thm_info = Schematic {
            index = i,
            theorem = thm',
            tvars = Term.add_tvars (Thm.prop_of thm') [],
            schematics = schematics,
            initial_round = r }
      in (thm_info, ((i+1, idx'), (consts', subs'))) end
  in fold_map prep rthms ((0, 0), (Symtab.empty, Inttab.empty)) ||> snd end



(** collecting substitutions **)

fun exceeded limit = (limit <= 0)
fun exceeded_limit (limit, _, _) = exceeded limit


fun derived_subst subst' subst = subst' |> Vartab.forall (fn (n, (_, T)) => 
  Vartab.lookup subst n |> Option.map (equal T o snd) |> the_default false)

fun eq_subst (subst1, subst2) =
  derived_subst subst1 subst2 andalso derived_subst subst2 subst1


fun with_all_grounds cx grounds f =
  if exceeded_limit cx then I else Symtab.fold f grounds

fun with_all_type_combinations cx schematics f (n, Ts) =
  if exceeded_limit cx then I
  else fold_product f (Symtab.lookup_list schematics n) Ts

fun derive_new_substs thy cx new_grounds schematics subst =
  with_all_grounds cx new_grounds
    (with_all_type_combinations cx schematics (fn T => fn U =>
      (case try (Sign.typ_match thy (T, U)) subst of
        NONE => I
      | SOME subst' => insert eq_subst subst'))) []


fun known_subst sub subs1 subs2 subst' =
  let fun derived (_, subst) = derived_subst subst' subst
  in derived sub orelse exists derived subs1 orelse exists derived subs2 end

fun within_limit f cx = if exceeded_limit cx then cx else f cx

fun fold_partial_substs derive add = within_limit (
  let
    fun fold_partial [] cx = cx
      | fold_partial (sub :: subs) (limit, subs', next) =
          if exceeded limit then (limit, sub :: subs @ subs', next)
          else sub |> (fn ((generation, full, _), subst) =>
            if full then fold_partial subs (limit, sub :: subs', next)
            else
              (case filter_out (known_subst sub subs subs') (derive subst) of
                [] => fold_partial subs (limit, sub :: subs', next)
              | substs =>
                  (limit, ((generation, full, true), subst) :: subs', next)
                  |> fold (within_limit o add) substs
                  |> fold_partial subs))
  in (fn (limit, subs, next) => fold_partial subs (limit, [], next)) end)


fun refine ctxt round known_grounds new_grounds (tvars, schematics) cx =
  let
    val thy = Proof_Context.theory_of ctxt
    val count_partial = Config.get ctxt keep_partial_instances

    fun add_new_ground subst n T =
      let val T' = Envir.subst_type subst T
      in
        (* FIXME: maybe keep types in a table or net for known_grounds,
           that might improve efficiency here
        *)
        if typ_has_tvars T' then I
        else if member (op =) (Symtab.lookup_list known_grounds n) T' then I
        else Symtab.cons_list (n, T')
      end

    fun add_new_subst subst (limit, subs, next_grounds) =
      let
        val full = forall (Vartab.defined subst o fst) tvars
        val limit' =
          if full orelse count_partial then limit - 1 else limit
        val sub = ((round, full, false), subst)
        val next_grounds' =
          (schematics, next_grounds)
          |-> Symtab.fold (uncurry (fold o add_new_ground subst))
      in (limit', sub :: subs, next_grounds') end
  in
    fold_partial_substs (derive_new_substs thy cx new_grounds schematics)
      add_new_subst cx
  end


(*
  'known_grounds' are all constant names known to occur schematically
  associated with all ground instances considered so far
*)
fun add_relevant_instances known_grounds (Const (c as (n, T))) =
      if typ_has_tvars T orelse not (Symtab.defined known_grounds n) then I
      else if member (op =) (Symtab.lookup_list known_grounds n) T then I
      else Symtab.insert_list (op =) c
  | add_relevant_instances _ _ = I

fun collect_instances known_grounds thm =
  Term.fold_aterms (add_relevant_instances known_grounds) (Thm.prop_of thm)


fun make_subst_ctxt ctxt thm_infos known_grounds substitutions =
  let
    (* The total limit of returned (ground) facts is the number of facts
       given to the monomorphizer increased by max_new_instances.  Since
       initially ground facts are returned anyway, the limit here is not
       counting them. *)
    val limit = Config.get ctxt max_new_instances + 
      fold (fn Schematic _ => Integer.add 1 | _ => I) thm_infos 0

    fun add_ground_consts (Ground thm) = collect_instances known_grounds thm
      | add_ground_consts (Schematic _) = I
    val initial_grounds = fold add_ground_consts thm_infos Symtab.empty
  in (known_grounds, (limit, substitutions, initial_grounds)) end

fun is_new round initial_round = (round = initial_round)
fun is_active round initial_round = (round > initial_round)

fun fold_schematic pred f = fold (fn
    Schematic {index, theorem, tvars, schematics, initial_round} =>
      if pred initial_round then f theorem (index, tvars, schematics) else I
  | Ground _ => I)

fun focus f _ (index, tvars, schematics) (limit, subs, next_grounds) =
  let
    val (limit', isubs', next_grounds') =
      (limit, Inttab.lookup_list subs index, next_grounds)
      |> f (tvars, schematics)
  in (limit', Inttab.update (index, isubs') subs, next_grounds') end

fun collect_substitutions thm_infos ctxt round subst_ctxt =
  let val (known_grounds, (limit, subs, next_grounds)) = subst_ctxt
  in
    if exceeded limit then subst_ctxt
    else
      let
        fun collect thm _ = collect_instances known_grounds thm
        val new = fold_schematic (is_new round) collect thm_infos next_grounds

        val known' = Symtab.merge_list (op =) (known_grounds, new)
        val step = focus o refine ctxt round known'
      in
        (limit, subs, Symtab.empty)
        |> not (Symtab.is_empty new) ?
            fold_schematic (is_active round) (step new) thm_infos
        |> fold_schematic (is_new round) (step known') thm_infos
        |> pair known'
      end
  end



(** instantiating schematic theorems **)

fun super_sort (Ground _) S = S
  | super_sort (Schematic {tvars, ...}) S = merge (op =) (S, maps snd tvars)

fun new_super_type ctxt thm_infos =
  let val S = fold super_sort thm_infos @{sort type}
  in yield_singleton Variable.invent_types S ctxt |>> SOME o TFree end

fun add_missing_tvar T (ix, S) subst =
  if Vartab.defined subst ix then subst
  else Vartab.update (ix, (S, T)) subst

fun complete tvars subst T =
  subst
  |> Vartab.map (K (apsnd (Term.map_atyps (fn TVar _ => T | U => U))))
  |> fold (add_missing_tvar T) tvars

fun instantiate_all' (mT, ctxt) subs thm_infos =
  let
    val thy = Proof_Context.theory_of ctxt

    fun cert (ix, (S, T)) = pairself (Thm.ctyp_of thy) (TVar (ix, S), T)
    fun cert' subst = Vartab.fold (cons o cert) subst []
    fun instantiate thm subst = Thm.instantiate (cert' subst, []) thm

    fun with_subst tvars f ((generation, full, _), subst) =
      if full then SOME (generation, f subst)
      else Option.map (pair generation o f o complete tvars subst) mT

    fun inst (Ground thm) = [(0, thm)]
      | inst (Schematic {theorem, tvars, index, ...}) =
          Inttab.lookup_list subs index
          |> map_filter (with_subst tvars (instantiate theorem))
  in (map inst thm_infos, ctxt) end

fun instantiate_all ctxt thm_infos (_, (_, subs, _)) =
  if Config.get ctxt keep_partial_instances then
    let fun is_refined ((_, _, refined), _) = refined
    in
      (Inttab.map (K (filter_out is_refined)) subs, thm_infos)
      |-> instantiate_all' (new_super_type ctxt thm_infos)
    end
  else instantiate_all' (NONE, ctxt) subs thm_infos



(** overall procedure **)

fun limit_rounds ctxt f =
  let
    val max = Config.get ctxt max_rounds
    fun round i x = if i > max then x else round (i + 1) (f ctxt i x)
  in round 1 end

fun monomorph schematic_consts_of rthms ctxt =
  let
    val (thm_infos, (known_grounds, subs)) = prepare schematic_consts_of rthms
  in
    if Symtab.is_empty known_grounds then
      (map (fn Ground thm => [(0, thm)] | _ => []) thm_infos, ctxt)
    else
      make_subst_ctxt ctxt thm_infos known_grounds subs
      |> limit_rounds ctxt (collect_substitutions thm_infos)
      |> instantiate_all ctxt thm_infos
  end


end

