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
  val complete_instances: bool Config.T
  val verbose: bool Config.T

  (* monomorphization *)
  val monomorph: (term -> typ list Symtab.table) -> (int * thm) list ->
    Proof.context -> (int * thm) list list * Proof.context
end

structure Monomorph: MONOMORPH =
struct

(* utility functions *)

fun fold_env _ [] y = y
  | fold_env f (x :: xs) y = fold_env f xs (f xs x y)

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
val complete_instances =
  Attrib.setup_config_bool @{binding monomorph_complete_instances} (K true)
val verbose = Attrib.setup_config_bool @{binding monomorph_verbose} (K true)

fun show_info ctxt msg = if Config.get ctxt verbose then tracing msg else ()



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
    val empty_subst = ((0, false, false), Vartab.empty)

    fun prep (r, thm) ((i, idx), (consts, substs)) =
      if not (Term.exists_type typ_has_tvars (Thm.prop_of thm)) then
        (Ground thm, ((i+1, idx + Thm.maxidx_of thm + 1), (consts, substs)))
      else
        let
          (* increase indices to avoid clashes of type variables *)
          val thm' = Thm.incr_indexes idx thm
          val idx' = Thm.maxidx_of thm' + 1
          val schematics = schematic_consts_of (Thm.prop_of thm')
          val consts' =
            Symtab.fold (fn (n, _) => Symtab.update (n, [])) schematics consts
          val substs' = Inttab.update (i, [empty_subst]) substs
          val thm_info = Schematic {
            index = i,
            theorem = thm',
            tvars = Term.add_tvars (Thm.prop_of thm') [],
            schematics = schematics,
            initial_round = r }
      in (thm_info, ((i+1, idx'), (consts', substs'))) end
  in fold_map prep rthms ((0, 0), (Symtab.empty, Inttab.empty)) ||> snd end



(** collecting substitutions **)

fun add_relevant_instances known_grounds (Const (c as (n, T))) =
      if typ_has_tvars T orelse not (Symtab.defined known_grounds n) then I
      else if member (op =) (Symtab.lookup_list known_grounds n) T then I
      else Symtab.insert_list (op =) c
  | add_relevant_instances _ _ = I

fun collect_instances known_grounds thm =
  Term.fold_aterms (add_relevant_instances known_grounds) (Thm.prop_of thm)


fun exceeded_limit (limit, _, _) = (limit <= 0)

fun with_substs index f (limit, substitutions, next_grounds) =
  let
    val substs = Inttab.lookup_list substitutions index
    val (limit', substs', next_grounds') = f (limit, substs, next_grounds)
  in (limit', Inttab.update (index, substs') substitutions, next_grounds') end

fun with_grounds grounds f cx =
  if exceeded_limit cx then cx else Symtab.fold f grounds cx

fun with_all_combinations schematics f (n, Ts) cx =
  if exceeded_limit cx then cx
  else fold_product f (Symtab.lookup_list schematics n) Ts cx

fun with_partial_substs f T U (cx as (limit, substs, next_grounds)) =
  if exceeded_limit cx then cx
  else fold_env (f (T, U)) substs (limit, [], next_grounds)


fun same_subst subst =
  Vartab.forall (fn (n, (_, T)) => 
    Vartab.lookup subst n |> Option.map (equal T o snd) |> the_default false)

(* FIXME: necessary? would it have an impact?
   comparing substitutions can be tricky ... *)
fun known substs1 substs2 subst = false

fun refine ctxt known_grounds new_grounds info =
  let
    val thy = Proof_Context.theory_of ctxt
    val count_partial = Config.get ctxt complete_instances
    val (round, index, _, tvars, schematics) = info

    fun refine_subst TU = try (Sign.typ_match thy TU)

    fun add_new_ground subst n T =
      let val T' = Envir.subst_type subst T
      in
        (* FIXME: maybe keep types in a table or net for known_grounds,
           that might improve efficiency here
        *)
        if member (op =) (Symtab.lookup_list known_grounds n) T' then I
        else Symtab.cons_list (n, T')
      end

    fun refine_step subst limit next_grounds substs =
      let
        val full = forall (Vartab.defined subst o fst) tvars
        val limit' =
          if full orelse count_partial then limit - 1 else limit
        val sub = ((round, full, false), subst)
        val next_grounds' =
          (schematics, next_grounds)
          |-> Symtab.fold (uncurry (fold o add_new_ground subst))
      in (limit', sub :: substs, next_grounds') end

    fun refine_substs TU substs sub (cx as (limit, substs', next_grounds)) =
      let val ((generation, full, _), subst) = sub
      in
        if exceeded_limit cx orelse full then
          (limit, sub :: substs', next_grounds)
        else
          (case refine_subst TU subst of
            NONE => (limit, sub :: substs', next_grounds)
          | SOME subst' =>
              if (same_subst subst orf known substs substs') subst' then
                (limit, sub :: substs', next_grounds)
              else
                substs'
                |> cons ((generation, full, true), subst)
                |> refine_step subst' limit next_grounds)
      end
  in
    with_substs index (
      with_grounds new_grounds (with_all_combinations schematics (
        with_partial_substs refine_substs)))
  end


fun make_subst_ctxt ctxt thm_infos known_grounds substitutions =
  let
    val limit = Config.get ctxt max_new_instances

    fun add_ground_consts (Ground thm) = collect_instances known_grounds thm
      | add_ground_consts (Schematic _) = I
    val initial_grounds = fold add_ground_consts thm_infos Symtab.empty
  in (known_grounds, (limit, substitutions, initial_grounds)) end

fun with_new round f thm_info =
  (case thm_info of
    Schematic {index, theorem, tvars, schematics, initial_round} =>
      if initial_round <> round then I
      else f (round, index, theorem, tvars, schematics)
  | Ground _ => I)

fun with_active round f thm_info =
  (case thm_info of
    Schematic {index, theorem, tvars, schematics, initial_round} =>
      if initial_round < round then I
      else f (round, index, theorem, tvars, schematics)
  | Ground _ => I)

fun collect_substitutions thm_infos ctxt round (known_grounds, subst_ctxt) =
  let val (limit, substitutions, next_grounds) = subst_ctxt
  in
    (*
      'known_grounds' are all constant names known to occur schematically
      associated with all ground instances considered so far
    *)
    if exceeded_limit subst_ctxt then (true, (known_grounds, subst_ctxt))
    else
      let
        fun collect (_, _, thm, _, _) = collect_instances known_grounds thm
        val new = fold (with_new round collect) thm_infos next_grounds
        val known' = Symtab.merge_list (op =) (known_grounds, new)
      in
        if Symtab.is_empty new then (true, (known_grounds, subst_ctxt))
        else
          (limit, substitutions, Symtab.empty)
          |> fold (with_active round (refine ctxt known_grounds new)) thm_infos
          |> fold (with_new round (refine ctxt Symtab.empty known')) thm_infos
          |> pair false o pair known'
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

fun instantiate_all' (mT, ctxt) substitutions thm_infos =
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
          Inttab.lookup_list substitutions index
          |> map_filter (with_subst tvars (instantiate theorem))
  in (map inst thm_infos, ctxt) end

fun instantiate_all ctxt thm_infos (_, (_, substitutions, _)) =
  if Config.get ctxt complete_instances then
    let
      fun refined ((_, _, true), _) = true
        | refined _ = false
    in
      (Inttab.map (K (filter_out refined)) substitutions, thm_infos)
      |-> instantiate_all' (new_super_type ctxt thm_infos)
    end
  else instantiate_all' (NONE, ctxt) substitutions thm_infos



(** overall procedure **)

fun limit_rounds ctxt f =
  let
    val max = Config.get ctxt max_rounds

    fun round _ (true, x) = x
      | round i (_, x) =
          if i <= max then round (i + 1) (f ctxt i x)
          else (
            show_info ctxt "Warning: Monomorphization limit reached";
            x)
  in round 1 o pair false end

fun monomorph schematic_consts_of rthms ctxt =
  let
    val (thm_infos, (known_grounds, substitutions)) =
      prepare schematic_consts_of rthms
  in
    if Symtab.is_empty known_grounds then
      (map (single o pair 0 o snd) rthms, ctxt)
    else
      make_subst_ctxt ctxt thm_infos known_grounds substitutions
      |> limit_rounds ctxt (collect_substitutions thm_infos)
      |> instantiate_all ctxt thm_infos
  end


end

