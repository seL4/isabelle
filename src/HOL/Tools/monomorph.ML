(*  Title:      HOL/Tools/monomorph.ML
    Author:     Sascha Boehme, TU Muenchen

Monomorphization of theorems, i.e., computation of ground instances for
theorems with type variables.  This procedure is incomplete in general,
but works well for most practical problems.

Monomorphization is essentially an enumeration of substitutions that map
schematic types to ground types. Applying these substitutions to theorems
with type variables results in monomorphized ground instances. The
enumeration is driven by schematic constants (constants occurring with
type variables) and all ground instances of such constants (occurrences
without type variables). The enumeration is organized in rounds in which
all substitutions for the schematic constants are computed that are induced
by the ground instances. Any new ground instance may induce further
substitutions in a subsequent round. To prevent nontermination, there is
an upper limit of rounds involved and of the number of monomorphized ground
instances computed.

Theorems to be monomorphized must be tagged with a number indicating the
initial round in which they participate first. The initial round is
ignored for theorems without type variables. For any other theorem, the
initial round must be greater than zero. Returned monomorphized theorems
carry a number showing from which monomorphization round they emerged.
*)

signature MONOMORPH =
sig
  (* utility functions *)
  val typ_has_tvars: typ -> bool
  val all_schematic_consts_of: term -> typ list Symtab.table
  val add_schematic_consts_of: term -> typ list Symtab.table ->
    typ list Symtab.table

  (* configuration options *)
  val max_rounds: int Config.T
  val max_new_instances: int Config.T
  val max_thm_instances: int Config.T
  val max_new_const_instances_per_round: int Config.T
  val max_duplicated_instances: int Config.T

  (* monomorphization *)
  val monomorph: (term -> typ list Symtab.table) -> Proof.context ->
    (int * thm) list -> (int * thm) list list
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

fun clear_grounds grounds = Symtab.map (K (K [])) grounds


(* configuration options *)

val max_rounds = Attrib.setup_config_int \<^binding>\<open>monomorph_max_rounds\<close> (K 5)

val max_new_instances =
  Attrib.setup_config_int \<^binding>\<open>monomorph_max_new_instances\<close> (K 500)

val max_thm_instances =
  Attrib.setup_config_int \<^binding>\<open>monomorph_max_thm_instances\<close> (K 20)

val max_new_const_instances_per_round =
  Attrib.setup_config_int \<^binding>\<open>monomorph_max_new_const_instances_per_round\<close> (K 5)

val max_duplicated_instances =
  Attrib.setup_config_int \<^binding>\<open>monomorph_max_duplicated_instances\<close> (K 16000)

fun limit_rounds ctxt f =
  let
    val max = Config.get ctxt max_rounds
    fun round i x = if i > max then x else round (i + 1) (f ctxt i x)
  in round 1 end


(* theorem information and related functions *)

datatype thm_info =
  Ground of thm |
  Ignored |
  Schematic of {
    id: int,
    theorem: thm,
    tvars: (indexname * sort) list,
    schematics: (string * typ) list,
    initial_round: int}

fun fold_grounds f = fold (fn Ground thm => f thm | _ => I)

fun fold_schematic f thm_info =
  (case thm_info of
    Schematic {id, theorem, tvars, schematics, initial_round} =>
      f id theorem tvars schematics initial_round
  | _ => I)

fun fold_schematics pred f =
  let
    fun apply id thm tvars schematics initial_round x =
      if pred initial_round then f id thm tvars schematics x else x
  in fold (fold_schematic apply) end


(* collecting data *)

(*
  Theorems with type variables that cannot be instantiated should be ignored.
  A type variable has only a chance to be instantiated if it occurs in the
  type of one of the schematic constants.
*)
fun groundable all_tvars schematics =
  let val tvars' = Symtab.fold (fold Term.add_tvarsT o snd) schematics []
  in forall (member (op =) tvars') all_tvars end


fun prepare schematic_consts_of rthms =
  let
    fun prep (initial_round, thm) ((id, idx), consts) =
      if Term.exists_type typ_has_tvars (Thm.prop_of thm) then
        let
          (* increase indices to avoid clashes of type variables *)
          val thm' = Thm.incr_indexes idx thm
          val idx' = Thm.maxidx_of thm' + 1

          val tvars = Term.add_tvars (Thm.prop_of thm') []
          val schematics = schematic_consts_of (Thm.prop_of thm')
          val schematics' =
            Symtab.fold (fn (n, Ts) => fold (cons o pair n) Ts) schematics []

          (* collect the names of all constants that need to be instantiated *)
          val consts' =
            consts
            |> Symtab.fold (fn (n, _) => Symtab.update (n, [])) schematics

          val thm_info =
            if not (groundable tvars schematics) then Ignored
            else
              Schematic {
                id = id,
                theorem = thm',
                tvars = tvars,
                schematics = schematics',
                initial_round = initial_round}
        in (thm_info, ((id + 1, idx'), consts')) end
      else (Ground thm, ((id + 1, idx + Thm.maxidx_of thm + 1), consts))
  in
    fold_map prep rthms ((0, 0), Symtab.empty) ||> snd
  end


(* collecting instances *)

fun instantiate ctxt subst =
  let
    fun cert (ix, (S, T)) = ((ix, S), Thm.ctyp_of ctxt T)
    fun cert' subst = Vartab.fold (cons o cert) subst []
  in Thm.instantiate (TVars.make (cert' subst), Vars.empty) end

fun add_new_grounds used_grounds new_grounds thm =
  let
    fun mem tab (n, T) = member (op =) (Symtab.lookup_list tab n) T
    fun add (Const (c as (n, _))) =
          if mem used_grounds c orelse mem new_grounds c then I
          else if not (Symtab.defined used_grounds n) then I
          else Symtab.insert_list (op =) c
      | add _ = I
  in Term.fold_aterms add (Thm.prop_of thm) end

fun add_insts max_instances max_duplicated_instances max_thm_insts ctxt round used_grounds
    new_grounds id thm tvars schematics cx =
  let
    exception ENOUGH of
      typ list Symtab.table * (int * int * ((int * (sort * typ) Vartab.table) * thm) list Inttab.table)

    val thy = Proof_Context.theory_of ctxt

    fun add subst (cx as (next_grounds, (hits, misses, insts))) =
      if hits >= max_instances orelse misses >= max_duplicated_instances then
        raise ENOUGH cx
      else
        let
          val thm' = instantiate ctxt subst thm
          val rthm = ((round, subst), thm')
          val rthms = Inttab.lookup_list insts id
          val n_insts' =
            if member (eq_snd Thm.eq_thm) rthms rthm then
              (hits, misses + 1, insts)
            else
              let
                val (hits', misses') =
                  if length rthms >= max_thm_insts then (hits, misses + 1) else (hits + 1, misses)
              in
                (hits', misses', Inttab.cons_list (id, rthm) insts)
              end
          val next_grounds' =
            add_new_grounds used_grounds new_grounds thm' next_grounds
        in (next_grounds', n_insts') end

    fun with_grounds (n, T) f subst (n', Us) =
      let
        fun matching U = (* one-step refinement of the given substitution *)
          (case try (Sign.typ_match thy (T, U)) subst of
            NONE => I
          | SOME subst' => f subst')
      in if n = n' then fold matching Us else I end

    fun with_matching_ground c subst f =
      (* Try new grounds before already used grounds. Otherwise only
         substitutions already seen in previous rounds get enumerated. *)
      Symtab.fold (with_grounds c (f true) subst) new_grounds #>
      Symtab.fold (with_grounds c (f false) subst) used_grounds

    fun is_complete subst =
      (* Check if a substitution is defined for all TVars of the theorem,
         which guarantees that the instantiation with this substitution results
         in a ground theorem since all matchings that led to this substitution
         are with ground types only. *)
      subset (op =) (tvars, Vartab.fold (cons o apsnd fst) subst [])

    fun for_schematics _ [] _ = I
      | for_schematics used_new (c :: cs) subst =
          with_matching_ground c subst (fn new => fn subst' =>
            if is_complete subst' then
              if used_new orelse new then add subst'
              else I
            else for_schematics (used_new orelse new) cs subst') #>
          for_schematics used_new cs subst
  in
    (* Enumerate all substitutions that lead to a ground instance of the
       theorem not seen before. A necessary condition for such a new ground
       instance is the usage of at least one ground from the new_grounds
       table. The approach used here is to match all schematics of the theorem
       with all relevant grounds. *)
    for_schematics false schematics Vartab.empty cx
    handle ENOUGH cx' => cx'
  end

fun is_new round initial_round = (round = initial_round)
fun is_active round initial_round = (round > initial_round)

fun find_instances max_instances max_duplicated_instances max_thm_insts max_new_grounds thm_infos
    ctxt round (known_grounds, new_grounds0, insts) =
  let
    val new_grounds =
      Symtab.map (fn _ => fn grounds =>
        if length grounds <= max_new_grounds then grounds
        else take max_new_grounds (sort Term_Ord.typ_ord grounds)) new_grounds0

    val add_new = add_insts max_instances max_duplicated_instances max_thm_insts ctxt round
    fun consider_all pred f (cx as (_, (hits, misses, _))) =
      if hits >= max_instances orelse misses >= max_duplicated_instances then
        cx
      else
        fold_schematics pred f thm_infos cx

    val known_grounds' = Symtab.merge_list (op =) (known_grounds, new_grounds)
    val empty_grounds = clear_grounds known_grounds'

    val (new_grounds', insts') =
      (Symtab.empty, insts)
      |> consider_all (is_active round) (add_new known_grounds new_grounds)
      |> consider_all (is_new round) (add_new empty_grounds known_grounds')
  in
    (known_grounds', new_grounds', insts')
  end

fun add_ground_types thm =
  let fun add (n, T) = Symtab.map_entry n (insert (op =) T)
  in Term.fold_aterms (fn Const c => add c | _ => I) (Thm.prop_of thm) end

fun collect_instances ctxt max_thm_insts max_new_grounds thm_infos consts =
  let
    val known_grounds = fold_grounds add_ground_types thm_infos consts
    val empty_grounds = clear_grounds known_grounds
    val max_instances = Config.get ctxt max_new_instances
      |> fold (fn Schematic _ => Integer.add 1 | _ => I) thm_infos
    val max_duplicated_instances = Config.get ctxt max_duplicated_instances
    val (_, _, (_, _, insts)) =
      limit_rounds ctxt (find_instances max_instances max_duplicated_instances max_thm_insts
      max_new_grounds thm_infos) (empty_grounds, known_grounds, (0, 0, Inttab.empty))
  in
    insts
  end


(* monomorphization *)

fun size_of_subst subst =
  Vartab.fold (Integer.add o size_of_typ o snd o snd) subst 0

fun subst_ord subst = int_ord (apply2 size_of_subst subst)

fun instantiated_thms _ _ (Ground thm) = [(0, thm)]
  | instantiated_thms _ _ Ignored = []
  | instantiated_thms max_thm_insts insts (Schematic {id, ...}) =
    Inttab.lookup_list insts id
    |> (fn rthms =>
      if length rthms <= max_thm_insts then rthms
      else take max_thm_insts (sort (prod_ord int_ord subst_ord o apply2 fst) rthms))
    |> map (apfst fst)

fun monomorph schematic_consts_of ctxt rthms =
  let
    val max_thm_insts = Config.get ctxt max_thm_instances
    val max_new_grounds = Config.get ctxt max_new_const_instances_per_round
    val (thm_infos, consts) = prepare schematic_consts_of rthms
    val insts =
      if Symtab.is_empty consts then Inttab.empty
      else collect_instances ctxt max_thm_insts max_new_grounds thm_infos consts
  in map (instantiated_thms max_thm_insts insts) thm_infos end

end
