(*  Title:      HOL/Tools/SMT/smt_monomorph.ML
    Author:     Sascha Boehme, TU Muenchen

Monomorphization of theorems, i.e., computation of all (necessary)
instances.  This procedure is incomplete in general, but works well for
most practical problems.

For a list of universally closed theorems (without schematic term
variables), monomorphization computes a list of theorems with schematic
term variables: all polymorphic constants (i.e., constants occurring both
with ground types and schematic type variables) are instantiated with all
(necessary) ground types; thereby theorems containing these constants are
copied.  To prevent non-termination, there is an upper limit for the number
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

signature SMT_MONOMORPH =
sig
  val monomorph: (int * thm) list -> Proof.context ->
    (int * thm) list * Proof.context
end

structure SMT_Monomorph: SMT_MONOMORPH =
struct

(* utility functions *)

val typ_has_tvars = Term.exists_subtype (fn TVar _ => true | _ => false)

val ignored = member (op =) [@{const_name All}, @{const_name Ex},
  @{const_name Let}, @{const_name If}, @{const_name HOL.eq}]

fun is_const pred (n, T) = not (ignored n) andalso pred T

fun collect_consts_if pred f =
  Thm.prop_of #>
  Term.fold_aterms (fn Const c => if is_const pred c then f c else I | _ => I)

val insert_const = Ord_List.insert (prod_ord fast_string_ord Term_Ord.typ_ord)

fun tvar_consts_of thm = collect_consts_if typ_has_tvars insert_const thm []

fun add_const_types pred =
  collect_consts_if pred (fn (n, T) => Symtab.map_entry n (insert (op =) T))

fun incr_indexes ithms =
  let
    fun inc (i, thm) idx =
      ((i, Thm.incr_indexes idx thm), Thm.maxidx_of thm + idx + 1)
  in fst (fold_map inc ithms 0) end



(* search for necessary substitutions *)

fun new_substitutions thy grounds (n, T) subst =
  if not (typ_has_tvars T) then [subst]
  else
    Symtab.lookup_list grounds n
    |> map_filter (try (fn U => Sign.typ_match thy (T, U) subst))
    |> cons subst

fun apply_subst grounds consts subst =
  let
    fun is_new_ground (n, T) = not (typ_has_tvars T) andalso
      not (member (op =) (Symtab.lookup_list grounds n) T)

    fun apply_const (n, T) new_grounds =
      let val c = (n, Envir.subst_type subst T)
      in
        new_grounds
        |> is_new_ground c ? Symtab.insert_list (op =) c
        |> pair c
      end
  in fold_map apply_const consts #>> pair subst end

fun specialize thy all_grounds new_grounds scs =
  let
    fun spec (subst, consts) next_grounds =
      [subst]
      |> fold (maps o new_substitutions thy new_grounds) consts
      |> rpair next_grounds
      |-> fold_map (apply_subst all_grounds consts)
  in
    fold_map spec scs #>> (fn scss =>
    fold (fold (insert (eq_snd (op =)))) scss [])
  end

val limit_reached_warning = "Warning: Monomorphization limit reached"

fun search_substitutions ctxt limit all_grounds new_grounds scss =
  let
    val thy = ProofContext.theory_of ctxt
    val all_grounds' = Symtab.merge_list (op =) (all_grounds, new_grounds)
    val spec = specialize thy all_grounds' new_grounds
    val (scss', new_grounds') = fold_map spec scss Symtab.empty
  in
    if Symtab.is_empty new_grounds' then scss'
    else if limit > 0 then
      search_substitutions ctxt (limit-1) all_grounds' new_grounds' scss'
    else (SMT_Config.verbose_msg ctxt (K limit_reached_warning) (); scss')
  end



(* instantiation *)

fun filter_most_specific thy =
  let
    fun typ_match (_, T) (_, U) = Sign.typ_match thy (T, U)

    fun is_trivial subst = Vartab.is_empty subst orelse
      forall (fn (v, (S, T)) => TVar (v, S) = T) (Vartab.dest subst)

    fun match general specific =
      (case try (fold2 typ_match general specific) Vartab.empty of
        NONE => false
      | SOME subst => not (is_trivial subst))

    fun most_specific _ [] = []
      | most_specific css ((ss, cs) :: scs) =
          let val substs = most_specific (cs :: css) scs
          in
            if exists (match cs) css orelse exists (match cs o snd) scs
            then substs else ss :: substs
          end

  in most_specific [] end

fun instantiate (i, thm) substs (ithms, ctxt) =
  let
    val (vs, Ss) = split_list (Term.add_tvars (Thm.prop_of thm) [])
    val (Tenv, ctxt') =
      ctxt
      |> Variable.invent_types Ss
      |>> map2 (fn v => fn (n, S) => (v, (S, TFree (n, S)))) vs

    val thy = ProofContext.theory_of ctxt'

    fun replace (v, (_, T)) (U as TVar (u, _)) = if u = v then T else U
      | replace _ T = T

    fun complete (vT as (v, _)) subst =
      subst
      |> not (Vartab.defined subst v) ? Vartab.update vT
      |> Vartab.map (K (apsnd (Term.map_atyps (replace vT))))

    fun cert (ix, (S, T)) = pairself (Thm.ctyp_of thy) (TVar (ix, S), T)

    fun inst subst =
      let val cTs = Vartab.fold (cons o cert) (fold complete Tenv subst) []
      in (i, Thm.instantiate (cTs, []) thm) end

  in (map inst substs @ ithms, ctxt') end



(* overall procedure *)

fun mono_all ctxt polys monos =
  let
    val scss = map (single o pair Vartab.empty o tvar_consts_of o snd) polys

    (* all known non-schematic instances of polymorphic constants: find all
       names of polymorphic constants, then add all known ground types *)
    val grounds =
      Symtab.empty
      |> fold (fold (fold (Symtab.update o rpair [] o fst) o snd)) scss
      |> fold (add_const_types (K true) o snd) monos
      |> fold (add_const_types (not o typ_has_tvars) o snd) polys

    val limit = Config.get ctxt SMT_Config.monomorph_limit
  in
    scss
    |> search_substitutions ctxt limit Symtab.empty grounds
    |> map (filter_most_specific (ProofContext.theory_of ctxt))
    |> rpair (monos, ctxt)
    |-> fold2 instantiate polys
  end

fun monomorph irules ctxt =
  irules
  |> List.partition (Term.exists_type typ_has_tvars o Thm.prop_of o snd)
  |>> incr_indexes  (* avoid clashes of schematic type variables *)
  |-> (fn [] => rpair ctxt | polys => mono_all ctxt polys)

end
