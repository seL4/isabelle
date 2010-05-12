(*  Title:      HOL/Tools/SMT/smt_monomorph.ML
    Author:     Sascha Boehme, TU Muenchen

Monomorphization of theorems, i.e., computation of all (necessary) instances.
*)

signature SMT_MONOMORPH =
sig
  val monomorph: thm list -> Proof.context -> thm list * Proof.context
end

structure SMT_Monomorph: SMT_MONOMORPH =
struct

val typ_has_tvars = Term.exists_subtype (fn TVar _ => true | _ => false)

val ignored = member (op =) [
  @{const_name All}, @{const_name Ex}, @{const_name Let}, @{const_name If},
  @{const_name "op ="}, @{const_name zero_class.zero},
  @{const_name one_class.one}, @{const_name number_of}]

fun is_const f (n, T) = not (ignored n) andalso f T
fun add_const_if f g (Const c) = if is_const f c then g c else I
  | add_const_if _ _ _ = I

fun collect_consts_if f g thm =
  Term.fold_aterms (add_const_if f g) (Thm.prop_of thm)

fun add_consts f =
  collect_consts_if f (fn (n, T) => Symtab.map_entry n (insert (op =) T))

val insert_const = OrdList.insert (prod_ord fast_string_ord Term_Ord.typ_ord)
fun tvar_consts_of thm = collect_consts_if typ_has_tvars insert_const thm []


fun incr_indexes thms =
  let fun inc thm idx = (Thm.incr_indexes idx thm, Thm.maxidx_of thm + idx + 1)
  in fst (fold_map inc thms 0) end


(* Compute all substitutions from the types "Ts" to all relevant
   types in "grounds", with respect to the given substitution. *)
fun new_substitutions thy grounds (n, T) subst =
  if not (typ_has_tvars T) then [subst]
  else
    Symtab.lookup_list grounds n
    |> map_filter (try (fn U => Sign.typ_match thy (T, U) subst))
    |> cons subst


(* Instantiate a set of constants with a substitution.  Also collect
   all new ground instances for the next round of specialization. *)
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


(* Compute new substitutions for the theorem "thm", based on
   previously found substitutions.
     Also collect new grounds, i.e., instantiated constants
   (without schematic types) which do not occur in any of the
   previous rounds. Note that thus no schematic type variables are
   shared among theorems. *)
fun specialize thy all_grounds new_grounds (thm, scs) =
  let
    fun spec (subst, consts) next_grounds =
      [subst]
      |> fold (maps o new_substitutions thy new_grounds) consts
      |> rpair next_grounds
      |-> fold_map (apply_subst all_grounds consts)
  in
    fold_map spec scs #>> (fn scss =>
    (thm, fold (fold (insert (eq_snd (op =)))) scss []))
  end


(* Compute all necessary substitutions.
     Instead of operating on the propositions of the theorems, the
   computation uses only the constants occurring with schematic type
   variables in the propositions. To ease comparisons, such sets of
   costants are always kept in their initial order. *)
fun incremental_monomorph thy limit all_grounds new_grounds ths =
  let
    val all_grounds' = Symtab.merge_list (op =) (all_grounds, new_grounds)
    val spec = specialize thy all_grounds' new_grounds
    val (ths', new_grounds') = fold_map spec ths Symtab.empty
  in
    if Symtab.is_empty new_grounds' then ths'
    else if limit > 0
    then incremental_monomorph thy (limit-1) all_grounds' new_grounds' ths'
    else (warning "SMT: monomorphization limit reached"; ths')
  end


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


fun instantiate thy Tenv =
  let
    fun replace (v, (_, T)) (U as TVar (u, _)) = if u = v then T else U
      | replace _ T = T

    fun complete (vT as (v, _)) subst =
      subst
      |> not (Vartab.defined subst v) ? Vartab.update vT
      |> Vartab.map (apsnd (Term.map_atyps (replace vT)))

    fun cert (ix, (S, T)) = pairself (Thm.ctyp_of thy) (TVar (ix, S), T)

    fun inst thm subst =
      let val cTs = Vartab.fold (cons o cert) (fold complete Tenv subst) []
      in Thm.instantiate (cTs, []) thm end

  in uncurry (map o inst) end


fun mono_all ctxt _ [] monos = (monos, ctxt)
  | mono_all ctxt limit polys monos =
      let
        fun invent_types thm ctxt =
          let val (vs, Ss) = split_list (Term.add_tvars (Thm.prop_of thm) [])
          in
            ctxt
            |> Variable.invent_types Ss
            |>> map2 (fn v => fn (n, S) => (v, (S, TFree (n, S)))) vs
          end
        val (Tenvs, ctxt') = fold_map invent_types polys ctxt

        val thy = ProofContext.theory_of ctxt'

        val ths = polys
          |> map (fn thm => (thm, [(Vartab.empty, tvar_consts_of thm)]))

        (* all constant names occurring with schematic types *)
        val ns = fold (fold (fold (insert (op =) o fst) o snd) o snd) ths []

        (* all known instances with non-schematic types *)
        val grounds =
          Symtab.make (map (rpair []) ns)
          |> fold (add_consts (K true)) monos
          |> fold (add_consts (not o typ_has_tvars)) polys
      in
        polys
        |> map (fn thm => (thm, [(Vartab.empty, tvar_consts_of thm)]))
        |> incremental_monomorph thy limit Symtab.empty grounds
        |> map (apsnd (filter_most_specific thy))
        |> flat o map2 (instantiate thy) Tenvs
        |> append monos
        |> rpair ctxt'
      end


val monomorph_limit = 10


(* Instantiate all polymorphic constants (i.e., constants occurring
   both with ground types and type variables) with all (necessary)
   ground types; thereby create copies of theorems containing those
   constants.
     To prevent non-termination, there is an upper limit for the
   number of recursions involved in the fixpoint construction.
     The initial set of theorems must not contain any schematic term
   variables, and the final list of theorems does not contain any
   schematic type variables anymore. *)
fun monomorph thms ctxt =
  thms
  |> List.partition (Term.exists_type typ_has_tvars o Thm.prop_of)
  |>> incr_indexes
  |-> mono_all ctxt monomorph_limit

end
