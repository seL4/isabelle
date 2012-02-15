(*  Title:      HOL/Boogie/Tools/boogie_vcs.ML
    Author:     Sascha Boehme, TU Muenchen

Store for Boogie's verification conditions.
*)

signature BOOGIE_VCS =
sig
  type vc
  val prop_of_vc: vc -> term
  val size_of: vc -> int
  val names_of: vc -> string list * string list
  val path_names_of: vc -> (string * bool) list list
  val paths_of: vc -> vc list
  val split_path: int -> vc -> (vc * vc) option
  val extract: vc -> string -> vc option
  val only: string list -> vc -> vc
  val without: string list -> vc -> vc
  val paths_and: int list -> string list -> vc -> vc
  val paths_without: int list -> string list -> vc -> vc

  datatype state = Proved | NotProved | PartiallyProved
  val set: (string * term) list -> theory -> theory
  val lookup: theory -> string -> vc option
  val discharge: string * (vc * thm) -> theory -> theory
  val state_of: theory -> (string * state) list
  val state_of_vc: theory -> string -> string list * string list
  val close: theory -> theory
  val is_closed: theory -> bool

  val rewrite_vcs: (theory -> term -> term) -> (theory -> thm -> thm) ->
    theory -> theory
  val add_assertion_filter: (term -> bool) -> theory -> theory
end

structure Boogie_VCs: BOOGIE_VCS =
struct

fun app_both f g (x, y) = (f x, g y)
fun app_hd_tl f g = (fn [] => [] | x :: xs => f x :: map g xs)


(* abstract representation of verification conditions *)

datatype vc =
  Assume of term * vc |
  Assert of (string * term) * vc |
  Ignore of vc |
  Proved of string * vc |
  Choice of vc * vc |
  True

val assume = curry Assume and assert = curry Assert
and proved = curry Proved and choice = curry Choice
and choice' = curry (Choice o swap)

val vc_of_term =
  let
    fun vc_of @{term True} = NONE
      | vc_of (@{term assert_at} $ Free (n, _) $ t) =
          SOME (Assert ((n, t), True))
      | vc_of (@{term HOL.implies} $ @{term True} $ u) = vc_of u
      | vc_of (@{term HOL.implies} $ t $ u) =
          vc_of u |> Option.map (assume t)
      | vc_of (@{term HOL.conj} $ (@{term assert_at} $ Free (n, _) $ t) $ u) =
          SOME (vc_of u |> the_default True |> assert (n, t))
      | vc_of (@{term HOL.conj} $ t $ u) =
          (case (vc_of t, vc_of u) of
            (NONE, r) => r
          | (l, NONE) => l
          | (SOME lv, SOME rv) => SOME (Choice (lv, rv)))
      | vc_of t = raise TERM ("vc_of_term", [t])
  in the_default True o vc_of end

val prop_of_vc =
  let
    fun mk_conj t u = @{term HOL.conj} $ t $ u

    fun term_of (Assume (t, v)) = @{term HOL.implies} $ t $ term_of v
      | term_of (Assert ((n, t), v)) =
          mk_conj (@{term assert_at} $ Free (n, @{typ bool}) $ t) (term_of v)
      | term_of (Ignore v) = term_of v
      | term_of (Proved (_, v)) = term_of v
      | term_of (Choice (lv, rv)) = mk_conj (term_of lv) (term_of rv)
      | term_of True = @{term True}
  in HOLogic.mk_Trueprop o term_of end


(* properties of verification conditions *)

fun size_of (Assume (_, v)) = size_of v
  | size_of (Assert (_, v)) = size_of v + 1
  | size_of (Ignore v) = size_of v
  | size_of (Proved (_, v)) = size_of v
  | size_of (Choice (lv, rv)) = size_of lv + size_of rv
  | size_of True = 0

val names_of =
  let
    fun add (Assume (_, v)) = add v
      | add (Assert ((n, _), v)) = apfst (cons n) #> add v
      | add (Ignore v) = add v
      | add (Proved (n, v)) = apsnd (cons n) #> add v
      | add (Choice (lv, rv)) = add lv #> add rv
      | add True = I
  in (fn vc => pairself rev (add vc ([], []))) end

fun path_names_of (Assume (_, v)) = path_names_of v
  | path_names_of (Assert ((n, _), v)) =
      path_names_of v
      |> app_hd_tl (cons (n, true)) (cons (n, false))
  | path_names_of (Ignore v) = path_names_of v
  | path_names_of (Proved (n, v)) = map (cons (n, false)) (path_names_of v)
  | path_names_of (Choice (lv, rv)) = path_names_of lv @ path_names_of rv
  | path_names_of True = [[]]

fun count_paths (Assume (_, v)) = count_paths v
  | count_paths (Assert (_, v)) = count_paths v
  | count_paths (Ignore v) = count_paths v
  | count_paths (Proved (_, v)) = count_paths v
  | count_paths (Choice (lv, rv)) = count_paths lv + count_paths rv
  | count_paths True = 1


(* extract parts of a verification condition *)

fun paths_of (Assume (t, v)) = paths_of v |> map (assume t)
  | paths_of (Assert (a, v)) = paths_of v |> app_hd_tl (assert a) Ignore
  | paths_of (Ignore v) = paths_of v |> map Ignore
  | paths_of (Proved (n, v)) = paths_of v |> app_hd_tl (proved n) Ignore
  | paths_of (Choice (lv, rv)) =
      map (choice' True) (paths_of lv) @ map (choice True) (paths_of rv)
  | paths_of True = [True]

fun prune f (Assume (t, v)) = Option.map (assume t) (prune f v)
  | prune f (Assert (a, v)) = f a v
  | prune f (Ignore v) = Option.map Ignore (prune f v)
  | prune f (Proved (n, v)) = Option.map (proved n) (prune f v)
  | prune f (Choice (lv, rv)) =
      (case (prune f lv, prune f rv) of
        (NONE, r) => r |> Option.map (choice True)
      | (l, NONE) => l |> Option.map (choice' True)
      | (SOME lv', SOME rv') => SOME (Choice (lv', rv')))
  | prune _ True = NONE

val split_path =
  let
    fun app f = Option.map (pairself f)

    fun split i (Assume (t, v)) = app (assume t) (split i v)
      | split i (Assert (a, v)) =
          if i > 1
          then Option.map (app_both (assert a) Ignore) (split (i-1) v)
          else Option.map (pair (Assert (a, True)))
            (prune (SOME o Assert oo pair) (Ignore v))
      | split i (Ignore v) = app Ignore (split i v)
      | split i (Proved (n, v)) = app (proved n) (split i v)
      | split i (Choice (v, True)) = app (choice' True) (split i v)
      | split i (Choice (True, v)) = app (choice True) (split i v)
      | split _ _ = NONE
  in split end

fun select_labels P =
  let
    fun assert (a as (n, _)) v =
      if P n then SOME (Assert (a, the_default True v))
      else Option.map Ignore v
    fun sel vc = prune (fn a => assert a o sel) vc
  in sel end

fun extract vc l = select_labels (equal l) vc
fun only ls = the_default True o select_labels (member (op =) ls)
fun without ls = the_default True o select_labels (not o member (op =) ls)

fun select_paths ps sub_select =
  let
    fun disjoint pp = null (inter (op =) ps pp)

    fun sel pp (Assume (t, v)) = Assume (t, sel pp v)
      | sel pp (Assert (a, v)) =
          if member (op =) ps (hd pp)
          then Assert (a, sel pp v)
          else Ignore (sel pp v)
      | sel pp (Ignore v) = Ignore (sel pp v)
      | sel pp (Proved (n, v)) = Proved (n, sel pp v)
      | sel pp (Choice (lv, rv)) =
          let val (lpp, rpp) = chop (count_paths lv) pp
          in
            if disjoint lpp then Choice (sub_select lv, sel rpp rv)
            else if disjoint rpp then Choice (sel lpp lv, sub_select rv)
            else Choice (sel lpp lv, sel rpp rv)
          end
      | sel _ True = True

    fun sel0 vc =
      let val pp = 1 upto count_paths vc
      in if disjoint pp then True else sel pp vc end
  in sel0 end

fun paths_and ps ls = select_paths ps (only ls)
fun paths_without ps ls = without ls o select_paths ps (K True)


(* discharge parts of a verification condition *)

local
  fun cprop_of thy t = Thm.cterm_of thy (HOLogic.mk_Trueprop t)
  fun imp_intr ct thm = Thm.implies_intr ct thm COMP_INCR @{thm impI}
  fun imp_elim th thm = @{thm mp} OF [thm, th]
  fun conj1 thm = @{thm conjunct1} OF [thm]
  fun conj2 thm = @{thm conjunct2} OF [thm]
  fun conj_intr lth rth = @{thm conjI} OF [lth, rth]
in
fun thm_of thy (Assume (t, v)) = imp_intr (cprop_of thy t) (thm_of thy v)
  | thm_of thy (Assert (_, v)) = thm_of thy v
  | thm_of thy (Ignore v) = thm_of thy v
  | thm_of thy (Proved (_, v)) = thm_of thy v
  | thm_of thy (Choice (lv, rv)) = conj_intr (thm_of thy lv) (thm_of thy rv)
  | thm_of _ True = @{thm TrueI}

fun join (Assume (_, pv), pthm) (Assume (t, v), thm) =
      let
        val mk_prop = Thm.apply @{cterm Trueprop}
        val ct = Thm.cprop_of thm |> Thm.dest_arg |> Thm.dest_arg1 |> mk_prop
        val th = Thm.assume ct
        val (v', thm') = join (pv, imp_elim th pthm) (v, imp_elim th thm)
      in (Assume (t, v'), imp_intr ct thm') end
  | join (Assert ((pn, pt), pv), pthm) (Assert ((n, t), v), thm) =
      let val pthm1 = conj1 pthm
      in
        if pn = n andalso pt aconv t
        then
          let val (v', thm') = join (pv, conj2 pthm) (v, thm)
          in (Proved (n, v'), conj_intr pthm1 thm') end
        else raise THM ("join: not matching", 1, [thm, pthm])
      end
  | join (Ignore pv, pthm) (Assert (a, v), thm) =
      join (pv, pthm) (v, thm) |>> assert a
  | join (Proved (_, pv), pthm) (Proved (n, v), thm) =
      let val (v', thm') = join (pv, pthm) (v, conj2 thm)
      in (Proved (n, v'), conj_intr (conj1 thm) thm') end
  | join (Ignore pv, pthm) (Proved (n, v), thm) =
      let val (v', thm') = join (pv, pthm) (v, conj2 thm)
      in (Proved (n, v'), conj_intr (conj1 thm) thm') end
  | join (Choice (plv, prv), pthm) (Choice (lv, rv), thm) =
      let
        val (lv', lthm) = join (plv, conj1 pthm) (lv, conj1 thm)
        val (rv', rthm) = join (prv, conj2 pthm) (rv, conj2 thm)
      in (Choice (lv', rv'), conj_intr lthm rthm) end
  | join (True, pthm) (v, thm) =
      if Thm.prop_of pthm aconv @{prop True} then (v, thm)
      else raise THM ("join: not True", 1, [pthm])
  | join (_, pthm) (_, thm) = raise THM ("join: not matching", 1, [thm, pthm])
end


fun err_unfinished () = error "An unfinished Boogie environment is still open."

fun err_vcs names = error (Pretty.string_of
  (Pretty.big_list "Undischarged Boogie verification conditions found:"
    (map Pretty.str names)))

type vcs_data = {
  vcs: (vc * (term * thm)) Symtab.table option,
  rewrite: theory -> thm -> thm,
  filters: (serial * (term -> bool)) Ord_List.T }

fun make_vcs_data (vcs, rewrite, filters) =
  {vcs=vcs, rewrite=rewrite, filters=filters}

fun map_vcs_data f ({vcs, rewrite, filters}) =
  make_vcs_data (f (vcs, rewrite, filters))

fun serial_ord ((i, _), (j, _)) = int_ord (i, j)

structure VCs_Data = Theory_Data
(
  type T = vcs_data
  val empty : T = make_vcs_data (NONE, K I, [])
  val extend = I
  fun merge ({vcs=vcs1, filters=fs1, ...} : T, {vcs=vcs2, filters=fs2, ...} : T) =
    (case (vcs1, vcs2) of
      (NONE, NONE) =>
        make_vcs_data (NONE, K I, Ord_List.merge serial_ord (fs1, fs2))
    | _ => err_unfinished ())
)

fun add_assertion_filter f =
  VCs_Data.map (map_vcs_data (fn (vcs, rewrite, filters) =>
    (vcs, rewrite, Ord_List.insert serial_ord (serial (), f) filters)))

fun filter_assertions thy =
  let
    fun filt_assert [] a = assert a
      | filt_assert ((_, f) :: fs) (a as (_, t)) =
          if f t then filt_assert fs a else I

    fun filt fs vc =
      the_default True (prune (fn a => SOME o filt_assert fs a o filt fs) vc)

  in filt (#filters (VCs_Data.get thy)) end

fun prep thy =
  vc_of_term #>
  filter_assertions thy #>
  (fn vc => (vc, (prop_of_vc vc, thm_of thy vc)))

fun set new_vcs thy = VCs_Data.map (map_vcs_data (fn (vcs, rewrite, filters) =>
  (case vcs of
    NONE => (SOME (Symtab.make (map (apsnd (prep thy)) new_vcs)), K I, filters)
  | SOME _ => err_unfinished ()))) thy

fun lookup thy name =
  (case #vcs (VCs_Data.get thy) of
    SOME vcs => Option.map fst (Symtab.lookup vcs name)
  | NONE => NONE)

fun discharge (name, prf) =
  let fun jn (vc, (t, thm)) = join prf (vc, thm) |> apsnd (pair t)
  in
    VCs_Data.map (map_vcs_data (fn (vcs, rewrite, filters) =>
      (Option.map (Symtab.map_entry name jn) vcs, rewrite, filters)))
  end

datatype state = Proved | NotProved | PartiallyProved

fun state_of_vc thy name =
  (case lookup thy name of
    SOME vc => names_of vc
  | NONE => ([], []))

fun state_of_vc' (vc, _) =
  (case names_of vc of
    ([], _) => Proved
  | (_, []) => NotProved
  | (_, _) => PartiallyProved)

fun state_of thy =
  (case #vcs (VCs_Data.get thy) of
    SOME vcs => map (apsnd state_of_vc') (Symtab.dest vcs)
  | NONE => [])

fun finished g (_, (t, thm)) = Thm.prop_of (g thm) aconv t

fun close thy = VCs_Data.map (map_vcs_data (fn (vcs, rewrite, filters) =>
  (case vcs of
    SOME raw_vcs =>
      let
        fun check vc =
          state_of_vc' vc = Proved andalso finished (rewrite thy) vc

        val _ =
          Symtab.dest raw_vcs
          |> map_filter (fn (n, vc) => if check vc then NONE else SOME n)
          |> (fn names => if null names then () else err_vcs names)
      in (NONE, rewrite, filters) end
  | NONE => (NONE, rewrite, filters)))) thy

val is_closed = is_none o #vcs o VCs_Data.get

fun rewrite_vcs f g thy =
  let
    fun rewr (_, (t, _)) = vc_of_term (f thy t)
      |> (fn vc => (vc, (t, thm_of thy vc)))
  in
    VCs_Data.map (map_vcs_data (fn (vcs, _, filters) =>
      (Option.map (Symtab.map (K rewr)) vcs, g, filters))) thy
  end

end
