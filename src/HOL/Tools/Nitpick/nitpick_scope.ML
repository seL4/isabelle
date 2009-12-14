(*  Title:      HOL/Tools/Nitpick/nitpick_scope.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Scope enumerator for Nitpick.
*)

signature NITPICK_SCOPE =
sig
  type styp = Nitpick_Util.styp
  type extended_context = Nitpick_HOL.extended_context

  type constr_spec = {
    const: styp,
    delta: int,
    epsilon: int,
    exclusive: bool,
    explicit_max: int,
    total: bool}

  type dtype_spec = {
    typ: typ,
    card: int,
    co: bool,
    precise: bool,
    shallow: bool,
    constrs: constr_spec list}

  type scope = {
    ext_ctxt: extended_context,
    card_assigns: (typ * int) list,
    bisim_depth: int,
    datatypes: dtype_spec list,
    ofs: int Typtab.table}

  val datatype_spec : dtype_spec list -> typ -> dtype_spec option
  val constr_spec : dtype_spec list -> styp -> constr_spec
  val is_precise_type : dtype_spec list -> typ -> bool
  val is_fully_comparable_type : dtype_spec list -> typ -> bool
  val offset_of_type : int Typtab.table -> typ -> int
  val spec_of_type : scope -> typ -> int * int
  val pretties_for_scope : scope -> bool -> Pretty.T list
  val multiline_string_for_scope : scope -> string
  val scopes_equivalent : scope -> scope -> bool
  val scope_less_eq : scope -> scope -> bool
  val all_scopes :
    extended_context -> int -> (typ option * int list) list
    -> (styp option * int list) list -> (styp option * int list) list
    -> int list -> typ list -> typ list -> typ list -> int * scope list
end;

structure Nitpick_Scope : NITPICK_SCOPE =
struct

open Nitpick_Util
open Nitpick_HOL

type constr_spec = {
  const: styp,
  delta: int,
  epsilon: int,
  exclusive: bool,
  explicit_max: int,
  total: bool}

type dtype_spec = {
  typ: typ,
  card: int,
  co: bool,
  precise: bool,
  shallow: bool,
  constrs: constr_spec list}

type scope = {
  ext_ctxt: extended_context,
  card_assigns: (typ * int) list,
  bisim_depth: int,
  datatypes: dtype_spec list,
  ofs: int Typtab.table}

datatype row_kind = Card of typ | Max of styp

type row = row_kind * int list
type block = row list

(* dtype_spec list -> typ -> dtype_spec option *)
fun datatype_spec (dtypes : dtype_spec list) T =
  List.find (curry (op =) T o #typ) dtypes

(* dtype_spec list -> styp -> constr_spec *)
fun constr_spec [] x = raise TERM ("Nitpick_Scope.constr_spec", [Const x])
  | constr_spec ({constrs, ...} :: dtypes : dtype_spec list) (x as (s, T)) =
    case List.find (curry (op =) (s, body_type T) o (apsnd body_type o #const))
                   constrs of
      SOME c => c
    | NONE => constr_spec dtypes x

(* dtype_spec list -> typ -> bool *)
fun is_precise_type dtypes (Type ("fun", Ts)) =
    forall (is_precise_type dtypes) Ts
  | is_precise_type dtypes (Type ("*", Ts)) = forall (is_precise_type dtypes) Ts
  | is_precise_type dtypes T =
    not (is_integer_type T) andalso #precise (the (datatype_spec dtypes T))
    handle Option.Option => true
fun is_fully_comparable_type dtypes (Type ("fun", [T1, T2])) =
    is_precise_type dtypes T1 andalso is_fully_comparable_type dtypes T2
  | is_fully_comparable_type dtypes (Type ("*", Ts)) =
    forall (is_fully_comparable_type dtypes) Ts
  | is_fully_comparable_type _ _ = true

(* int Typtab.table -> typ -> int *)
fun offset_of_type ofs T =
  case Typtab.lookup ofs T of
    SOME j0 => j0
  | NONE => Typtab.lookup ofs dummyT |> the_default 0

(* scope -> typ -> int * int *)
fun spec_of_type ({card_assigns, ofs, ...} : scope) T =
  (card_of_type card_assigns T
   handle TYPE ("Nitpick_HOL.card_of_type", _, _) => ~1, offset_of_type ofs T)

(* (string -> string) -> scope
   -> string list * string list * string list * string list * string list *)
fun quintuple_for_scope quote ({ext_ctxt as {thy, ctxt, ...}, card_assigns,
                                bisim_depth, datatypes, ...} : scope) =
  let
    val (iter_asgns, card_asgns) =
      card_assigns |> filter_out (curry (op =) @{typ bisim_iterator} o fst)
                   |> List.partition (is_fp_iterator_type o fst)
    val (unimportant_card_asgns, important_card_asgns) =
      card_asgns |> List.partition ((is_integer_type orf is_datatype thy) o fst)
    val cards =
      map (fn (T, k) => quote (string_for_type ctxt T) ^ " = " ^
                        string_of_int k)
    fun maxes () =
      maps (map_filter
                (fn {const, explicit_max, ...} =>
                    if explicit_max < 0 then
                      NONE
                    else
                      SOME (Syntax.string_of_term ctxt (Const const) ^ " = " ^
                            string_of_int explicit_max))
                 o #constrs) datatypes
    fun iters () =
      map (fn (T, k) =>
              quote (Syntax.string_of_term ctxt
                         (Const (const_for_iterator_type T))) ^ " = " ^
              string_of_int (k - 1)) iter_asgns
    fun bisims () =
      if bisim_depth < 0 andalso forall (not o #co) datatypes then []
      else ["bisim_depth = " ^ string_of_int bisim_depth]
  in
    setmp_show_all_types
        (fn () => (cards important_card_asgns, cards unimportant_card_asgns,
                   maxes (), iters (), bisims ())) ()
  end

(* scope -> bool -> Pretty.T list *)
fun pretties_for_scope scope verbose =
  let
    val (important_cards, unimportant_cards, maxes, iters, bisim_depths) =
      quintuple_for_scope maybe_quote scope
    val ss = map (prefix "card ") important_cards @
             (if verbose then
                map (prefix "card ") unimportant_cards @
                map (prefix "max ") maxes @
                map (prefix "iter ") iters @
                bisim_depths
              else
                [])
  in
    if null ss then []
    else serial_commas "and" ss |> map Pretty.str |> Pretty.breaks
  end

(* scope -> string *)
fun multiline_string_for_scope scope =
  let
    val (important_cards, unimportant_cards, maxes, iters, bisim_depths) =
      quintuple_for_scope I scope
    val cards = important_cards @ unimportant_cards
  in
    case (if null cards then [] else ["card: " ^ commas cards]) @
         (if null maxes then [] else ["max: " ^ commas maxes]) @
         (if null iters then [] else ["iter: " ^ commas iters]) @
         bisim_depths of
      [] => "empty"
    | lines => space_implode "\n" lines
  end

(* scope -> scope -> bool *)
fun scopes_equivalent (s1 : scope) (s2 : scope) =
  #datatypes s1 = #datatypes s2 andalso #card_assigns s1 = #card_assigns s2
fun scope_less_eq (s1 : scope) (s2 : scope) =
  (s1, s2) |> pairself (map snd o #card_assigns) |> op ~~ |> forall (op <=)

(* row -> int *)
fun rank_of_row (_, ks) = length ks
(* block -> int *)
fun rank_of_block block = fold Integer.max (map rank_of_row block) 1
(* int -> typ * int list -> typ * int list *)
fun project_row column (y, ks) = (y, [nth ks (Int.min (column, length ks - 1))])
(* int -> block -> block *)
fun project_block (column, block) = map (project_row column) block

(* (''a * ''a -> bool) -> (''a option * int list) list -> ''a -> int list *)
fun lookup_ints_assign eq asgns key =
  case triple_lookup eq asgns key of
    SOME ks => ks
  | NONE => raise ARG ("Nitpick_Scope.lookup_ints_assign", "")
(* theory -> (typ option * int list) list -> typ -> int list *)
fun lookup_type_ints_assign thy asgns T =
  map (curry Int.max 1) (lookup_ints_assign (type_match thy) asgns T)
  handle ARG ("Nitpick_Scope.lookup_ints_assign", _) =>
         raise TYPE ("Nitpick_Scope.lookup_type_ints_assign", [T], [])
(* theory -> (styp option * int list) list -> styp -> int list *)
fun lookup_const_ints_assign thy asgns x =
  lookup_ints_assign (const_match thy) asgns x
  handle ARG ("Nitpick_Scope.lookup_ints_assign", _) =>
         raise TERM ("Nitpick_Scope.lookup_const_ints_assign", [Const x])

(* theory -> (styp option * int list) list -> styp -> row option *)
fun row_for_constr thy maxes_asgns constr =
  SOME (Max constr, lookup_const_ints_assign thy maxes_asgns constr)
  handle TERM ("lookup_const_ints_assign", _) => NONE

(* extended_context -> (typ option * int list) list
   -> (styp option * int list) list -> (styp option * int list) list -> int list
   -> typ -> block *)
fun block_for_type (ext_ctxt as {thy, ...}) cards_asgns maxes_asgns iters_asgns
                   bisim_depths T =
  if T = @{typ bisim_iterator} then
    [(Card T, map (fn k => Int.max (0, k) + 1) bisim_depths)]
  else if is_fp_iterator_type T then
    [(Card T, map (fn k => Int.max (0, k) + 1)
                  (lookup_const_ints_assign thy iters_asgns
                                            (const_for_iterator_type T)))]
  else
    (Card T, lookup_type_ints_assign thy cards_asgns T) ::
    (case datatype_constrs ext_ctxt T of
       [_] => []
     | constrs => map_filter (row_for_constr thy maxes_asgns) constrs)

(* extended_context -> (typ option * int list) list
   -> (styp option * int list) list -> (styp option * int list) list -> int list
   -> typ list -> typ list -> block list *)
fun blocks_for_types ext_ctxt cards_asgns maxes_asgns iters_asgns bisim_depths
                     mono_Ts nonmono_Ts =
  let
    (* typ -> block *)
    val block_for = block_for_type ext_ctxt cards_asgns maxes_asgns iters_asgns
                                   bisim_depths
    val mono_block = maps block_for mono_Ts
    val nonmono_blocks = map block_for nonmono_Ts
  in mono_block :: nonmono_blocks end

val sync_threshold = 5

(* int list -> int list list *)
fun all_combinations_ordered_smartly ks =
  let
    (* int list -> int *)
    fun cost_with_monos [] = 0
      | cost_with_monos (k :: ks) =
        if k < sync_threshold andalso forall (curry (op =) k) ks then
          k - sync_threshold
        else
          k * (k + 1) div 2 + Integer.sum ks
    fun cost_without_monos [] = 0
      | cost_without_monos [k] = k
      | cost_without_monos (_ :: k :: ks) =
        if k < sync_threshold andalso forall (curry (op =) k) ks then
          k - sync_threshold
        else
          Integer.sum (k :: ks)
  in
    ks |> all_combinations
       |> map (`(if fst (hd ks) > 1 then cost_with_monos
                 else cost_without_monos))
       |> sort (int_ord o pairself fst) |> map snd
  end

(* typ -> bool *)
fun is_self_recursive_constr_type T =
  exists (exists_subtype (curry (op =) (body_type T))) (binder_types T)

(* (styp * int) list -> styp -> int *)
fun constr_max maxes x = the_default ~1 (AList.lookup (op =) maxes x)

type scope_desc = (typ * int) list * (styp * int) list

(* extended_context -> scope_desc -> typ * int -> bool *)
fun is_surely_inconsistent_card_assign ext_ctxt (card_asgns, max_asgns) (T, k) =
  case datatype_constrs ext_ctxt T of
    [] => false
  | xs =>
    let
      val precise_cards =
        map (Integer.prod
             o map (bounded_precise_card_of_type ext_ctxt k 0 card_asgns)
             o binder_types o snd) xs
      val maxes = map (constr_max max_asgns) xs
      (* int -> int -> int *)
      fun effective_max 0 ~1 = k
        | effective_max 0 max = max
        | effective_max card ~1 = card
        | effective_max card max = Int.min (card, max)
      val max = map2 effective_max precise_cards maxes |> Integer.sum
      (* unit -> int *)
      fun doms_card () =
        xs |> map (Integer.prod o map (bounded_card_of_type k ~1 card_asgns)
                   o binder_types o snd)
           |> Integer.sum
    in
      max < k
      orelse (forall (not_equal 0) precise_cards andalso doms_card () < k)
    end
    handle TYPE ("Nitpick_HOL.card_of_type", _, _) => false

(* extended_context -> scope_desc -> bool *)
fun is_surely_inconsistent_scope_description ext_ctxt
                                             (desc as (card_asgns, _)) =
  exists (is_surely_inconsistent_card_assign ext_ctxt desc) card_asgns

(* extended_context -> scope_desc -> (typ * int) list option *)
fun repair_card_assigns ext_ctxt (card_asgns, max_asgns) =
  let
    (* (typ * int) list -> (typ * int) list -> (typ * int) list option *)
    fun aux seen [] = SOME seen
      | aux seen ((T, 0) :: _) = NONE
      | aux seen ((T, k) :: asgns) =
        (if is_surely_inconsistent_scope_description ext_ctxt
                ((T, k) :: seen, max_asgns) then
           raise SAME ()
         else
           case aux ((T, k) :: seen) asgns of
             SOME asgns => SOME asgns
           | NONE => raise SAME ())
        handle SAME () => aux seen ((T, k - 1) :: asgns)
  in aux [] (rev card_asgns) end

(* theory -> (typ * int) list -> typ * int -> typ * int *)
fun repair_iterator_assign thy asgns (T as Type (s, Ts), k) =
    (T, if T = @{typ bisim_iterator} then
          let val co_cards = map snd (filter (is_codatatype thy o fst) asgns) in
            Int.min (k, Integer.sum co_cards)
          end
        else if is_fp_iterator_type T then
          case Ts of
            [] => 1
          | _ => bounded_card_of_type k ~1 asgns (foldr1 HOLogic.mk_prodT Ts)
        else
          k)
  | repair_iterator_assign _ _ asgn = asgn

(* row -> scope_desc -> scope_desc *)
fun add_row_to_scope_descriptor (kind, ks) (card_asgns, max_asgns) =
  case kind of
    Card T => ((T, the_single ks) :: card_asgns, max_asgns)
  | Max x => (card_asgns, (x, the_single ks) :: max_asgns)
(* block -> scope_desc *)
fun scope_descriptor_from_block block =
  fold_rev add_row_to_scope_descriptor block ([], [])
(* extended_context -> block list -> int list -> scope_desc option *)
fun scope_descriptor_from_combination (ext_ctxt as {thy, ...}) blocks columns =
  let
    val (card_asgns, max_asgns) =
      maps project_block (columns ~~ blocks) |> scope_descriptor_from_block
    val card_asgns = repair_card_assigns ext_ctxt (card_asgns, max_asgns) |> the
  in
    SOME (map (repair_iterator_assign thy card_asgns) card_asgns, max_asgns)
  end
  handle Option.Option => NONE

(* theory -> (typ * int) list -> dtype_spec list -> int Typtab.table *)
fun offset_table_for_card_assigns thy asgns dtypes =
  let
    (* int -> (int * int) list -> (typ * int) list -> int Typtab.table
       -> int Typtab.table *)
    fun aux next _ [] = Typtab.update_new (dummyT, next)
      | aux next reusable ((T, k) :: asgns) =
        if k = 1 orelse is_integer_type T then
          aux next reusable asgns
        else if length (these (Option.map #constrs (datatype_spec dtypes T)))
                > 1 then
          Typtab.update_new (T, next) #> aux (next + k) reusable asgns
        else
          case AList.lookup (op =) reusable k of
            SOME j0 => Typtab.update_new (T, j0) #> aux next reusable asgns
          | NONE => Typtab.update_new (T, next)
                    #> aux (next + k) ((k, next) :: reusable) asgns
  in aux 0 [] asgns Typtab.empty end

(* int -> (typ * int) list -> typ -> int *)
fun domain_card max card_asgns =
  Integer.prod o map (bounded_card_of_type max max card_asgns) o binder_types

(* scope_desc -> bool -> int -> (int -> int) -> int -> int -> bool * styp
   -> constr_spec list -> constr_spec list *)
fun add_constr_spec (card_asgns, max_asgns) co card sum_dom_cards num_self_recs
                    num_non_self_recs (self_rec, x as (s, T)) constrs =
  let
    val max = constr_max max_asgns x
    (* int -> int *)
    fun bound k = Int.min (card, (max >= 0 ? curry Int.min max) k)
    (* unit -> int *)
    fun next_delta () = if null constrs then 0 else #epsilon (hd constrs)
    val {delta, epsilon, exclusive, total} =
      if max = 0 then
        let val delta = next_delta () in
          {delta = delta, epsilon = delta, exclusive = true, total = false}
        end
      else if not co andalso num_self_recs > 0 then
        if not self_rec andalso num_non_self_recs = 1
           andalso domain_card 2 card_asgns T = 1 then
          {delta = 0, epsilon = 1, exclusive = (s = @{const_name Nil}),
           total = true}
        else if s = @{const_name Cons} then
          {delta = 1, epsilon = card, exclusive = true, total = false}
        else
          {delta = 0, epsilon = card, exclusive = false, total = false}
      else if card = sum_dom_cards (card + 1) then
        let val delta = next_delta () in
          {delta = delta, epsilon = delta + domain_card card card_asgns T,
           exclusive = true, total = true}
        end
      else
        {delta = 0, epsilon = card,
         exclusive = (num_self_recs + num_non_self_recs = 1), total = false}
  in
    {const = x, delta = delta, epsilon = epsilon, exclusive = exclusive,
     explicit_max = max, total = total} :: constrs
  end

(* extended_context -> typ list -> scope_desc -> typ * int -> dtype_spec *)
fun datatype_spec_from_scope_descriptor (ext_ctxt as {thy, ...}) shallow_dataTs
                                        (desc as (card_asgns, _)) (T, card) =
  let
    val shallow = member (op =) shallow_dataTs T
    val co = is_codatatype thy T
    val xs = boxed_datatype_constrs ext_ctxt T
    val self_recs = map (is_self_recursive_constr_type o snd) xs
    val (num_self_recs, num_non_self_recs) =
      List.partition (curry (op =) true) self_recs |> pairself length
    val precise = (card = bounded_precise_card_of_type ext_ctxt (card + 1) 0
                                                       card_asgns T)
    (* int -> int *)
    fun sum_dom_cards max =
      map (domain_card max card_asgns o snd) xs |> Integer.sum
    val constrs =
      fold_rev (add_constr_spec desc co card sum_dom_cards num_self_recs
                                num_non_self_recs) (self_recs ~~ xs) []
  in
    {typ = T, card = card, co = co, precise = precise, shallow = shallow,
     constrs = constrs}
  end

(* extended_context -> int -> typ list -> scope_desc -> scope *)
fun scope_from_descriptor (ext_ctxt as {thy, ...}) sym_break shallow_dataTs
                          (desc as (card_asgns, _)) =
  let
    val datatypes =
      map (datatype_spec_from_scope_descriptor ext_ctxt shallow_dataTs desc)
          (filter (is_datatype thy o fst) card_asgns)
    val bisim_depth = card_of_type card_asgns @{typ bisim_iterator} - 1
  in
    {ext_ctxt = ext_ctxt, card_assigns = card_asgns, datatypes = datatypes,
     bisim_depth = bisim_depth,
     ofs = if sym_break <= 0 then Typtab.empty
           else offset_table_for_card_assigns thy card_asgns datatypes}
  end

(* theory -> typ list -> (typ option * int list) list
   -> (typ option * int list) list *)
fun fix_cards_assigns_wrt_boxing _ _ [] = []
  | fix_cards_assigns_wrt_boxing thy Ts ((SOME T, ks) :: cards_asgns) =
    (if is_fun_type T orelse is_pair_type T then
       Ts |> filter (curry (type_match thy o swap) T o unbox_type)
          |> map (rpair ks o SOME)
     else
       [(SOME T, ks)]) @ fix_cards_assigns_wrt_boxing thy Ts cards_asgns
  | fix_cards_assigns_wrt_boxing thy Ts ((NONE, ks) :: cards_asgns) =
    (NONE, ks) :: fix_cards_assigns_wrt_boxing thy Ts cards_asgns

val max_scopes = 4096
val distinct_threshold = 512

(* extended_context -> int -> (typ option * int list) list
   -> (styp option * int list) list -> (styp option * int list) list -> int list
   -> typ list -> typ list -> typ list -> int * scope list *)
fun all_scopes (ext_ctxt as {thy, ...}) sym_break cards_asgns maxes_asgns
               iters_asgns bisim_depths mono_Ts nonmono_Ts shallow_dataTs =
  let
    val cards_asgns = fix_cards_assigns_wrt_boxing thy mono_Ts cards_asgns
    val blocks = blocks_for_types ext_ctxt cards_asgns maxes_asgns iters_asgns
                                  bisim_depths mono_Ts nonmono_Ts
    val ranks = map rank_of_block blocks
    val all = all_combinations_ordered_smartly (map (rpair 0) ranks)
    val head = take max_scopes all
    val descs = map_filter (scope_descriptor_from_combination ext_ctxt blocks)
                           head
  in
    (length all - length head,
     descs |> length descs <= distinct_threshold ? distinct (op =)
           |> map (scope_from_descriptor ext_ctxt sym_break shallow_dataTs))
  end

end;
