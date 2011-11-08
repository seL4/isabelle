(*  Title:      HOL/Tools/Nitpick/nitpick_scope.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009, 2010

Scope enumerator for Nitpick.
*)

signature NITPICK_SCOPE =
sig
  type styp = Nitpick_Util.styp
  type hol_context = Nitpick_HOL.hol_context

  type constr_spec =
    {const: styp,
     delta: int,
     epsilon: int,
     exclusive: bool,
     explicit_max: int,
     total: bool}

  type datatype_spec =
    {typ: typ,
     card: int,
     co: bool,
     standard: bool,
     self_rec: bool,
     complete: bool * bool,
     concrete: bool * bool,
     deep: bool,
     constrs: constr_spec list}

  type scope =
    {hol_ctxt: hol_context,
     binarize: bool,
     card_assigns: (typ * int) list,
     bits: int,
     bisim_depth: int,
     datatypes: datatype_spec list,
     ofs: int Typtab.table}

  val is_asymmetric_nondatatype : typ -> bool
  val datatype_spec : datatype_spec list -> typ -> datatype_spec option
  val constr_spec : datatype_spec list -> styp -> constr_spec
  val is_complete_type : datatype_spec list -> bool -> typ -> bool
  val is_concrete_type : datatype_spec list -> bool -> typ -> bool
  val is_exact_type : datatype_spec list -> bool -> typ -> bool
  val offset_of_type : int Typtab.table -> typ -> int
  val spec_of_type : scope -> typ -> int * int
  val pretties_for_scope : scope -> bool -> Pretty.T list
  val multiline_string_for_scope : scope -> string
  val scopes_equivalent : scope * scope -> bool
  val scope_less_eq : scope -> scope -> bool
  val is_self_recursive_constr_type : typ -> bool
  val all_scopes :
    hol_context -> bool -> (typ option * int list) list
    -> (styp option * int list) list -> (styp option * int list) list
    -> int list -> int list -> typ list -> typ list -> typ list -> typ list
    -> int * scope list
end;

structure Nitpick_Scope : NITPICK_SCOPE =
struct

open Nitpick_Util
open Nitpick_HOL

type constr_spec =
  {const: styp,
   delta: int,
   epsilon: int,
   exclusive: bool,
   explicit_max: int,
   total: bool}

type datatype_spec =
  {typ: typ,
   card: int,
   co: bool,
   standard: bool,
   self_rec: bool,
   complete: bool * bool,
   concrete: bool * bool,
   deep: bool,
   constrs: constr_spec list}

type scope =
  {hol_ctxt: hol_context,
   binarize: bool,
   card_assigns: (typ * int) list,
   bits: int,
   bisim_depth: int,
   datatypes: datatype_spec list,
   ofs: int Typtab.table}

datatype row_kind = Card of typ | Max of styp

type row = row_kind * int list
type block = row list

val is_asymmetric_nondatatype =
  is_iterator_type orf is_integer_type orf is_bit_type

fun datatype_spec (dtypes : datatype_spec list) T =
  List.find (curry (op =) T o #typ) dtypes

fun constr_spec [] x = raise TERM ("Nitpick_Scope.constr_spec", [Const x])
  | constr_spec ({constrs, ...} :: dtypes : datatype_spec list) (x as (s, T)) =
    case List.find (curry (op =) (s, body_type T) o (apsnd body_type o #const))
                   constrs of
      SOME c => c
    | NONE => constr_spec dtypes x

fun is_complete_type dtypes facto (Type (@{type_name fun}, [T1, T2])) =
    is_concrete_type dtypes facto T1 andalso is_complete_type dtypes facto T2
  | is_complete_type dtypes facto (Type (@{type_name prod}, Ts)) =
    forall (is_complete_type dtypes facto) Ts
  | is_complete_type dtypes facto T =
    not (is_integer_like_type T) andalso not (is_bit_type T) andalso
    fun_from_pair (#complete (the (datatype_spec dtypes T))) facto
    handle Option.Option => true
and is_concrete_type dtypes facto (Type (@{type_name fun}, [T1, T2])) =
    is_complete_type dtypes facto T1 andalso is_concrete_type dtypes facto T2
  | is_concrete_type dtypes facto (Type (@{type_name prod}, Ts)) =
    forall (is_concrete_type dtypes facto) Ts
  | is_concrete_type dtypes facto T =
    fun_from_pair (#concrete (the (datatype_spec dtypes T))) facto
    handle Option.Option => true
and is_exact_type dtypes facto =
  is_complete_type dtypes facto andf is_concrete_type dtypes facto

fun offset_of_type ofs T =
  case Typtab.lookup ofs T of
    SOME j0 => j0
  | NONE => Typtab.lookup ofs dummyT |> the_default 0

fun spec_of_type ({card_assigns, ofs, ...} : scope) T =
  (card_of_type card_assigns T
   handle TYPE ("Nitpick_HOL.card_of_type", _, _) => ~1, offset_of_type ofs T)

fun quintuple_for_scope code_type code_term code_string
        ({hol_ctxt = {ctxt = ctxt0, stds, ...}, card_assigns, bits, bisim_depth,
         datatypes, ...} : scope) =
  let
    val ctxt = set_show_all_types ctxt0
    val boring_Ts = [@{typ unsigned_bit}, @{typ signed_bit},
                     @{typ bisim_iterator}]
    val (iter_assigns, card_assigns) =
      card_assigns |> filter_out (member (op =) boring_Ts o fst)
                   |> List.partition (is_fp_iterator_type o fst)
    val (secondary_card_assigns, primary_card_assigns) =
      card_assigns
      |> List.partition ((is_integer_type orf is_datatype ctxt stds) o fst)
    val cards =
      map (fn (T, k) =>
              [code_type ctxt T, code_string (" = " ^ string_of_int k)])
    fun maxes () =
      maps (map_filter
                (fn {const, explicit_max, ...} =>
                    if explicit_max < 0 then
                      NONE
                    else
                      SOME [code_term ctxt (Const const),
                            code_string (" = " ^ string_of_int explicit_max)])
                 o #constrs) datatypes
    fun iters () =
      map (fn (T, k) =>
              [code_term ctxt (Const (const_for_iterator_type T)),
               code_string (" = " ^ string_of_int (k - 1))]) iter_assigns
    fun miscs () =
      (if bits = 0 then []
       else [code_string ("bits = " ^ string_of_int bits)]) @
      (if bisim_depth < 0 andalso forall (not o #co) datatypes then []
       else [code_string ("bisim_depth = " ^ signed_string_of_int bisim_depth)])
  in
    (cards primary_card_assigns, cards secondary_card_assigns,
     maxes (), iters (), miscs ())
  end

fun pretties_for_scope scope verbose =
  let
    fun standard_blocks s = map (Pretty.block o cons (Pretty.str (s ^ " ")))
    val (primary_cards, secondary_cards, maxes, iters, miscs) =
      quintuple_for_scope (pretty_maybe_quote oo pretty_for_type)
                          (pretty_maybe_quote oo Syntax.pretty_term)
                          Pretty.str scope
  in
    standard_blocks "card" primary_cards @
    (if verbose then
       standard_blocks "card" secondary_cards @
       standard_blocks "max" maxes @
       standard_blocks "iter" iters @
       miscs
     else
       [])
    |> pretty_serial_commas "and"
  end

fun multiline_string_for_scope scope =
  let
    val (primary_cards, secondary_cards, maxes, iters, miscs) =
      quintuple_for_scope Syntax.string_of_typ Syntax.string_of_term I scope
    val cards = primary_cards @ secondary_cards
  in
    case (if null cards then [] else ["card: " ^ commas (map implode cards)]) @
         (if null maxes then [] else ["max: " ^ commas (map implode maxes)]) @
         (if null iters then [] else ["iter: " ^ commas (map implode iters)]) @
         miscs of
      [] => "empty"
    | lines => space_implode "\n" lines
  end

fun scopes_equivalent (s1 : scope, s2 : scope) =
  #datatypes s1 = #datatypes s2 andalso #card_assigns s1 = #card_assigns s2
fun scope_less_eq (s1 : scope) (s2 : scope) =
  (s1, s2) |> pairself (map snd o #card_assigns) |> op ~~ |> forall (op <=)

fun rank_of_row (_, ks) = length ks
fun rank_of_block block = fold Integer.max (map rank_of_row block) 1
fun project_row _ (y, []) = (y, [1]) (* desperate measure *)
  | project_row column (y, ks) = (y, [nth ks (Int.min (column, length ks - 1))])
fun project_block (column, block) = map (project_row column) block

fun lookup_ints_assign eq assigns key =
  case triple_lookup eq assigns key of
    SOME ks => ks
  | NONE => raise ARG ("Nitpick_Scope.lookup_ints_assign", "")
fun lookup_type_ints_assign thy assigns T =
  map (Integer.max 1) (lookup_ints_assign (type_match thy) assigns T)
  handle ARG ("Nitpick_Scope.lookup_ints_assign", _) =>
         raise TYPE ("Nitpick_Scope.lookup_type_ints_assign", [T], [])
fun lookup_const_ints_assign thy assigns x =
  lookup_ints_assign (const_match thy) assigns x
  handle ARG ("Nitpick_Scope.lookup_ints_assign", _) =>
         raise TERM ("Nitpick_Scope.lookup_const_ints_assign", [Const x])

fun row_for_constr thy maxes_assigns constr =
  SOME (Max constr, lookup_const_ints_assign thy maxes_assigns constr)
  handle TERM ("lookup_const_ints_assign", _) => NONE

val max_bits = 31 (* Kodkod limit *)

fun block_for_type (hol_ctxt as {thy, ...}) binarize cards_assigns maxes_assigns
                   iters_assigns bitss bisim_depths T =
  case T of
    @{typ unsigned_bit} =>
    [(Card T, map (Integer.min max_bits o Integer.max 1) bitss)]
  | @{typ signed_bit} =>
    [(Card T, map (Integer.add 1 o Integer.min max_bits o Integer.max 1) bitss)]
  | @{typ "unsigned_bit word"} =>
    [(Card T, lookup_type_ints_assign thy cards_assigns nat_T)]
  | @{typ "signed_bit word"} =>
    [(Card T, lookup_type_ints_assign thy cards_assigns int_T)]
  | @{typ bisim_iterator} =>
    [(Card T, map (Integer.add 1 o Integer.max 0) bisim_depths)]
  | _ =>
    if is_fp_iterator_type T then
      [(Card T, map (Integer.add 1 o Integer.max 0)
                    (lookup_const_ints_assign thy iters_assigns
                                              (const_for_iterator_type T)))]
    else
      (Card T, lookup_type_ints_assign thy cards_assigns T) ::
      (case binarized_and_boxed_datatype_constrs hol_ctxt binarize T of
         [_] => []
       | constrs => map_filter (row_for_constr thy maxes_assigns) constrs)

fun blocks_for_types hol_ctxt binarize cards_assigns maxes_assigns iters_assigns
                     bitss bisim_depths mono_Ts nonmono_Ts =
  let
    val block_for = block_for_type hol_ctxt binarize cards_assigns maxes_assigns
                                   iters_assigns bitss bisim_depths
    val mono_block = maps block_for mono_Ts
    val nonmono_blocks = map block_for nonmono_Ts
  in mono_block :: nonmono_blocks end

val sync_threshold = 5
val linearity = 5

val all_combinations_ordered_smartly =
  let
    fun cost [] = 0
      | cost [k] = k
      | cost (k :: ks) =
        if k < sync_threshold andalso forall (curry (op =) k) ks then
          k - sync_threshold
        else
          k :: ks |> map (fn k => (k + linearity) * (k + linearity))
                  |> Integer.sum
  in
    all_combinations #> map (`cost) #> sort (int_ord o pairself fst) #> map snd
  end

fun is_self_recursive_constr_type T =
  exists (exists_subtype (curry (op =) (body_type T))) (binder_types T)

fun constr_max maxes x = the_default ~1 (AList.lookup (op =) maxes x)

type scope_desc = (typ * int) list * (styp * int) list

fun is_surely_inconsistent_card_assign hol_ctxt binarize
                                       (card_assigns, max_assigns) (T, k) =
  case binarized_and_boxed_datatype_constrs hol_ctxt binarize T of
    [] => false
  | xs =>
    let
      val dom_cards =
        map (Integer.prod o map (bounded_card_of_type k ~1 card_assigns)
             o binder_types o snd) xs
      val maxes = map (constr_max max_assigns) xs
      fun effective_max card ~1 = card
        | effective_max card max = Int.min (card, max)
      val max = map2 effective_max dom_cards maxes |> Integer.sum
    in max < k end
fun is_surely_inconsistent_scope_description hol_ctxt binarize seen rest
                                             max_assigns =
  exists (is_surely_inconsistent_card_assign hol_ctxt binarize
                                             (seen @ rest, max_assigns)) seen

fun repair_card_assigns hol_ctxt binarize (card_assigns, max_assigns) =
  let
    fun aux seen [] = SOME seen
      | aux _ ((_, 0) :: _) = NONE
      | aux seen ((T, k) :: rest) =
        (if is_surely_inconsistent_scope_description hol_ctxt binarize
                ((T, k) :: seen) rest max_assigns then
           raise SAME ()
         else
           case aux ((T, k) :: seen) rest of
             SOME assigns => SOME assigns
           | NONE => raise SAME ())
        handle SAME () => aux seen ((T, k - 1) :: rest)
  in aux [] (rev card_assigns) end

fun repair_iterator_assign ctxt assigns (T as Type (_, Ts), k) =
    (T, if T = @{typ bisim_iterator} then
          let
            val co_cards = map snd (filter (is_codatatype ctxt o fst) assigns)
          in Int.min (k, Integer.sum co_cards) end
        else if is_fp_iterator_type T then
          case Ts of
            [] => 1
          | _ => bounded_card_of_type k ~1 assigns (foldr1 HOLogic.mk_prodT Ts)
        else
          k)
  | repair_iterator_assign _ _ assign = assign

fun add_row_to_scope_descriptor (kind, ks) (card_assigns, max_assigns) =
  case kind of
    Card T => ((T, the_single ks) :: card_assigns, max_assigns)
  | Max x => (card_assigns, (x, the_single ks) :: max_assigns)
fun scope_descriptor_from_block block =
  fold_rev add_row_to_scope_descriptor block ([], [])
fun scope_descriptor_from_combination (hol_ctxt as {ctxt, ...}) binarize blocks
                                      columns =
  let
    val (card_assigns, max_assigns) =
      maps project_block (columns ~~ blocks) |> scope_descriptor_from_block
  in
    (card_assigns, max_assigns)
    |> repair_card_assigns hol_ctxt binarize
    |> Option.map
           (fn card_assigns =>
               (map (repair_iterator_assign ctxt card_assigns) card_assigns,
                max_assigns))
  end

fun offset_table_for_card_assigns dtypes assigns =
  let
    fun aux next _ [] = Typtab.update_new (dummyT, next)
      | aux next reusable ((T, k) :: assigns) =
        if k = 1 orelse is_asymmetric_nondatatype T then
          aux next reusable assigns
        else if length (these (Option.map #constrs (datatype_spec dtypes T)))
                > 1 then
          Typtab.update_new (T, next) #> aux (next + k) reusable assigns
        else
          case AList.lookup (op =) reusable k of
            SOME j0 => Typtab.update_new (T, j0) #> aux next reusable assigns
          | NONE => Typtab.update_new (T, next)
                    #> aux (next + k) ((k, next) :: reusable) assigns
  in Typtab.empty |> aux 0 [] assigns end

fun domain_card max card_assigns =
  Integer.prod o map (bounded_card_of_type max max card_assigns) o binder_types

fun add_constr_spec (card_assigns, max_assigns) acyclic card sum_dom_cards
                    num_self_recs num_non_self_recs (self_rec, x as (_, T))
                    constrs =
  let
    val max = constr_max max_assigns x
    fun next_delta () = if null constrs then 0 else #epsilon (hd constrs)
    val {delta, epsilon, exclusive, total} =
      if max = 0 then
        let val delta = next_delta () in
          {delta = delta, epsilon = delta, exclusive = true, total = false}
        end
      else if num_self_recs > 0 then
        (if num_non_self_recs = 1 then
           if self_rec then
             case List.last constrs of
               {delta = 0, epsilon = 1, exclusive = true, ...} =>
               {delta = 1, epsilon = card, exclusive = (num_self_recs = 1),
                total = false}
             | _ => raise SAME ()
           else
             if domain_card 2 card_assigns T = 1 then
               {delta = 0, epsilon = 1, exclusive = acyclic, total = acyclic}
             else
               raise SAME ()
         else
           raise SAME ())
        handle SAME () =>
               {delta = 0, epsilon = card, exclusive = false, total = false}
      else if card = sum_dom_cards (card + 1) then
        let val delta = next_delta () in
          {delta = delta, epsilon = delta + domain_card card card_assigns T,
           exclusive = true, total = true}
        end
      else
        {delta = 0, epsilon = card,
         exclusive = (num_self_recs + num_non_self_recs = 1), total = false}
  in
    {const = x, delta = delta, epsilon = epsilon, exclusive = exclusive,
     explicit_max = max, total = total} :: constrs
  end

fun has_exact_card hol_ctxt facto finitizable_dataTs card_assigns T =
  let val card = card_of_type card_assigns T in
    card = bounded_exact_card_of_type hol_ctxt
               (if facto then finitizable_dataTs else []) (card + 1) 0
               card_assigns T
  end

fun datatype_spec_from_scope_descriptor (hol_ctxt as {thy, ctxt, stds, ...})
        binarize deep_dataTs finitizable_dataTs (desc as (card_assigns, _))
        (T, card) =
  let
    val deep = member (op =) deep_dataTs T
    val co = is_codatatype ctxt T
    val standard = is_standard_datatype thy stds T
    val xs = binarized_and_boxed_datatype_constrs hol_ctxt binarize T
    val self_recs = map (is_self_recursive_constr_type o snd) xs
    val (num_self_recs, num_non_self_recs) =
      List.partition I self_recs |> pairself length
    val self_rec = num_self_recs > 0
    fun is_complete facto =
      has_exact_card hol_ctxt facto finitizable_dataTs card_assigns T
    fun is_concrete facto =
      is_word_type T orelse
      (* FIXME: looks wrong other types than just functions might be
         abstract. "is_complete" is also suspicious. *)
      xs |> maps (binder_types o snd) |> maps binder_types
         |> forall (has_exact_card hol_ctxt facto finitizable_dataTs
                                   card_assigns)
    val complete = pair_from_fun is_complete
    val concrete = pair_from_fun is_concrete
    fun sum_dom_cards max =
      map (domain_card max card_assigns o snd) xs |> Integer.sum
    val constrs =
      fold_rev (add_constr_spec desc (not co andalso standard) card
                                sum_dom_cards num_self_recs num_non_self_recs)
               (sort (bool_ord o swap o pairself fst) (self_recs ~~ xs)) []
  in
    {typ = T, card = card, co = co, standard = standard, self_rec = self_rec,
     complete = complete, concrete = concrete, deep = deep, constrs = constrs}
  end

fun scope_from_descriptor (hol_ctxt as {ctxt, stds, ...}) binarize deep_dataTs
                          finitizable_dataTs (desc as (card_assigns, _)) =
  let
    val datatypes =
      map (datatype_spec_from_scope_descriptor hol_ctxt binarize deep_dataTs
                                               finitizable_dataTs desc)
          (filter (is_datatype ctxt stds o fst) card_assigns)
    val bits = card_of_type card_assigns @{typ signed_bit} - 1
               handle TYPE ("Nitpick_HOL.card_of_type", _, _) =>
                      card_of_type card_assigns @{typ unsigned_bit}
                      handle TYPE ("Nitpick_HOL.card_of_type", _, _) => 0
    val bisim_depth = card_of_type card_assigns @{typ bisim_iterator} - 1
  in
    {hol_ctxt = hol_ctxt, binarize = binarize, card_assigns = card_assigns,
     datatypes = datatypes, bits = bits, bisim_depth = bisim_depth,
     ofs = offset_table_for_card_assigns datatypes card_assigns}
  end

fun repair_cards_assigns_wrt_boxing_etc _ _ [] = []
  | repair_cards_assigns_wrt_boxing_etc thy Ts ((SOME T, ks) :: cards_assigns) =
    (if is_fun_type T orelse is_pair_type T then
       Ts |> filter (curry (type_match thy o swap) T) |> map (rpair ks o SOME)
     else
       [(SOME T, ks)]) @
       repair_cards_assigns_wrt_boxing_etc thy Ts cards_assigns
  | repair_cards_assigns_wrt_boxing_etc thy Ts ((NONE, ks) :: cards_assigns) =
    (NONE, ks) :: repair_cards_assigns_wrt_boxing_etc thy Ts cards_assigns

val max_scopes = 5000
val distinct_threshold = 1000

fun all_scopes (hol_ctxt as {thy, ...}) binarize cards_assigns maxes_assigns
               iters_assigns bitss bisim_depths mono_Ts nonmono_Ts deep_dataTs
               finitizable_dataTs =
  let
    val cards_assigns =
      repair_cards_assigns_wrt_boxing_etc thy mono_Ts cards_assigns
    val blocks =
      blocks_for_types hol_ctxt binarize cards_assigns maxes_assigns
                       iters_assigns bitss bisim_depths mono_Ts nonmono_Ts
    val ranks = map rank_of_block blocks
    val all = all_combinations_ordered_smartly (map (rpair 0) ranks)
    val head = take max_scopes all
    val descs =
      map_filter (scope_descriptor_from_combination hol_ctxt binarize blocks)
                 head
  in
    (length all - length head,
     descs |> length descs <= distinct_threshold ? distinct (op =)
           |> map (scope_from_descriptor hol_ctxt binarize deep_dataTs
                                         finitizable_dataTs))
  end

end;
