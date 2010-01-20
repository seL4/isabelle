(*  Title:      HOL/Tools/Nitpick/nitpick_kodkod.ML
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   2008, 2009

Kodkod problem generator part of Kodkod.
*)

signature NITPICK_KODKOD =
sig
  type extended_context = Nitpick_HOL.extended_context
  type dtype_spec = Nitpick_Scope.dtype_spec
  type kodkod_constrs = Nitpick_Peephole.kodkod_constrs
  type nut = Nitpick_Nut.nut
  type nfa_transition = Kodkod.rel_expr * typ
  type nfa_entry = typ * nfa_transition list
  type nfa_table = nfa_entry list

  structure NameTable : TABLE

  val univ_card :
    int -> int -> int -> Kodkod.bound list -> Kodkod.formula -> int
  val check_bits : int -> Kodkod.formula -> unit
  val check_arity : int -> int -> unit
  val kk_tuple : bool -> int -> int list -> Kodkod.tuple
  val tuple_set_from_atom_schema : (int * int) list -> Kodkod.tuple_set
  val sequential_int_bounds : int -> Kodkod.int_bound list
  val pow_of_two_int_bounds : int -> int -> int -> Kodkod.int_bound list
  val bounds_for_built_in_rels_in_formula :
    bool -> int -> int -> int -> int -> Kodkod.formula -> Kodkod.bound list
  val bound_for_plain_rel : Proof.context -> bool -> nut -> Kodkod.bound
  val bound_for_sel_rel :
    Proof.context -> bool -> dtype_spec list -> nut -> Kodkod.bound
  val merge_bounds : Kodkod.bound list -> Kodkod.bound list
  val declarative_axiom_for_plain_rel : kodkod_constrs -> nut -> Kodkod.formula
  val declarative_axioms_for_datatypes :
    extended_context -> int -> int Typtab.table -> kodkod_constrs
    -> nut NameTable.table -> dtype_spec list -> Kodkod.formula list
  val kodkod_formula_from_nut :
    int -> int Typtab.table -> bool -> kodkod_constrs -> nut -> Kodkod.formula
end;

structure Nitpick_Kodkod : NITPICK_KODKOD =
struct

open Nitpick_Util
open Nitpick_HOL
open Nitpick_Scope
open Nitpick_Peephole
open Nitpick_Rep
open Nitpick_Nut

structure KK = Kodkod

type nfa_transition = KK.rel_expr * typ
type nfa_entry = typ * nfa_transition list
type nfa_table = nfa_entry list

structure NfaGraph = Graph(type key = typ val ord = TermOrd.typ_ord)

(* int -> KK.int_expr list *)
fun flip_nums n = index_seq 1 n @ [0] |> map KK.Num

(* int -> int -> int -> KK.bound list -> KK.formula -> int *)
fun univ_card nat_card int_card main_j0 bounds formula =
  let
    (* KK.rel_expr -> int -> int *)
    fun rel_expr_func r k =
      Int.max (k, case r of
                    KK.Atom j => j + 1
                  | KK.AtomSeq (k', j0) => j0 + k'
                  | _ => 0)
    (* KK.tuple -> int -> int *)
    fun tuple_func t k =
      case t of
        KK.Tuple js => fold Integer.max (map (Integer.add 1) js) k
      | _ => k
    (* KK.tuple_set -> int -> int *)
    fun tuple_set_func ts k =
      Int.max (k, case ts of KK.TupleAtomSeq (k', j0) => j0 + k' | _ => 0)
    val expr_F = {formula_func = K I, rel_expr_func = rel_expr_func,
                  int_expr_func = K I}
    val tuple_F = {tuple_func = tuple_func, tuple_set_func = tuple_set_func}
    val card = fold (KK.fold_bound expr_F tuple_F) bounds 1
               |> KK.fold_formula expr_F formula
  in Int.max (main_j0 + fold Integer.max [2, nat_card, int_card] 0, card) end

(* int -> KK.formula -> unit *)
fun check_bits bits formula =
  let
    (* KK.int_expr -> unit -> unit *)
    fun int_expr_func (KK.Num k) () =
        if is_twos_complement_representable bits k then
          ()
        else
          raise TOO_SMALL ("Nitpick_Kodkod.check_bits",
                           "\"bits\" value " ^ string_of_int bits ^
                           " too small for problem")
      | int_expr_func _ () = ()
    val expr_F = {formula_func = K I, rel_expr_func = K I,
                  int_expr_func = int_expr_func}
  in KK.fold_formula expr_F formula () end

(* int -> int -> unit *)
fun check_arity univ_card n =
  if n > KK.max_arity univ_card then
    raise TOO_LARGE ("Nitpick_Kodkod.check_arity",
                     "arity " ^ string_of_int n ^ " too large for universe of \
                     \cardinality " ^ string_of_int univ_card)
  else
    ()

(* bool -> int -> int list -> KK.tuple *)
fun kk_tuple debug univ_card js =
  if debug then
    KK.Tuple js
  else
    KK.TupleIndex (length js,
                   fold (fn j => fn accum => accum * univ_card + j) js 0)

(* (int * int) list -> KK.tuple_set *)
val tuple_set_from_atom_schema = foldl1 KK.TupleProduct o map KK.TupleAtomSeq
(* rep -> KK.tuple_set *)
val upper_bound_for_rep = tuple_set_from_atom_schema o atom_schema_of_rep

(* int -> KK.tuple_set *)
val single_atom = KK.TupleSet o single o KK.Tuple o single
(* int -> KK.int_bound list *)
fun sequential_int_bounds n = [(NONE, map single_atom (index_seq 0 n))]
(* int -> int -> KK.int_bound list *)
fun pow_of_two_int_bounds bits j0 univ_card =
  let
    (* int -> int -> int -> KK.int_bound list *)
    fun aux 0  _ _ = []
      | aux 1 pow_of_two j =
        if j < univ_card then [(SOME (~ pow_of_two), [single_atom j])] else []
      | aux iter pow_of_two j =
        (SOME pow_of_two, [single_atom j]) ::
        aux (iter - 1) (2 * pow_of_two) (j + 1)
  in aux (bits + 1) 1 j0 end

(* KK.formula -> KK.n_ary_index list *)
fun built_in_rels_in_formula formula =
  let
    (* KK.rel_expr -> KK.n_ary_index list -> KK.n_ary_index list *)
    fun rel_expr_func (r as KK.Rel (x as (n, j))) =
        if x = unsigned_bit_word_sel_rel orelse x = signed_bit_word_sel_rel then
          I
        else
          (case AList.lookup (op =) (#rels initial_pool) n of
             SOME k => j < k ? insert (op =) x
           | NONE => I)
      | rel_expr_func _ = I
    val expr_F = {formula_func = K I, rel_expr_func = rel_expr_func,
                  int_expr_func = K I}
  in KK.fold_formula expr_F formula [] end

val max_table_size = 65536

(* int -> unit *)
fun check_table_size k =
  if k > max_table_size then
    raise TOO_LARGE ("Nitpick_Kodkod.check_table_size",
                     "precomputed table too large (" ^ string_of_int k ^ ")")
  else
    ()

(* bool -> int -> int * int -> (int -> int) -> KK.tuple list *)
fun tabulate_func1 debug univ_card (k, j0) f =
  (check_table_size k;
   map_filter (fn j1 => let val j2 = f j1 in
                          if j2 >= 0 then
                            SOME (kk_tuple debug univ_card [j1 + j0, j2 + j0])
                          else
                            NONE
                        end) (index_seq 0 k))
(* bool -> int -> int * int -> int -> (int * int -> int) -> KK.tuple list *)
fun tabulate_op2 debug univ_card (k, j0) res_j0 f =
  (check_table_size (k * k);
   map_filter (fn j => let
                         val j1 = j div k
                         val j2 = j - j1 * k
                         val j3 = f (j1, j2)
                       in
                         if j3 >= 0 then
                           SOME (kk_tuple debug univ_card
                                          [j1 + j0, j2 + j0, j3 + res_j0])
                         else
                           NONE
                       end) (index_seq 0 (k * k)))
(* bool -> int -> int * int -> int -> (int * int -> int * int)
   -> KK.tuple list *)
fun tabulate_op2_2 debug univ_card (k, j0) res_j0 f =
  (check_table_size (k * k);
   map_filter (fn j => let
                         val j1 = j div k
                         val j2 = j - j1 * k
                         val (j3, j4) = f (j1, j2)
                       in
                         if j3 >= 0 andalso j4 >= 0 then
                           SOME (kk_tuple debug univ_card
                                          [j1 + j0, j2 + j0, j3 + res_j0,
                                           j4 + res_j0])
                         else
                           NONE
                       end) (index_seq 0 (k * k)))
(* bool -> int -> int * int -> (int * int -> int) -> KK.tuple list *)
fun tabulate_nat_op2 debug univ_card (k, j0) f =
  tabulate_op2 debug univ_card (k, j0) j0 (atom_for_nat (k, 0) o f)
fun tabulate_int_op2 debug univ_card (k, j0) f =
  tabulate_op2 debug univ_card (k, j0) j0
               (atom_for_int (k, 0) o f o pairself (int_for_atom (k, 0)))
(* bool -> int -> int * int -> (int * int -> int * int) -> KK.tuple list *)
fun tabulate_int_op2_2 debug univ_card (k, j0) f =
  tabulate_op2_2 debug univ_card (k, j0) j0
                 (pairself (atom_for_int (k, 0)) o f
                  o pairself (int_for_atom (k, 0)))

(* int * int -> int *)
fun isa_div (m, n) = m div n handle General.Div => 0
fun isa_mod (m, n) = m mod n handle General.Div => m
fun isa_gcd (m, 0) = m
  | isa_gcd (m, n) = isa_gcd (n, isa_mod (m, n))
fun isa_lcm (m, n) = isa_div (m * n, isa_gcd (m, n))
val isa_zgcd = isa_gcd o pairself abs
(* int * int -> int * int *)
fun isa_norm_frac (m, n) =
  if n < 0 then isa_norm_frac (~m, ~n)
  else if m = 0 orelse n = 0 then (0, 1)
  else let val p = isa_zgcd (m, n) in (isa_div (m, p), isa_div (n, p)) end

(* bool -> int -> int -> int -> int -> int * int
   -> string * bool * KK.tuple list *)
fun tabulate_built_in_rel debug univ_card nat_card int_card j0 (x as (n, _)) =
  (check_arity univ_card n;
   if x = not3_rel then
     ("not3", tabulate_func1 debug univ_card (2, j0) (curry (op -) 1))
   else if x = suc_rel then
     ("suc", tabulate_func1 debug univ_card (univ_card - j0 - 1, j0)
                            (Integer.add 1))
   else if x = nat_add_rel then
     ("nat_add", tabulate_nat_op2 debug univ_card (nat_card, j0) (op +))
   else if x = int_add_rel then
     ("int_add", tabulate_int_op2 debug univ_card (int_card, j0) (op +))
   else if x = nat_subtract_rel then
     ("nat_subtract",
      tabulate_op2 debug univ_card (nat_card, j0) j0 (uncurry nat_minus))
   else if x = int_subtract_rel then
     ("int_subtract", tabulate_int_op2 debug univ_card (int_card, j0) (op -))
   else if x = nat_multiply_rel then
     ("nat_multiply", tabulate_nat_op2 debug univ_card (nat_card, j0) (op * ))
   else if x = int_multiply_rel then
     ("int_multiply", tabulate_int_op2 debug univ_card (int_card, j0) (op * ))
   else if x = nat_divide_rel then
     ("nat_divide", tabulate_nat_op2 debug univ_card (nat_card, j0) isa_div)
   else if x = int_divide_rel then
     ("int_divide", tabulate_int_op2 debug univ_card (int_card, j0) isa_div)
   else if x = nat_less_rel then
     ("nat_less", tabulate_nat_op2 debug univ_card (nat_card, j0)
                                   (int_for_bool o op <))
   else if x = int_less_rel then
     ("int_less", tabulate_int_op2 debug univ_card (int_card, j0)
                                   (int_for_bool o op <))
   else if x = gcd_rel then
     ("gcd", tabulate_nat_op2 debug univ_card (nat_card, j0) isa_gcd)
   else if x = lcm_rel then
     ("lcm", tabulate_nat_op2 debug univ_card (nat_card, j0) isa_lcm)
   else if x = norm_frac_rel then
     ("norm_frac", tabulate_int_op2_2 debug univ_card (int_card, j0)
                                      isa_norm_frac)
   else
     raise ARG ("Nitpick_Kodkod.tabulate_built_in_rel", "unknown relation"))

(* bool -> int -> int -> int -> int -> int * int -> KK.rel_expr -> KK.bound *)
fun bound_for_built_in_rel debug univ_card nat_card int_card j0 x =
  let
    val (nick, ts) = tabulate_built_in_rel debug univ_card nat_card int_card
                                           j0 x
  in ([(x, nick)], [KK.TupleSet ts]) end

(* bool -> int -> int -> int -> int -> KK.formula -> KK.bound list *)
fun bounds_for_built_in_rels_in_formula debug univ_card nat_card int_card j0 =
  map (bound_for_built_in_rel debug univ_card nat_card int_card j0)
  o built_in_rels_in_formula

(* Proof.context -> bool -> string -> typ -> rep -> string *)
fun bound_comment ctxt debug nick T R =
  short_name nick ^
  (if debug then " :: " ^ plain_string_from_yxml (Syntax.string_of_typ ctxt T)
   else "") ^ " : " ^ string_for_rep R

(* Proof.context -> bool -> nut -> KK.bound *)
fun bound_for_plain_rel ctxt debug (u as FreeRel (x, T, R, nick)) =
    ([(x, bound_comment ctxt debug nick T R)],
     if nick = @{const_name bisim_iterator_max} then
       case R of
         Atom (k, j0) => [single_atom (k - 1 + j0)]
       | _ => raise NUT ("Nitpick_Kodkod.bound_for_plain_rel", [u])
     else
       [KK.TupleSet [], upper_bound_for_rep R])
  | bound_for_plain_rel _ _ u =
    raise NUT ("Nitpick_Kodkod.bound_for_plain_rel", [u])

(* Proof.context -> bool -> dtype_spec list -> nut -> KK.bound *)
fun bound_for_sel_rel ctxt debug dtypes
        (FreeRel (x, T as Type ("fun", [T1, T2]), R as Func (Atom (_, j0), R2),
                  nick)) =
    let
      val constr as {delta, epsilon, exclusive, explicit_max, ...} =
        constr_spec dtypes (original_name nick, T1)
    in
      ([(x, bound_comment ctxt debug nick T R)],
       if explicit_max = 0 then
         [KK.TupleSet []]
       else
         let val ts = KK.TupleAtomSeq (epsilon - delta, delta + j0) in
           if R2 = Formula Neut then
             [ts] |> not exclusive ? cons (KK.TupleSet [])
           else
             [KK.TupleSet [], KK.TupleProduct (ts, upper_bound_for_rep R2)]
         end)
    end
  | bound_for_sel_rel _ _ _ u =
    raise NUT ("Nitpick_Kodkod.bound_for_sel_rel", [u])

(* KK.bound list -> KK.bound list *)
fun merge_bounds bs =
  let
    (* KK.bound -> int *)
    fun arity (zs, _) = fst (fst (hd zs))
    (* KK.bound list -> KK.bound -> KK.bound list -> KK.bound list *)
    fun add_bound ds b [] = List.revAppend (ds, [b])
      | add_bound ds b (c :: cs) =
        if arity b = arity c andalso snd b = snd c then
          List.revAppend (ds, (fst c @ fst b, snd c) :: cs)
        else
          add_bound (c :: ds) b cs
  in fold (add_bound []) bs [] end

(* int -> int -> KK.rel_expr list *)
fun unary_var_seq j0 n = map (curry KK.Var 1) (index_seq j0 n)

(* int list -> KK.rel_expr *)
val singleton_from_combination = foldl1 KK.Product o map KK.Atom
(* rep -> KK.rel_expr list *)
fun all_singletons_for_rep R =
  if is_lone_rep R then
    all_combinations_for_rep R |> map singleton_from_combination
  else
    raise REP ("Nitpick_Kodkod.all_singletons_for_rep", [R])

(* KK.rel_expr -> KK.rel_expr list *)
fun unpack_products (KK.Product (r1, r2)) =
    unpack_products r1 @ unpack_products r2
  | unpack_products r = [r]
fun unpack_joins (KK.Join (r1, r2)) = unpack_joins r1 @ unpack_joins r2
  | unpack_joins r = [r]

(* rep -> KK.rel_expr *)
val empty_rel_for_rep = empty_n_ary_rel o arity_of_rep
fun full_rel_for_rep R =
  case atom_schema_of_rep R of
    [] => raise REP ("Nitpick_Kodkod.full_rel_for_rep", [R])
  | schema => foldl1 KK.Product (map KK.AtomSeq schema)

(* int -> int list -> KK.decl list *)
fun decls_for_atom_schema j0 schema =
  map2 (fn j => fn x => KK.DeclOne ((1, j), KK.AtomSeq x))
       (index_seq j0 (length schema)) schema

(* The type constraint below is a workaround for a Poly/ML bug. *)

(* kodkod_constrs -> rep -> KK.rel_expr -> KK.formula *)
fun d_n_ary_function ({kk_all, kk_join, kk_lone, kk_one, ...} : kodkod_constrs)
                     R r =
  let val body_R = body_rep R in
    if is_lone_rep body_R then
      let
        val binder_schema = atom_schema_of_reps (binder_reps R)
        val body_schema = atom_schema_of_rep body_R
        val one = is_one_rep body_R
        val opt_x = case r of KK.Rel x => SOME x | _ => NONE
      in
        if opt_x <> NONE andalso length binder_schema = 1 andalso
           length body_schema = 1 then
          (if one then KK.Function else KK.Functional)
              (the opt_x, KK.AtomSeq (hd binder_schema),
               KK.AtomSeq (hd body_schema))
        else
          let
            val decls = decls_for_atom_schema ~1 binder_schema
            val vars = unary_var_seq ~1 (length binder_schema)
            val kk_xone = if one then kk_one else kk_lone
          in kk_all decls (kk_xone (fold kk_join vars r)) end
      end
    else
      KK.True
  end
fun kk_n_ary_function kk R (r as KK.Rel x) =
    if not (is_opt_rep R) then
      if x = suc_rel then
        KK.False
      else if x = nat_add_rel then
        formula_for_bool (card_of_rep (body_rep R) = 1)
      else if x = nat_multiply_rel then
        formula_for_bool (card_of_rep (body_rep R) <= 2)
      else
        d_n_ary_function kk R r
    else if x = nat_subtract_rel then
      KK.True
    else
      d_n_ary_function kk R r
  | kk_n_ary_function kk R r = d_n_ary_function kk R r

(* kodkod_constrs -> KK.rel_expr list -> KK.formula *)
fun kk_disjoint_sets _ [] = KK.True
  | kk_disjoint_sets (kk as {kk_and, kk_no, kk_intersect, ...} : kodkod_constrs)
                     (r :: rs) =
    fold (kk_and o kk_no o kk_intersect r) rs (kk_disjoint_sets kk rs)

(* int -> kodkod_constrs -> (KK.rel_expr -> KK.rel_expr) -> KK.rel_expr
   -> KK.rel_expr *)
fun basic_rel_rel_let j ({kk_rel_let, ...} : kodkod_constrs) f r =
  if inline_rel_expr r then
    f r
  else
    let val x = (KK.arity_of_rel_expr r, j) in
      kk_rel_let [KK.AssignRelReg (x, r)] (f (KK.RelReg x))
    end
(* kodkod_constrs -> (KK.rel_expr -> KK.rel_expr) -> KK.rel_expr
   -> KK.rel_expr *)
val single_rel_rel_let = basic_rel_rel_let 0
(* kodkod_constrs -> (KK.rel_expr -> KK.rel_expr -> KK.rel_expr) -> KK.rel_expr
   -> KK.rel_expr -> KK.rel_expr *)
fun double_rel_rel_let kk f r1 r2 =
  single_rel_rel_let kk (fn r1 => basic_rel_rel_let 1 kk (f r1) r2) r1
(* kodkod_constrs -> (KK.rel_expr -> KK.rel_expr -> KK.rel_expr -> KK.rel_expr)
   -> KK.rel_expr -> KK.rel_expr -> KK.rel_expr -> KK.rel_expr *)
fun tripl_rel_rel_let kk f r1 r2 r3 =
  double_rel_rel_let kk
      (fn r1 => fn r2 => basic_rel_rel_let 2 kk (f r1 r2) r3) r1 r2

(* kodkod_constrs -> int -> KK.formula -> KK.rel_expr *)
fun atom_from_formula ({kk_rel_if, ...} : kodkod_constrs) j0 f =
  kk_rel_if f (KK.Atom (j0 + 1)) (KK.Atom j0)
(* kodkod_constrs -> rep -> KK.formula -> KK.rel_expr *)
fun rel_expr_from_formula kk R f =
  case unopt_rep R of
    Atom (2, j0) => atom_from_formula kk j0 f
  | _ => raise REP ("Nitpick_Kodkod.rel_expr_from_formula", [R])

(* kodkod_cotrs -> int -> int -> KK.rel_expr -> KK.rel_expr list *)
fun unpack_vect_in_chunks ({kk_project_seq, ...} : kodkod_constrs) chunk_arity
                          num_chunks r =
  List.tabulate (num_chunks, fn j => kk_project_seq r (j * chunk_arity)
                                                    chunk_arity)

(* kodkod_constrs -> bool -> rep -> rep -> KK.rel_expr -> KK.rel_expr
   -> KK.rel_expr *)
fun kk_n_fold_join
        (kk as {kk_intersect, kk_product, kk_join, kk_project_seq, ...}) one R1
        res_R r1 r2 =
  case arity_of_rep R1 of
    1 => kk_join r1 r2
  | arity1 =>
    let
      val unpacked_rs1 =
        if inline_rel_expr r1 then unpack_vect_in_chunks kk 1 arity1 r1
        else unpack_products r1
    in
      if one andalso length unpacked_rs1 = arity1 then
        fold kk_join unpacked_rs1 r2
      else
        kk_project_seq
            (kk_intersect (kk_product r1 (full_rel_for_rep res_R)) r2)
            arity1 (arity_of_rep res_R)
    end

(* kodkod_constrs -> rep -> rep -> KK.rel_expr -> KK.rel_expr list
   -> KK.rel_expr list -> KK.rel_expr *)
fun kk_case_switch (kk as {kk_union, kk_product, ...}) R1 R2 r rs1 rs2 =
  if rs1 = rs2 then r
  else kk_n_fold_join kk true R1 R2 r (fold1 kk_union (map2 kk_product rs1 rs2))

val lone_rep_fallback_max_card = 4096
val some_j0 = 0

(* kodkod_constrs -> rep -> rep -> KK.rel_expr -> KK.rel_expr *)
fun lone_rep_fallback kk new_R old_R r =
  if old_R = new_R then
    r
  else
    let val card = card_of_rep old_R in
      if is_lone_rep old_R andalso is_lone_rep new_R andalso
         card = card_of_rep new_R then
        if card >= lone_rep_fallback_max_card then
          raise TOO_LARGE ("Nitpick_Kodkod.lone_rep_fallback",
                           "too high cardinality (" ^ string_of_int card ^ ")")
        else
          kk_case_switch kk old_R new_R r (all_singletons_for_rep old_R)
                         (all_singletons_for_rep new_R)
      else
        raise REP ("Nitpick_Kodkod.lone_rep_fallback", [old_R, new_R])
    end
(* kodkod_constrs -> int * int -> rep -> KK.rel_expr -> KK.rel_expr *)
and atom_from_rel_expr kk (x as (k, j0)) old_R r =
  case old_R of
    Func (R1, R2) =>
    let
      val dom_card = card_of_rep R1
      val R2' = case R2 of Atom _ => R2 | _ => Atom (card_of_rep R2, some_j0)
    in
      atom_from_rel_expr kk x (Vect (dom_card, R2'))
                         (vect_from_rel_expr kk dom_card R2' old_R r)
    end
  | Opt _ => raise REP ("Nitpick_Kodkod.atom_from_rel_expr", [old_R])
  | _ => lone_rep_fallback kk (Atom x) old_R r
(* kodkod_constrs -> rep list -> rep -> KK.rel_expr -> KK.rel_expr *)
and struct_from_rel_expr kk Rs old_R r =
  case old_R of
    Atom _ => lone_rep_fallback kk (Struct Rs) old_R r
  | Struct Rs' =>
    let
      val Rs = filter (not_equal Unit) Rs
      val Rs' = filter (not_equal Unit) Rs'
    in
      if Rs' = Rs then
        r
      else if map card_of_rep Rs' = map card_of_rep Rs then
        let
          val old_arities = map arity_of_rep Rs'
          val old_offsets = offset_list old_arities
          val old_rs = map2 (#kk_project_seq kk r) old_offsets old_arities
        in
          fold1 (#kk_product kk)
                (map3 (rel_expr_from_rel_expr kk) Rs Rs' old_rs)
        end
      else
        lone_rep_fallback kk (Struct Rs) old_R r
    end
  | _ => raise REP ("Nitpick_Kodkod.struct_from_rel_expr", [old_R])
(* kodkod_constrs -> int -> rep -> rep -> KK.rel_expr -> KK.rel_expr *)
and vect_from_rel_expr kk k R old_R r =
  case old_R of
    Atom _ => lone_rep_fallback kk (Vect (k, R)) old_R r
  | Vect (k', R') =>
    if k = k' andalso R = R' then r
    else lone_rep_fallback kk (Vect (k, R)) old_R r
  | Func (R1, Formula Neut) =>
    if k = card_of_rep R1 then
      fold1 (#kk_product kk)
            (map (fn arg_r =>
                     rel_expr_from_formula kk R (#kk_subset kk arg_r r))
                 (all_singletons_for_rep R1))
    else
      raise REP ("Nitpick_Kodkod.vect_from_rel_expr", [old_R])
  | Func (Unit, R2) => rel_expr_from_rel_expr kk R R2 r
  | Func (R1, R2) =>
    fold1 (#kk_product kk)
          (map (fn arg_r =>
                   rel_expr_from_rel_expr kk R R2
                                         (kk_n_fold_join kk true R1 R2 arg_r r))
               (all_singletons_for_rep R1))
  | _ => raise REP ("Nitpick_Kodkod.vect_from_rel_expr", [old_R])
(* kodkod_constrs -> rep -> rep -> rep -> KK.rel_expr -> KK.rel_expr *)
and func_from_no_opt_rel_expr kk R1 R2 (Atom x) r =
    let
      val dom_card = card_of_rep R1
      val R2' = case R2 of Atom _ => R2 | _ => Atom (card_of_rep R2, some_j0)
    in
      func_from_no_opt_rel_expr kk R1 R2 (Vect (dom_card, R2'))
                                (vect_from_rel_expr kk dom_card R2' (Atom x) r)
    end
  | func_from_no_opt_rel_expr kk Unit R2 old_R r =
    (case old_R of
       Vect (k, R') => rel_expr_from_rel_expr kk R2 R' r
     | Func (Unit, R2') => rel_expr_from_rel_expr kk R2 R2' r
     | Func (Atom (1, _), Formula Neut) =>
       (case unopt_rep R2 of
          Atom (2, j0) => atom_from_formula kk j0 (#kk_some kk r)
        | _ => raise REP ("Nitpick_Kodkod.func_from_no_opt_rel_expr",
                          [old_R, Func (Unit, R2)]))
     | Func (R1', R2') =>
       rel_expr_from_rel_expr kk R2 R2' (#kk_project_seq kk r (arity_of_rep R1')
                              (arity_of_rep R2'))
     | _ => raise REP ("Nitpick_Kodkod.func_from_no_opt_rel_expr",
                       [old_R, Func (Unit, R2)]))
  | func_from_no_opt_rel_expr kk R1 (Formula Neut) old_R r =
    (case old_R of
       Vect (k, Atom (2, j0)) =>
       let
         val args_rs = all_singletons_for_rep R1
         val vals_rs = unpack_vect_in_chunks kk 1 k r
         (* KK.rel_expr -> KK.rel_expr -> KK.rel_expr *)
         fun empty_or_singleton_set_for arg_r val_r =
           #kk_join kk val_r (#kk_product kk (KK.Atom (j0 + 1)) arg_r)
       in
         fold1 (#kk_union kk) (map2 empty_or_singleton_set_for args_rs vals_rs)
       end
     | Func (R1', Formula Neut) =>
       if R1 = R1' then
         r
       else
         let
           val schema = atom_schema_of_rep R1
           val r1 = fold1 (#kk_product kk) (unary_var_seq ~1 (length schema))
                    |> rel_expr_from_rel_expr kk R1' R1
           val kk_xeq = (if is_one_rep R1' then #kk_subset else #kk_rel_eq) kk
         in
           #kk_comprehension kk (decls_for_atom_schema ~1 schema) (kk_xeq r1 r)
         end
     | Func (Unit, (Atom (2, j0))) =>
       #kk_rel_if kk (#kk_rel_eq kk r (KK.Atom (j0 + 1)))
                  (full_rel_for_rep R1) (empty_rel_for_rep R1)
     | Func (R1', Atom (2, j0)) =>
       func_from_no_opt_rel_expr kk R1 (Formula Neut)
           (Func (R1', Formula Neut)) (#kk_join kk r (KK.Atom (j0 + 1)))
     | _ => raise REP ("Nitpick_Kodkod.func_from_no_opt_rel_expr",
                       [old_R, Func (R1, Formula Neut)]))
  | func_from_no_opt_rel_expr kk R1 R2 old_R r =
    case old_R of
      Vect (k, R) =>
      let
        val args_rs = all_singletons_for_rep R1
        val vals_rs = unpack_vect_in_chunks kk (arity_of_rep R) k r
                      |> map (rel_expr_from_rel_expr kk R2 R)
      in fold1 (#kk_union kk) (map2 (#kk_product kk) args_rs vals_rs) end
    | Func (R1', Formula Neut) =>
      (case R2 of
         Atom (x as (2, j0)) =>
         let val schema = atom_schema_of_rep R1 in
           if length schema = 1 then
             #kk_override kk (#kk_product kk (KK.AtomSeq (hd schema))
                                             (KK.Atom j0))
                             (#kk_product kk r (KK.Atom (j0 + 1)))
           else
             let
               val r1 = fold1 (#kk_product kk) (unary_var_seq ~1 (length schema))
                        |> rel_expr_from_rel_expr kk R1' R1
               val r2 = KK.Var (1, ~(length schema) - 1)
               val r3 = atom_from_formula kk j0 (#kk_subset kk r1 r)
             in
               #kk_comprehension kk (decls_for_atom_schema ~1 (schema @ [x]))
                                 (#kk_subset kk r2 r3)
             end
           end
         | _ => raise REP ("Nitpick_Kodkod.func_from_no_opt_rel_expr",
                           [old_R, Func (R1, R2)]))
    | Func (Unit, R2') =>
      let val j0 = some_j0 in
        func_from_no_opt_rel_expr kk R1 R2 (Func (Atom (1, j0), R2'))
                                  (#kk_product kk (KK.Atom j0) r)
      end
    | Func (R1', R2') =>
      if R1 = R1' andalso R2 = R2' then
        r
      else
        let
          val dom_schema = atom_schema_of_rep R1
          val ran_schema = atom_schema_of_rep R2
          val dom_prod = fold1 (#kk_product kk)
                               (unary_var_seq ~1 (length dom_schema))
                         |> rel_expr_from_rel_expr kk R1' R1
          val ran_prod = fold1 (#kk_product kk)
                               (unary_var_seq (~(length dom_schema) - 1)
                                              (length ran_schema))
                         |> rel_expr_from_rel_expr kk R2' R2
          val app = kk_n_fold_join kk true R1' R2' dom_prod r
          val kk_xeq = (if is_one_rep R2' then #kk_subset else #kk_rel_eq) kk
        in
          #kk_comprehension kk (decls_for_atom_schema ~1
                                                      (dom_schema @ ran_schema))
                               (kk_xeq ran_prod app)
        end
    | _ => raise REP ("Nitpick_Kodkod.func_from_no_opt_rel_expr",
                      [old_R, Func (R1, R2)])
(* kodkod_constrs -> rep -> rep -> KK.rel_expr -> KK.rel_expr *)
and rel_expr_from_rel_expr kk new_R old_R r =
  let
    val unopt_old_R = unopt_rep old_R
    val unopt_new_R = unopt_rep new_R
  in
    if unopt_old_R <> old_R andalso unopt_new_R = new_R then
      raise REP ("Nitpick_Kodkod.rel_expr_from_rel_expr", [old_R, new_R])
    else if unopt_new_R = unopt_old_R then
      r
    else
      (case unopt_new_R of
         Atom x => atom_from_rel_expr kk x
       | Struct Rs => struct_from_rel_expr kk Rs
       | Vect (k, R') => vect_from_rel_expr kk k R'
       | Func (R1, R2) => func_from_no_opt_rel_expr kk R1 R2
       | _ => raise REP ("Nitpick_Kodkod.rel_expr_from_rel_expr",
                         [old_R, new_R]))
          unopt_old_R r
  end
(* kodkod_constrs -> rep -> rep -> rep -> KK.rel_expr -> KK.rel_expr *)
and rel_expr_to_func kk R1 R2 = rel_expr_from_rel_expr kk (Func (R1, R2))

(* kodkod_constrs -> typ -> KK.rel_expr -> KK.rel_expr *)
fun bit_set_from_atom ({kk_join, ...} : kodkod_constrs) T r =
  kk_join r (KK.Rel (if T = @{typ "unsigned_bit word"} then
                       unsigned_bit_word_sel_rel
                     else
                       signed_bit_word_sel_rel))
(* kodkod_constrs -> typ -> KK.rel_expr -> KK.int_expr *)
val int_expr_from_atom = KK.SetSum ooo bit_set_from_atom
(* kodkod_constrs -> typ -> rep -> KK.int_expr -> KK.rel_expr *)
fun atom_from_int_expr (kk as {kk_rel_eq, kk_comprehension, ...}
                        : kodkod_constrs) T R i =
  kk_comprehension (decls_for_atom_schema ~1 (atom_schema_of_rep R))
                   (kk_rel_eq (bit_set_from_atom kk T (KK.Var (1, ~1)))
                              (KK.Bits i))

(* kodkod_constrs -> nut -> KK.formula *)
fun declarative_axiom_for_plain_rel kk (FreeRel (x, _, R as Func _, nick)) =
    kk_n_ary_function kk (R |> nick = @{const_name List.set} ? unopt_rep)
                      (KK.Rel x)
  | declarative_axiom_for_plain_rel ({kk_lone, kk_one, ...} : kodkod_constrs)
                                    (FreeRel (x, _, R, _)) =
    if is_one_rep R then kk_one (KK.Rel x)
    else if is_lone_rep R andalso card_of_rep R > 1 then kk_lone (KK.Rel x)
    else KK.True
  | declarative_axiom_for_plain_rel _ u =
    raise NUT ("Nitpick_Kodkod.declarative_axiom_for_plain_rel", [u])

(* nut NameTable.table -> styp -> KK.rel_expr * rep * int *)
fun const_triple rel_table (x as (s, T)) =
  case the_name rel_table (ConstName (s, T, Any)) of
    FreeRel ((n, j), _, R, _) => (KK.Rel (n, j), R, n)
  | _ => raise TERM ("Nitpick_Kodkod.const_triple", [Const x])

(* nut NameTable.table -> styp -> KK.rel_expr *)
fun discr_rel_expr rel_table = #1 o const_triple rel_table o discr_for_constr

(* extended_context -> kodkod_constrs -> nut NameTable.table -> dtype_spec list
   -> styp -> int -> nfa_transition list *)
fun nfa_transitions_for_sel ext_ctxt ({kk_project, ...} : kodkod_constrs)
                            rel_table (dtypes : dtype_spec list) constr_x n =
  let
    val x as (_, T) = boxed_nth_sel_for_constr ext_ctxt constr_x n
    val (r, R, arity) = const_triple rel_table x
    val type_schema = type_schema_of_rep T R
  in
    map_filter (fn (j, T) =>
                   if forall (not_equal T o #typ) dtypes then NONE
                   else SOME (kk_project r (map KK.Num [0, j]), T))
               (index_seq 1 (arity - 1) ~~ tl type_schema)
  end
(* extended_context -> kodkod_constrs -> nut NameTable.table -> dtype_spec list
   -> styp -> nfa_transition list *)
fun nfa_transitions_for_constr ext_ctxt kk rel_table dtypes (x as (_, T)) =
  maps (nfa_transitions_for_sel ext_ctxt kk rel_table dtypes x)
       (index_seq 0 (num_sels_for_constr_type T))
(* extended_context -> kodkod_constrs -> nut NameTable.table -> dtype_spec list
   -> dtype_spec -> nfa_entry option *)
fun nfa_entry_for_datatype _ _ _ _ ({co = true, ...} : dtype_spec) = NONE
  | nfa_entry_for_datatype _ _ _ _ {shallow = true, ...} = NONE
  | nfa_entry_for_datatype ext_ctxt kk rel_table dtypes {typ, constrs, ...} =
    SOME (typ, maps (nfa_transitions_for_constr ext_ctxt kk rel_table dtypes
                     o #const) constrs)

val empty_rel = KK.Product (KK.None, KK.None)

(* nfa_table -> typ -> typ -> KK.rel_expr list *)
fun direct_path_rel_exprs nfa start final =
  case AList.lookup (op =) nfa final of
    SOME trans => map fst (filter (curry (op =) start o snd) trans)
  | NONE => []
(* kodkod_constrs -> nfa_table -> typ list -> typ -> typ -> KK.rel_expr *)
and any_path_rel_expr ({kk_union, ...} : kodkod_constrs) nfa [] start final =
    fold kk_union (direct_path_rel_exprs nfa start final)
         (if start = final then KK.Iden else empty_rel)
  | any_path_rel_expr (kk as {kk_union, ...}) nfa (q :: qs) start final =
    kk_union (any_path_rel_expr kk nfa qs start final)
             (knot_path_rel_expr kk nfa qs start q final)
(* kodkod_constrs -> nfa_table -> typ list -> typ -> typ -> typ
   -> KK.rel_expr *)
and knot_path_rel_expr (kk as {kk_join, kk_reflexive_closure, ...}) nfa qs start
                       knot final =
  kk_join (kk_join (any_path_rel_expr kk nfa qs knot final)
                   (kk_reflexive_closure (loop_path_rel_expr kk nfa qs knot)))
          (any_path_rel_expr kk nfa qs start knot)
(* kodkod_constrs -> nfa_table -> typ list -> typ -> KK.rel_expr *)
and loop_path_rel_expr ({kk_union, ...} : kodkod_constrs) nfa [] start =
    fold kk_union (direct_path_rel_exprs nfa start start) empty_rel
  | loop_path_rel_expr (kk as {kk_union, kk_closure, ...}) nfa (q :: qs) start =
    if start = q then
      kk_closure (loop_path_rel_expr kk nfa qs start)
    else
      kk_union (loop_path_rel_expr kk nfa qs start)
               (knot_path_rel_expr kk nfa qs start q start)

(* nfa_table -> unit NfaGraph.T *)
fun graph_for_nfa nfa =
  let
    (* typ -> unit NfaGraph.T -> unit NfaGraph.T *)
    fun new_node q = perhaps (try (NfaGraph.new_node (q, ())))
    (* nfa_table -> unit NfaGraph.T -> unit NfaGraph.T *)
    fun add_nfa [] = I
      | add_nfa ((_, []) :: nfa) = add_nfa nfa
      | add_nfa ((q, ((_, q') :: transitions)) :: nfa) =
        add_nfa ((q, transitions) :: nfa) o NfaGraph.add_edge (q, q') o
        new_node q' o new_node q
  in add_nfa nfa NfaGraph.empty end

(* nfa_table -> nfa_table list *)
fun strongly_connected_sub_nfas nfa =
  nfa |> graph_for_nfa |> NfaGraph.strong_conn
      |> map (fn keys => filter (member (op =) keys o fst) nfa)

(* dtype_spec list -> kodkod_constrs -> nfa_table -> typ -> KK.formula *)
fun acyclicity_axiom_for_datatype dtypes kk nfa start =
  #kk_no kk (#kk_intersect kk
                 (loop_path_rel_expr kk nfa (map fst nfa) start) KK.Iden)
(* extended_context -> kodkod_constrs -> nut NameTable.table -> dtype_spec list
   -> KK.formula list *)
fun acyclicity_axioms_for_datatypes ext_ctxt kk rel_table dtypes =
  map_filter (nfa_entry_for_datatype ext_ctxt kk rel_table dtypes) dtypes
  |> strongly_connected_sub_nfas
  |> maps (fn nfa => map (acyclicity_axiom_for_datatype dtypes kk nfa o fst)
                         nfa)

(* extended_context -> int -> kodkod_constrs -> nut NameTable.table
   -> KK.rel_expr -> constr_spec -> int -> KK.formula *)
fun sel_axiom_for_sel ext_ctxt j0
        (kk as {kk_all, kk_implies, kk_formula_if, kk_subset, kk_rel_eq, kk_no,
                kk_join, ...}) rel_table dom_r
        ({const, delta, epsilon, exclusive, explicit_max, ...} : constr_spec)
        n =
  let
    val x as (_, T) = boxed_nth_sel_for_constr ext_ctxt const n
    val (r, R, arity) = const_triple rel_table x
    val R2 = dest_Func R |> snd
    val z = (epsilon - delta, delta + j0)
  in
    if exclusive then
      kk_n_ary_function kk (Func (Atom z, R2)) r
    else
      let val r' = kk_join (KK.Var (1, 0)) r in
        kk_all [KK.DeclOne ((1, 0), KK.AtomSeq z)]
               (kk_formula_if (kk_subset (KK.Var (1, 0)) dom_r)
                              (kk_n_ary_function kk R2 r') (kk_no r'))
      end
  end
(* extended_context -> int -> int -> kodkod_constrs -> nut NameTable.table
   -> constr_spec -> KK.formula list *)
fun sel_axioms_for_constr ext_ctxt bits j0 kk rel_table
        (constr as {const, delta, epsilon, explicit_max, ...}) =
  let
    val honors_explicit_max =
      explicit_max < 0 orelse epsilon - delta <= explicit_max
  in
    if explicit_max = 0 then
      [formula_for_bool honors_explicit_max]
    else
      let
        val ran_r = discr_rel_expr rel_table const
        val max_axiom =
          if honors_explicit_max then
            KK.True
          else if is_twos_complement_representable bits (epsilon - delta) then
            KK.LE (KK.Cardinality ran_r, KK.Num explicit_max)
          else
            raise TOO_SMALL ("Nitpick_Kodkod.sel_axioms_for_constr",
                             "\"bits\" value " ^ string_of_int bits ^
                             " too small for \"max\"")
      in
        max_axiom ::
        map (sel_axiom_for_sel ext_ctxt j0 kk rel_table ran_r constr)
            (index_seq 0 (num_sels_for_constr_type (snd const)))
      end
  end
(* extended_context -> int -> int -> kodkod_constrs -> nut NameTable.table
   -> dtype_spec -> KK.formula list *)
fun sel_axioms_for_datatype ext_ctxt bits j0 kk rel_table
                            ({constrs, ...} : dtype_spec) =
  maps (sel_axioms_for_constr ext_ctxt bits j0 kk rel_table) constrs

(* extended_context -> kodkod_constrs -> nut NameTable.table -> constr_spec
   -> KK.formula list *)
fun uniqueness_axiom_for_constr ext_ctxt
        ({kk_all, kk_implies, kk_and, kk_rel_eq, kk_lone, kk_join, ...}
         : kodkod_constrs) rel_table ({const, ...} : constr_spec) =
  let
    (* KK.rel_expr -> KK.formula *)
    fun conjunct_for_sel r =
      kk_rel_eq (kk_join (KK.Var (1, 0)) r) (kk_join (KK.Var (1, 1)) r)
    val num_sels = num_sels_for_constr_type (snd const)
    val triples = map (const_triple rel_table
                       o boxed_nth_sel_for_constr ext_ctxt const)
                      (~1 upto num_sels - 1)
    val j0 = case triples |> hd |> #2 of
               Func (Atom (_, j0), _) => j0
             | R => raise REP ("Nitpick_Kodkod.uniqueness_axiom_for_constr",
                               [R])
    val set_r = triples |> hd |> #1
  in
    if num_sels = 0 then
      kk_lone set_r
    else
      kk_all (map (KK.DeclOne o rpair set_r o pair 1) [0, 1])
             (kk_implies
                  (fold1 kk_and (map (conjunct_for_sel o #1) (tl triples)))
                  (kk_rel_eq (KK.Var (1, 0)) (KK.Var (1, 1))))
  end
(* extended_context -> kodkod_constrs -> nut NameTable.table -> dtype_spec
   -> KK.formula list *)
fun uniqueness_axioms_for_datatype ext_ctxt kk rel_table
                                   ({constrs, ...} : dtype_spec) =
  map (uniqueness_axiom_for_constr ext_ctxt kk rel_table) constrs

(* constr_spec -> int *)
fun effective_constr_max ({delta, epsilon, ...} : constr_spec) = epsilon - delta
(* int -> kodkod_constrs -> nut NameTable.table -> dtype_spec
   -> KK.formula list *)
fun partition_axioms_for_datatype j0 (kk as {kk_rel_eq, kk_union, ...})
                                  rel_table
                                  ({card, constrs, ...} : dtype_spec) =
  if forall #exclusive constrs then
    [Integer.sum (map effective_constr_max constrs) = card |> formula_for_bool]
  else
    let val rs = map (discr_rel_expr rel_table o #const) constrs in
      [kk_rel_eq (fold1 kk_union rs) (KK.AtomSeq (card, j0)),
       kk_disjoint_sets kk rs]
    end

(* extended_context -> int -> int Typtab.table -> kodkod_constrs
   -> nut NameTable.table -> dtype_spec -> KK.formula list *)
fun other_axioms_for_datatype _ _ _ _ _ {shallow = true, ...} = []
  | other_axioms_for_datatype ext_ctxt bits ofs kk rel_table
                              (dtype as {typ, ...}) =
    let val j0 = offset_of_type ofs typ in
      sel_axioms_for_datatype ext_ctxt bits j0 kk rel_table dtype @
      uniqueness_axioms_for_datatype ext_ctxt kk rel_table dtype @
      partition_axioms_for_datatype j0 kk rel_table dtype
    end

(* extended_context -> int -> int Typtab.table -> kodkod_constrs
   -> nut NameTable.table -> dtype_spec list -> KK.formula list *)
fun declarative_axioms_for_datatypes ext_ctxt bits ofs kk rel_table dtypes =
  acyclicity_axioms_for_datatypes ext_ctxt kk rel_table dtypes @
  maps (other_axioms_for_datatype ext_ctxt bits ofs kk rel_table) dtypes

(* int -> int Typtab.table -> bool -> kodkod_constrs -> nut -> KK.formula *)
fun kodkod_formula_from_nut bits ofs liberal
        (kk as {kk_all, kk_exist, kk_formula_let, kk_formula_if, kk_or, kk_not,
                kk_iff, kk_implies, kk_and, kk_subset, kk_rel_eq, kk_no, kk_one,
                kk_some, kk_rel_let, kk_rel_if, kk_union, kk_difference,
                kk_intersect, kk_product, kk_join, kk_closure, kk_comprehension,
                kk_project, kk_project_seq, kk_not3, kk_nat_less, kk_int_less,
                ...}) u =
  let
    val main_j0 = offset_of_type ofs bool_T
    val bool_j0 = main_j0
    val bool_atom_R = Atom (2, main_j0)
    val false_atom = KK.Atom bool_j0
    val true_atom = KK.Atom (bool_j0 + 1)

    (* polarity -> int -> KK.rel_expr -> KK.formula *)
    fun formula_from_opt_atom polar j0 r =
      case polar of
        Neg => kk_not (kk_rel_eq r (KK.Atom j0))
      | _ => kk_rel_eq r (KK.Atom (j0 + 1))
    (* int -> KK.rel_expr -> KK.formula *)
    val formula_from_atom = formula_from_opt_atom Pos

    (* KK.formula -> KK.formula -> KK.formula *)
    fun kk_notimplies f1 f2 = kk_and f1 (kk_not f2)
    (* KK.rel_expr -> KK.rel_expr -> KK.rel_expr *)
    val kk_or3 =
      double_rel_rel_let kk
          (fn r1 => fn r2 =>
              kk_rel_if (kk_subset true_atom (kk_union r1 r2)) true_atom
                        (kk_intersect r1 r2))
    val kk_and3 =
      double_rel_rel_let kk
          (fn r1 => fn r2 =>
              kk_rel_if (kk_subset false_atom (kk_union r1 r2)) false_atom
                        (kk_intersect r1 r2))
    fun kk_notimplies3 r1 r2 = kk_and3 r1 (kk_not3 r2)

    (* int -> KK.rel_expr -> KK.formula list *)
    val unpack_formulas =
      map (formula_from_atom bool_j0) oo unpack_vect_in_chunks kk 1
    (* (KK.formula -> KK.formula -> KK.formula) -> int -> KK.rel_expr
       -> KK.rel_expr -> KK.rel_expr *)
    fun kk_vect_set_op connective k r1 r2 =
      fold1 kk_product (map2 (atom_from_formula kk bool_j0 oo connective)
                             (unpack_formulas k r1) (unpack_formulas k r2))
    (* (KK.formula -> KK.formula -> KK.formula) -> int -> KK.rel_expr
       -> KK.rel_expr -> KK.formula *)
    fun kk_vect_set_bool_op connective k r1 r2 =
      fold1 kk_and (map2 connective (unpack_formulas k r1)
                         (unpack_formulas k r2))

    (* nut -> KK.formula *)
    fun to_f u =
      case rep_of u of
        Formula polar =>
        (case u of
           Cst (False, _, _) => KK.False
         | Cst (True, _, _) => KK.True
         | Op1 (Not, _, _, u1) =>
           kk_not (to_f_with_polarity (flip_polarity polar) u1)
         | Op1 (Finite, _, _, u1) =>
           let val opt1 = is_opt_rep (rep_of u1) in
             case polar of
               Neut =>
               if opt1 then raise NUT ("Nitpick_Kodkod.to_f (Finite)", [u])
               else KK.True
             | Pos => formula_for_bool (not opt1)
             | Neg => KK.True
           end
         | Op1 (IsUnknown, _, _, u1) => kk_no (to_r u1)
         | Op1 (Cast, _, _, u1) => to_f_with_polarity polar u1
         | Op2 (All, _, _, u1, u2) =>
           kk_all (untuple to_decl u1) (to_f_with_polarity polar u2)
         | Op2 (Exist, _, _, u1, u2) =>
           kk_exist (untuple to_decl u1) (to_f_with_polarity polar u2)
         | Op2 (Or, _, _, u1, u2) =>
           kk_or (to_f_with_polarity polar u1) (to_f_with_polarity polar u2)
         | Op2 (And, _, _, u1, u2) =>
           kk_and (to_f_with_polarity polar u1) (to_f_with_polarity polar u2)
         | Op2 (Less, T, Formula polar, u1, u2) =>
           formula_from_opt_atom polar bool_j0
               (to_r (Op2 (Less, T, Opt bool_atom_R, u1, u2)))
         | Op2 (Subset, _, _, u1, u2) =>
           let
             val dom_T = domain_type (type_of u1)
             val R1 = rep_of u1
             val R2 = rep_of u2
             val (dom_R, ran_R) =
               case min_rep R1 R2 of
                 Func (Unit, R') =>
                 (Atom (1, offset_of_type ofs dom_T), R')
               | Func Rp => Rp
               | R => (Atom (card_of_domain_from_rep 2 R,
                             offset_of_type ofs dom_T),
                       if is_opt_rep R then Opt bool_atom_R else Formula Neut)
             val set_R = Func (dom_R, ran_R)
           in
             if not (is_opt_rep ran_R) then
               to_set_bool_op kk_implies kk_subset u1 u2
             else if polar = Neut then
               raise NUT ("Nitpick_Kodkod.to_f (Subset)", [u])
             else
               let
                 (* FIXME: merge with similar code below *)
                 (* bool -> nut -> KK.rel_expr *)
                 fun set_to_r widen u =
                   if widen then
                     kk_difference (full_rel_for_rep dom_R)
                                   (kk_join (to_rep set_R u) false_atom)
                   else
                     kk_join (to_rep set_R u) true_atom
                 val widen1 = (polar = Pos andalso is_opt_rep R1)
                 val widen2 = (polar = Neg andalso is_opt_rep R2)
               in kk_subset (set_to_r widen1 u1) (set_to_r widen2 u2) end
           end
         | Op2 (DefEq, _, _, u1, u2) =>
           (case min_rep (rep_of u1) (rep_of u2) of
              Unit => KK.True
            | Formula polar =>
              kk_iff (to_f_with_polarity polar u1) (to_f_with_polarity polar u2)
            | min_R =>
              let
                (* nut -> nut list *)
                fun args (Op2 (Apply, _, _, u1, u2)) = u2 :: args u1
                  | args (Tuple (_, _, us)) = us
                  | args _ = []
                val opt_arg_us = filter (is_opt_rep o rep_of) (args u1)
              in
                if null opt_arg_us orelse not (is_Opt min_R) orelse
                   is_eval_name u1 then
                  fold (kk_or o (kk_no o to_r)) opt_arg_us
                       (kk_rel_eq (to_rep min_R u1) (to_rep min_R u2))
                else
                  kk_subset (to_rep min_R u1) (to_rep min_R u2)
              end)
         | Op2 (Eq, T, R, u1, u2) =>
           (case min_rep (rep_of u1) (rep_of u2) of
              Unit => KK.True
            | Formula polar =>
              kk_iff (to_f_with_polarity polar u1) (to_f_with_polarity polar u2)
            | min_R =>
              if is_opt_rep min_R then
                if polar = Neut then
                  (* continuation of hackish optimization *)
                  kk_rel_eq (to_rep min_R u1) (to_rep min_R u2)
                else if is_Cst Unrep u1 then
                  to_could_be_unrep (polar = Neg) u2
                else if is_Cst Unrep u2 then
                  to_could_be_unrep (polar = Neg) u1
                else
                  let
                    val r1 = to_rep min_R u1
                    val r2 = to_rep min_R u2
                    val both_opt = forall (is_opt_rep o rep_of) [u1, u2]
                  in
                    (if polar = Pos then
                       if not both_opt then
                         kk_rel_eq r1 r2
                       else if is_lone_rep min_R andalso
                               arity_of_rep min_R = 1 then
                         kk_some (kk_intersect r1 r2)
                       else
                         raise SAME ()
                     else
                       if is_lone_rep min_R then
                         if arity_of_rep min_R = 1 then
                           kk_subset (kk_product r1 r2) KK.Iden
                         else if not both_opt then
                           (r1, r2) |> is_opt_rep (rep_of u2) ? swap
                                    |-> kk_subset
                         else
                           raise SAME ()
                       else
                         raise SAME ())
                    handle SAME () =>
                           formula_from_opt_atom polar bool_j0
                               (to_guard [u1, u2] bool_atom_R
                                         (rel_expr_from_formula kk bool_atom_R
                                                            (kk_rel_eq r1 r2)))
                  end
              else
                let
                  val r1 = to_rep min_R u1
                  val r2 = to_rep min_R u2
                in
                  if is_one_rep min_R then
                    let
                      val rs1 = unpack_products r1
                      val rs2 = unpack_products r2
                    in
                      if length rs1 = length rs2 andalso
                         map KK.arity_of_rel_expr rs1
                         = map KK.arity_of_rel_expr rs2 then
                        fold1 kk_and (map2 kk_subset rs1 rs2)
                      else
                        kk_subset r1 r2
                    end
                  else
                    kk_rel_eq r1 r2
                end)
         | Op2 (The, T, _, u1, u2) =>
           to_f_with_polarity polar
                              (Op2 (The, T, Opt (Atom (2, bool_j0)), u1, u2))
         | Op2 (Eps, T, _, u1, u2) =>
           to_f_with_polarity polar
                              (Op2 (Eps, T, Opt (Atom (2, bool_j0)), u1, u2))
         | Op2 (Apply, T, _, u1, u2) =>
           (case (polar, rep_of u1) of
              (Neg, Func (R, Formula Neut)) => kk_subset (to_opt R u2) (to_r u1)
            | _ =>
              to_f_with_polarity polar
                 (Op2 (Apply, T, Opt (Atom (2, offset_of_type ofs T)), u1, u2)))
         | Op3 (Let, _, _, u1, u2, u3) =>
           kk_formula_let [to_expr_assign u1 u2] (to_f_with_polarity polar u3)
         | Op3 (If, _, _, u1, u2, u3) =>
           kk_formula_if (to_f u1) (to_f_with_polarity polar u2)
                         (to_f_with_polarity polar u3)
         | FormulaReg (j, _, _) => KK.FormulaReg j
         | _ => raise NUT ("Nitpick_Kodkod.to_f", [u]))
      | Atom (2, j0) => formula_from_atom j0 (to_r u)
      | _ => raise NUT ("Nitpick_Kodkod.to_f", [u])
    (* polarity -> nut -> KK.formula *)
    and to_f_with_polarity polar u =
      case rep_of u of
        Formula _ => to_f u
      | Atom (2, j0) => formula_from_atom j0 (to_r u)
      | Opt (Atom (2, j0)) => formula_from_opt_atom polar j0 (to_r u)
      | _ => raise NUT ("Nitpick_Kodkod.to_f_with_polarity", [u])
    (* nut -> KK.rel_expr *)
    and to_r u =
      case u of
        Cst (False, _, Atom _) => false_atom
      | Cst (True, _, Atom _) => true_atom
      | Cst (Iden, T, Func (Struct [R1, R2], Formula Neut)) =>
        if R1 = R2 andalso arity_of_rep R1 = 1 then
          kk_intersect KK.Iden (kk_product (full_rel_for_rep R1) KK.Univ)
        else
          let
            val schema1 = atom_schema_of_rep R1
            val schema2 = atom_schema_of_rep R2
            val arity1 = length schema1
            val arity2 = length schema2
            val r1 = fold1 kk_product (unary_var_seq 0 arity1)
            val r2 = fold1 kk_product (unary_var_seq arity1 arity2)
            val min_R = min_rep R1 R2
          in
            kk_comprehension
                (decls_for_atom_schema 0 (schema1 @ schema2))
                (kk_rel_eq (rel_expr_from_rel_expr kk min_R R1 r1)
                           (rel_expr_from_rel_expr kk min_R R2 r2))
          end
      | Cst (Iden, T, Func (Atom (1, j0), Formula Neut)) => KK.Atom j0
      | Cst (Iden, T as Type ("fun", [T1, _]), R as Func (R1, _)) =>
        to_rep R (Cst (Iden, T, Func (one_rep ofs T1 R1, Formula Neut)))
      | Cst (Num j, T, R) =>
        if is_word_type T then
          atom_from_int_expr kk T R (KK.Num j)
        else if T = int_T then
          case atom_for_int (card_of_rep R, offset_of_type ofs int_T) j of
            ~1 => if is_opt_rep R then KK.None
                  else raise NUT ("Nitpick_Kodkod.to_r (Num)", [u])
          | j' => KK.Atom j'
        else
          if j < card_of_rep R then KK.Atom (j + offset_of_type ofs T)
          else if is_opt_rep R then KK.None
          else raise NUT ("Nitpick_Kodkod.to_r (Num)", [u])
      | Cst (Unknown, _, R) => empty_rel_for_rep R
      | Cst (Unrep, _, R) => empty_rel_for_rep R
      | Cst (Suc, T as @{typ "unsigned_bit word => unsigned_bit word"}, R) =>
        to_bit_word_unary_op T R (curry KK.Add (KK.Num 1))
      | Cst (Suc, @{typ "nat => nat"}, Func (Atom x, _)) =>
        kk_intersect (KK.Rel suc_rel) (kk_product KK.Univ (KK.AtomSeq x))
      | Cst (Suc, _, Func (Atom x, _)) => KK.Rel suc_rel
      | Cst (Add, Type ("fun", [@{typ nat}, _]), _) => KK.Rel nat_add_rel
      | Cst (Add, Type ("fun", [@{typ int}, _]), _) => KK.Rel int_add_rel
      | Cst (Add, T as Type ("fun", [@{typ "unsigned_bit word"}, _]), R) =>
        to_bit_word_binary_op T R NONE (SOME (curry KK.Add))
      | Cst (Add, T as Type ("fun", [@{typ "signed_bit word"}, _]), R) =>
        to_bit_word_binary_op T R
            (SOME (fn i1 => fn i2 => fn i3 =>
                 kk_implies (KK.LE (KK.Num 0, KK.BitXor (i1, i2)))
                            (KK.LE (KK.Num 0, KK.BitXor (i2, i3)))))
            (SOME (curry KK.Add))
      | Cst (Subtract, Type ("fun", [@{typ nat}, _]), _) =>
        KK.Rel nat_subtract_rel
      | Cst (Subtract, Type ("fun", [@{typ int}, _]), _) =>
        KK.Rel int_subtract_rel
      | Cst (Subtract, T as Type ("fun", [@{typ "unsigned_bit word"}, _]), R) =>
        to_bit_word_binary_op T R NONE
            (SOME (fn i1 => fn i2 =>
                      KK.IntIf (KK.LE (i1, i2), KK.Num 0, KK.Sub (i1, i2))))
      | Cst (Subtract, T as Type ("fun", [@{typ "signed_bit word"}, _]), R) =>
        to_bit_word_binary_op T R
            (SOME (fn i1 => fn i2 => fn i3 =>
                 kk_implies (KK.LT (KK.BitXor (i1, i2), KK.Num 0))
                            (KK.LT (KK.BitXor (i2, i3), KK.Num 0))))
            (SOME (curry KK.Sub))
      | Cst (Multiply, Type ("fun", [@{typ nat}, _]), _) =>
        KK.Rel nat_multiply_rel
      | Cst (Multiply, Type ("fun", [@{typ int}, _]), _) =>
        KK.Rel int_multiply_rel
      | Cst (Multiply,
             T as Type ("fun", [Type (@{type_name word}, [bit_T]), _]), R) =>
        to_bit_word_binary_op T R
            (SOME (fn i1 => fn i2 => fn i3 =>
                kk_or (KK.IntEq (i2, KK.Num 0))
                      (KK.IntEq (KK.Div (i3, i2), i1)
                       |> bit_T = @{typ signed_bit}
                          ? kk_and (KK.LE (KK.Num 0,
                                           foldl1 KK.BitAnd [i1, i2, i3])))))
            (SOME (curry KK.Mult))
      | Cst (Divide, Type ("fun", [@{typ nat}, _]), _) => KK.Rel nat_divide_rel
      | Cst (Divide, Type ("fun", [@{typ int}, _]), _) => KK.Rel int_divide_rel
      | Cst (Divide, T as Type ("fun", [@{typ "unsigned_bit word"}, _]), R) =>
        to_bit_word_binary_op T R NONE
            (SOME (fn i1 => fn i2 =>
                      KK.IntIf (KK.IntEq (i2, KK.Num 0),
                                KK.Num 0, KK.Div (i1, i2))))
      | Cst (Divide, T as Type ("fun", [@{typ "signed_bit word"}, _]), R) =>
        to_bit_word_binary_op T R
            (SOME (fn i1 => fn i2 => fn i3 =>
                      KK.LE (KK.Num 0, foldl1 KK.BitAnd [i1, i2, i3])))
            (SOME (fn i1 => fn i2 =>
                 KK.IntIf (kk_and (KK.LT (i1, KK.Num 0))
                                  (KK.LT (KK.Num 0, i2)),
                     KK.Sub (KK.Div (KK.Add (i1, KK.Num 1), i2), KK.Num 1),
                     KK.IntIf (kk_and (KK.LT (KK.Num 0, i1))
                                      (KK.LT (i2, KK.Num 0)),
                         KK.Sub (KK.Div (KK.Sub (i1, KK.Num 1), i2), KK.Num 1),
                         KK.IntIf (KK.IntEq (i2, KK.Num 0),
                                   KK.Num 0, KK.Div (i1, i2))))))
      | Cst (Gcd, _, _) => KK.Rel gcd_rel
      | Cst (Lcm, _, _) => KK.Rel lcm_rel
      | Cst (Fracs, _, Func (Atom (1, _), _)) => KK.None
      | Cst (Fracs, _, Func (Struct _, _)) =>
        kk_project_seq (KK.Rel norm_frac_rel) 2 2
      | Cst (NormFrac, _, _) => KK.Rel norm_frac_rel
      | Cst (NatToInt, Type ("fun", [@{typ nat}, _]), Func (Atom _, Atom _)) =>
        KK.Iden
      | Cst (NatToInt, Type ("fun", [@{typ nat}, _]),
             Func (Atom (nat_k, nat_j0), Opt (Atom (int_k, int_j0)))) =>
        if nat_j0 = int_j0 then
          kk_intersect KK.Iden
              (kk_product (KK.AtomSeq (max_int_for_card int_k + 1, nat_j0))
                          KK.Univ)
        else
          raise BAD ("Nitpick_Kodkod.to_r (NatToInt)", "\"nat_j0 <> int_j0\"")
      | Cst (NatToInt, T as Type ("fun", [@{typ "unsigned_bit word"}, _]), R) =>
        to_bit_word_unary_op T R I
      | Cst (IntToNat, Type ("fun", [@{typ int}, _]),
             Func (Atom (int_k, int_j0), nat_R)) =>
        let
          val abs_card = max_int_for_card int_k + 1
          val (nat_k, nat_j0) = the_single (atom_schema_of_rep nat_R)
          val overlap = Int.min (nat_k, abs_card)
        in
          if nat_j0 = int_j0 then
            kk_union (kk_product (KK.AtomSeq (int_k - abs_card,
                                              int_j0 + abs_card))
                                 (KK.Atom nat_j0))
                     (kk_intersect KK.Iden
                          (kk_product (KK.AtomSeq (overlap, int_j0)) KK.Univ))
          else
            raise BAD ("Nitpick_Kodkod.to_r (IntToNat)", "\"nat_j0 <> int_j0\"")
        end
      | Cst (IntToNat, T as Type ("fun", [@{typ "signed_bit word"}, _]), R) =>
        to_bit_word_unary_op T R
            (fn i => KK.IntIf (KK.LE (i, KK.Num 0), KK.Num 0, i))
      | Op1 (Not, _, R, u1) => kk_not3 (to_rep R u1)
      | Op1 (Finite, _, Opt (Atom _), _) => KK.None
      | Op1 (Converse, T, R, u1) =>
        let
          val (b_T, a_T) = HOLogic.dest_prodT (domain_type T)
          val (b_R, a_R) =
            case R of
              Func (Struct [R1, R2], _) => (R1, R2)
            | Func (R1, _) =>
              if card_of_rep R1 <> 1 then
                raise REP ("Nitpick_Kodkod.to_r (Converse)", [R])
              else
                pairself (Atom o pair 1 o offset_of_type ofs) (b_T, a_T)
            | _ => raise REP ("Nitpick_Kodkod.to_r (Converse)", [R])
          val body_R = body_rep R
          val a_arity = arity_of_rep a_R
          val b_arity = arity_of_rep b_R
          val ab_arity = a_arity + b_arity
          val body_arity = arity_of_rep body_R
        in
          kk_project (to_rep (Func (Struct [a_R, b_R], body_R)) u1)
                     (map KK.Num (index_seq a_arity b_arity @
                                  index_seq 0 a_arity @
                                  index_seq ab_arity body_arity))
          |> rel_expr_from_rel_expr kk R (Func (Struct [b_R, a_R], body_R))
        end
      | Op1 (Closure, _, R, u1) =>
        if is_opt_rep R then
          let
            val T1 = type_of u1
            val R' = rep_to_binary_rel_rep ofs T1 (unopt_rep (rep_of u1))
            val R'' = opt_rep ofs T1 R'
          in
            single_rel_rel_let kk
                (fn r =>
                    let
                      val true_r = kk_closure (kk_join r true_atom)
                      val full_r = full_rel_for_rep R'
                      val false_r = kk_difference full_r
                                        (kk_closure (kk_difference full_r
                                                        (kk_join r false_atom)))
                    in
                      rel_expr_from_rel_expr kk R R''
                          (kk_union (kk_product true_r true_atom)
                                    (kk_product false_r false_atom))
                    end) (to_rep R'' u1)
          end
        else
          let val R' = rep_to_binary_rel_rep ofs (type_of u1) (rep_of u1) in
            rel_expr_from_rel_expr kk R R' (kk_closure (to_rep R' u1))
          end
      | Op1 (SingletonSet, _, Func (R1, Opt _), Cst (Unrep, _, _)) =>
        (if R1 = Unit then I else kk_product (full_rel_for_rep R1)) false_atom
      | Op1 (SingletonSet, _, R, u1) =>
        (case R of
           Func (R1, Formula Neut) => to_rep R1 u1
         | Func (Unit, Opt R) => to_guard [u1] R true_atom
         | Func (R1, R2 as Opt _) =>
           single_rel_rel_let kk
               (fn r => kk_rel_if (kk_no r) (empty_rel_for_rep R)
                            (rel_expr_to_func kk R1 bool_atom_R
                                              (Func (R1, Formula Neut)) r))
               (to_opt R1 u1)
         | _ => raise NUT ("Nitpick_Kodkod.to_r (SingletonSet)", [u]))
      | Op1 (Tha, T, R, u1) =>
        if is_opt_rep R then
          kk_join (to_rep (Func (unopt_rep R, Opt bool_atom_R)) u1) true_atom
        else
          to_rep (Func (R, Formula Neut)) u1
      | Op1 (First, T, R, u1) => to_nth_pair_sel 0 T R u1
      | Op1 (Second, T, R, u1) => to_nth_pair_sel 1 T R u1
      | Op1 (Cast, _, R, u1) =>
        ((case rep_of u1 of
            Formula _ =>
            (case unopt_rep R of
               Atom (2, j0) => atom_from_formula kk j0 (to_f u1)
             | _ => raise SAME ())
          | _ => raise SAME ())
         handle SAME () => rel_expr_from_rel_expr kk R (rep_of u1) (to_r u1))
      | Op2 (All, T, R as Opt _, u1, u2) =>
        to_r (Op1 (Not, T, R,
                   Op2 (Exist, T, R, u1, Op1 (Not, T, rep_of u2, u2))))
      | Op2 (Exist, T, Opt _, u1, u2) =>
        let val rs1 = untuple to_decl u1 in
          if not (is_opt_rep (rep_of u2)) then
            kk_rel_if (kk_exist rs1 (to_f u2)) true_atom KK.None
          else
            let val r2 = to_r u2 in
              kk_union (kk_rel_if (kk_exist rs1 (kk_rel_eq r2 true_atom))
                                  true_atom KK.None)
                       (kk_rel_if (kk_all rs1 (kk_rel_eq r2 false_atom))
                                  false_atom KK.None)
            end
        end
      | Op2 (Or, _, _, u1, u2) =>
        if is_opt_rep (rep_of u1) then kk_rel_if (to_f u2) true_atom (to_r u1)
        else kk_rel_if (to_f u1) true_atom (to_r u2)
      | Op2 (And, _, _, u1, u2) =>
        if is_opt_rep (rep_of u1) then kk_rel_if (to_f u2) (to_r u1) false_atom
        else kk_rel_if (to_f u1) (to_r u2) false_atom
      | Op2 (Less, _, _, u1, u2) =>
        (case type_of u1 of
           @{typ nat} =>
           if is_Cst Unrep u1 then to_compare_with_unrep u2 false_atom
           else if is_Cst Unrep u2 then to_compare_with_unrep u1 true_atom
           else kk_nat_less (to_integer u1) (to_integer u2)
         | @{typ int} => kk_int_less (to_integer u1) (to_integer u2)
         | _ => double_rel_rel_let kk
                    (fn r1 => fn r2 =>
                        kk_rel_if
                            (fold kk_and (map_filter (fn (u, r) =>
                                 if is_opt_rep (rep_of u) then SOME (kk_some r)
                                 else NONE) [(u1, r1), (u2, r2)]) KK.True)
                            (atom_from_formula kk bool_j0 (KK.LT (pairself
                                (int_expr_from_atom kk (type_of u1)) (r1, r2))))
                            KK.None)
                    (to_r u1) (to_r u2))
      | Op2 (The, T, R, u1, u2) =>
        if is_opt_rep R then
          let val r1 = to_opt (Func (unopt_rep R, bool_atom_R)) u1 in
            kk_rel_if (kk_one (kk_join r1 true_atom)) (kk_join r1 true_atom)
                      (kk_rel_if (kk_or (kk_some (kk_join r1 true_atom))
                                        (kk_subset (full_rel_for_rep R)
                                                   (kk_join r1 false_atom)))
                                 (to_rep R u2) (empty_rel_for_rep R))
          end
        else
          let val r1 = to_rep (Func (R, Formula Neut)) u1 in
            kk_rel_if (kk_one r1) r1 (to_rep R u2)
          end
      | Op2 (Eps, T, R, u1, u2) =>
        if is_opt_rep (rep_of u1) then
          let
            val r1 = to_rep (Func (unopt_rep R, Opt bool_atom_R)) u1
            val r2 = to_rep R u2
          in
            kk_union (kk_rel_if (kk_one (kk_join r1 true_atom))
                                (kk_join r1 true_atom) (empty_rel_for_rep R))
                     (kk_rel_if (kk_or (kk_subset r2 (kk_join r1 true_atom))
                                       (kk_subset (full_rel_for_rep R)
                                                  (kk_join r1 false_atom)))
                                r2 (empty_rel_for_rep R))
          end
        else
          let
            val r1 = to_rep (Func (unopt_rep R, Formula Neut)) u1
            val r2 = to_rep R u2
          in
            kk_union (kk_rel_if (kk_one r1) r1 (empty_rel_for_rep R))
                     (kk_rel_if (kk_or (kk_no r1) (kk_subset r2 r1))
                                r2 (empty_rel_for_rep R))
          end
      | Op2 (Triad, T, Opt (Atom (2, j0)), u1, u2) =>
        let
          val f1 = to_f u1
          val f2 = to_f u2
        in
          if f1 = f2 then
            atom_from_formula kk j0 f1
          else
            kk_union (kk_rel_if f1 true_atom KK.None)
                     (kk_rel_if f2 KK.None false_atom)
        end
      | Op2 (Union, _, R, u1, u2) =>
        to_set_op kk_or kk_or3 kk_union kk_union kk_intersect false R u1 u2
      | Op2 (SetDifference, _, R, u1, u2) =>
        to_set_op kk_notimplies kk_notimplies3 kk_difference kk_intersect
                  kk_union true R u1 u2
      | Op2 (Intersect, _, R, u1, u2) =>
        to_set_op kk_and kk_and3 kk_intersect kk_intersect kk_union false R
                  u1 u2
      | Op2 (Composition, _, R, u1, u2) =>
        let
          val (a_T, b_T) = HOLogic.dest_prodT (domain_type (type_of u1))
          val (_, c_T) = HOLogic.dest_prodT (domain_type (type_of u2))
          val ab_k = card_of_domain_from_rep 2 (rep_of u1)
          val bc_k = card_of_domain_from_rep 2 (rep_of u2)
          val ac_k = card_of_domain_from_rep 2 R
          val a_k = exact_root 2 (ac_k * ab_k div bc_k)
          val b_k = exact_root 2 (ab_k * bc_k div ac_k)
          val c_k = exact_root 2 (bc_k * ac_k div ab_k)
          val a_R = Atom (a_k, offset_of_type ofs a_T)
          val b_R = Atom (b_k, offset_of_type ofs b_T)
          val c_R = Atom (c_k, offset_of_type ofs c_T)
          val body_R = body_rep R
        in
          (case body_R of
             Formula Neut =>
             kk_join (to_rep (Func (Struct [a_R, b_R], Formula Neut)) u1)
                     (to_rep (Func (Struct [b_R, c_R], Formula Neut)) u2)
           | Opt (Atom (2, _)) =>
             let
               (* FIXME: merge with similar code above *)
               (* rep -> rep -> nut -> KK.rel_expr *)
               fun must R1 R2 u =
                 kk_join (to_rep (Func (Struct [R1, R2], body_R)) u) true_atom
               fun may R1 R2 u =
                 kk_difference
                     (full_rel_for_rep (Struct [R1, R2]))
                     (kk_join (to_rep (Func (Struct [R1, R2], body_R)) u)
                              false_atom)
             in
               kk_union
                   (kk_product (kk_join (must a_R b_R u1) (must b_R c_R u2))
                               true_atom)
                   (kk_product (kk_difference
                                   (full_rel_for_rep (Struct [a_R, c_R]))
                                   (kk_join (may a_R b_R u1) (may b_R c_R u2)))
                               false_atom)
             end
           | _ => raise NUT ("Nitpick_Kodkod.to_r (Composition)", [u]))
          |> rel_expr_from_rel_expr kk R (Func (Struct [a_R, c_R], body_R))
        end
      | Op2 (Product, T, R, u1, u2) =>
        let
          val (a_T, b_T) = HOLogic.dest_prodT (domain_type T)
          val a_k = card_of_domain_from_rep 2 (rep_of u1)
          val b_k = card_of_domain_from_rep 2 (rep_of u2)
          val a_R = Atom (a_k, offset_of_type ofs a_T)
          val b_R = Atom (b_k, offset_of_type ofs b_T)
          val body_R = body_rep R
        in
          (case body_R of
             Formula Neut =>
             kk_product (to_rep (Func (a_R, Formula Neut)) u1)
                        (to_rep (Func (b_R, Formula Neut)) u2)
           | Opt (Atom (2, _)) =>
             let
               (* KK.rel_expr -> rep -> nut -> KK.rel_expr *)
               fun do_nut r R u = kk_join (to_rep (Func (R, body_R)) u) r
               (* KK.rel_expr -> KK.rel_expr *)
               fun do_term r =
                 kk_product (kk_product (do_nut r a_R u1) (do_nut r b_R u2)) r
             in kk_union (do_term true_atom) (do_term false_atom) end
           | _ => raise NUT ("Nitpick_Kodkod.to_r (Product)", [u]))
          |> rel_expr_from_rel_expr kk R (Func (Struct [a_R, b_R], body_R))
        end
      | Op2 (Image, T, R, u1, u2) =>
        (case (rep_of u1, rep_of u2) of
           (Func (R11, R12), Func (R21, Formula Neut)) =>
           if R21 = R11 andalso is_lone_rep R12 then
             let
               (* KK.rel_expr -> KK.rel_expr *)
               fun big_join r = kk_n_fold_join kk false R21 R12 r (to_r u1)
               val core_r = big_join (to_r u2)
               val core_R = Func (R12, Formula Neut)
             in
               if is_opt_rep R12 then
                 let
                   val schema = atom_schema_of_rep R21
                   val decls = decls_for_atom_schema ~1 schema
                   val vars = unary_var_seq ~1 (length decls)
                   val f = kk_some (big_join (fold1 kk_product vars))
                 in
                   kk_rel_if (kk_all decls f)
                             (rel_expr_from_rel_expr kk R core_R core_r)
                             (rel_expr_from_rel_expr kk R (opt_rep ofs T core_R)
                                              (kk_product core_r true_atom))
                 end
               else
                 rel_expr_from_rel_expr kk R core_R core_r
             end
           else
             raise NUT ("Nitpick_Kodkod.to_r (Image)", [u1, u2])
         | _ => raise NUT ("Nitpick_Kodkod.to_r (Image)", [u1, u2]))
      | Op2 (Apply, @{typ nat}, _,
             Op2 (Apply, _, _, Cst (Subtract, _, _), u1), u2) =>
        if is_Cst Unrep u2 andalso not (is_opt_rep (rep_of u1)) then
          KK.Atom (offset_of_type ofs nat_T)
        else
          fold kk_join (map to_integer [u1, u2]) (KK.Rel nat_subtract_rel)
      | Op2 (Apply, _, R, u1, u2) =>
        if is_Cst Unrep u2 andalso is_set_type (type_of u1) andalso
           is_FreeName u1 then
          false_atom
        else
          to_apply R u1 u2
      | Op2 (Lambda, T, R as Opt (Atom (1, j0)), u1, u2) =>
        to_guard [u1, u2] R (KK.Atom j0)
      | Op2 (Lambda, T, Func (_, Formula Neut), u1, u2) =>
        kk_comprehension (untuple to_decl u1) (to_f u2)
      | Op2 (Lambda, T, Func (_, R2), u1, u2) =>
        let
          val dom_decls = untuple to_decl u1
          val ran_schema = atom_schema_of_rep R2
          val ran_decls = decls_for_atom_schema ~1 ran_schema
          val ran_vars = unary_var_seq ~1 (length ran_decls)
        in
          kk_comprehension (dom_decls @ ran_decls)
                           (kk_subset (fold1 kk_product ran_vars)
                                      (to_rep R2 u2))
        end
      | Op3 (Let, _, R, u1, u2, u3) =>
        kk_rel_let [to_expr_assign u1 u2] (to_rep R u3)
      | Op3 (If, _, R, u1, u2, u3) =>
        if is_opt_rep (rep_of u1) then
          tripl_rel_rel_let kk
              (fn r1 => fn r2 => fn r3 =>
                  let val empty_r = empty_rel_for_rep R in
                    fold1 kk_union
                          [kk_rel_if (kk_rel_eq r1 true_atom) r2 empty_r,
                           kk_rel_if (kk_rel_eq r1 false_atom) r3 empty_r,
                           kk_rel_if (kk_rel_eq r2 r3)
                                (if inline_rel_expr r2 then r2 else r3) empty_r]
                  end)
              (to_r u1) (to_rep R u2) (to_rep R u3)
        else
          kk_rel_if (to_f u1) (to_rep R u2) (to_rep R u3)
      | Tuple (_, R, us) =>
        (case unopt_rep R of
           Struct Rs => to_product Rs us
         | Vect (k, R) => to_product (replicate k R) us
         | Atom (1, j0) =>
           (case filter (not_equal Unit o rep_of) us of
              [] => KK.Atom j0
            | us' => kk_rel_if (kk_some (fold1 kk_product (map to_r us')))
                               (KK.Atom j0) KK.None)
         | _ => raise NUT ("Nitpick_Kodkod.to_r (Tuple)", [u]))
      | Construct ([u'], _, _, []) => to_r u'
      | Construct (discr_u :: sel_us, T, R, arg_us) =>
        let
          val set_rs =
            map2 (fn sel_u => fn arg_u =>
                     let
                       val (R1, R2) = dest_Func (rep_of sel_u)
                       val sel_r = to_r sel_u
                       val arg_r = to_opt R2 arg_u
                     in
                       if is_one_rep R2 then
                         kk_n_fold_join kk true R2 R1 arg_r
                              (kk_project sel_r (flip_nums (arity_of_rep R2)))
                       else
                         kk_comprehension [KK.DeclOne ((1, ~1), to_r discr_u)]
                             (kk_rel_eq (kk_join (KK.Var (1, ~1)) sel_r) arg_r)
                     end) sel_us arg_us
        in fold1 kk_intersect set_rs end
      | BoundRel (x, _, _, _) => KK.Var x
      | FreeRel (x, _, _, _) => KK.Rel x
      | RelReg (j, _, R) => KK.RelReg (arity_of_rep R, j)
      | u => raise NUT ("Nitpick_Kodkod.to_r", [u])
    (* nut -> KK.decl *)
    and to_decl (BoundRel (x, _, R, _)) =
        KK.DeclOne (x, KK.AtomSeq (the_single (atom_schema_of_rep R)))
      | to_decl u = raise NUT ("Nitpick_Kodkod.to_decl", [u])
    (* nut -> KK.expr_assign *)
    and to_expr_assign (FormulaReg (j, _, R)) u =
        KK.AssignFormulaReg (j, to_f u)
      | to_expr_assign (RelReg (j, _, R)) u =
        KK.AssignRelReg ((arity_of_rep R, j), to_r u)
      | to_expr_assign u1 _ = raise NUT ("Nitpick_Kodkod.to_expr_assign", [u1])
    (* int * int -> nut -> KK.rel_expr *)
    and to_atom (x as (k, j0)) u =
      case rep_of u of
        Formula _ => atom_from_formula kk j0 (to_f u)
      | Unit => if k = 1 then KK.Atom j0
                else raise NUT ("Nitpick_Kodkod.to_atom", [u])
      | R => atom_from_rel_expr kk x R (to_r u)
    (* rep list -> nut -> KK.rel_expr *)
    and to_struct Rs u =
      case rep_of u of
        Unit => full_rel_for_rep (Struct Rs)
      | R' => struct_from_rel_expr kk Rs R' (to_r u)
    (* int -> rep -> nut -> KK.rel_expr *)
    and to_vect k R u =
      case rep_of u of
        Unit => full_rel_for_rep (Vect (k, R))
      | R' => vect_from_rel_expr kk k R R' (to_r u)
    (* rep -> rep -> nut -> KK.rel_expr *)
    and to_func R1 R2 u =
      case rep_of u of
        Unit => full_rel_for_rep (Func (R1, R2))
      | R' => rel_expr_to_func kk R1 R2 R' (to_r u)
    (* rep -> nut -> KK.rel_expr *)
    and to_opt R u =
      let val old_R = rep_of u in
        if is_opt_rep old_R then
          rel_expr_from_rel_expr kk (Opt R) old_R (to_r u)
        else
          to_rep R u
      end
    (* rep -> nut -> KK.rel_expr *)
    and to_rep (Atom x) u = to_atom x u
      | to_rep (Struct Rs) u = to_struct Rs u
      | to_rep (Vect (k, R)) u = to_vect k R u
      | to_rep (Func (R1, R2)) u = to_func R1 R2 u
      | to_rep (Opt R) u = to_opt R u
      | to_rep R _ = raise REP ("Nitpick_Kodkod.to_rep", [R])
    (* nut -> KK.rel_expr *)
    and to_integer u = to_opt (one_rep ofs (type_of u) (rep_of u)) u
    (* nut list -> rep -> KK.rel_expr -> KK.rel_expr *)
    and to_guard guard_us R r =
      let
        val unpacked_rs = unpack_joins r
        val plain_guard_rs =
          map to_r (filter (is_Opt o rep_of) guard_us)
          |> filter_out (member (op =) unpacked_rs)
        val func_guard_us =
          filter ((is_Func andf is_opt_rep) o rep_of) guard_us
        val func_guard_rs = map to_r func_guard_us
        val guard_fs =
          map kk_no plain_guard_rs @
          map2 (kk_not oo kk_n_ary_function kk)
               (map (unopt_rep o rep_of) func_guard_us) func_guard_rs
      in
        if null guard_fs then
          r
        else
          kk_rel_if (fold1 kk_or guard_fs) (empty_rel_for_rep R) r
      end
    (* rep -> rep -> KK.rel_expr -> int -> KK.rel_expr *)
    and to_project new_R old_R r j0 =
      rel_expr_from_rel_expr kk new_R old_R
                             (kk_project_seq r j0 (arity_of_rep old_R))
    (* rep list -> nut list -> KK.rel_expr *)
    and to_product Rs us =
      case map (uncurry to_opt) (filter (not_equal Unit o fst) (Rs ~~ us)) of
        [] => raise REP ("Nitpick_Kodkod.to_product", Rs)
      | rs => fold1 kk_product rs
    (* int -> typ -> rep -> nut -> KK.rel_expr *)
    and to_nth_pair_sel n res_T res_R u =
      case u of
        Tuple (_, _, us) => to_rep res_R (nth us n)
      | _ => let
               val R = rep_of u
               val (a_T, b_T) = HOLogic.dest_prodT (type_of u)
               val Rs =
                 case unopt_rep R of
                   Struct (Rs as [_, _]) => Rs
                 | _ =>
                   let
                     val res_card = card_of_rep res_R
                     val other_card = card_of_rep R div res_card
                     val (a_card, b_card) = (res_card, other_card)
                                            |> n = 1 ? swap
                   in
                     [Atom (a_card, offset_of_type ofs a_T),
                      Atom (b_card, offset_of_type ofs b_T)]
                   end
               val nth_R = nth Rs n
               val j0 = if n = 0 then 0 else arity_of_rep (hd Rs)
             in
               case arity_of_rep nth_R of
                 0 => to_guard [u] res_R
                               (to_rep res_R (Cst (Unity, res_T, Unit)))
               | arity => to_project res_R nth_R (to_rep (Opt (Struct Rs)) u) j0
             end
    (* (KK.formula -> KK.formula -> KK.formula)
       -> (KK.rel_expr -> KK.rel_expr -> KK.formula) -> nut -> nut
       -> KK.formula *)
    and to_set_bool_op connective set_oper u1 u2 =
      let
        val min_R = min_rep (rep_of u1) (rep_of u2)
        val r1 = to_rep min_R u1
        val r2 = to_rep min_R u2
      in
        case min_R of
          Vect (k, Atom _) => kk_vect_set_bool_op connective k r1 r2
        | Func (R1, Formula Neut) => set_oper r1 r2
        | Func (Unit, Atom (2, j0)) =>
          connective (formula_from_atom j0 r1) (formula_from_atom j0 r2)
        | Func (R1, Atom _) => set_oper (kk_join r1 true_atom)
                                        (kk_join r2 true_atom)
        | _ => raise REP ("Nitpick_Kodkod.to_set_bool_op", [min_R])
      end
    (* (KK.formula -> KK.formula -> KK.formula)
       -> (KK.rel_expr -> KK.rel_expr -> KK.rel_expr)
       -> (KK.rel_expr -> KK.rel_expr -> KK.formula)
       -> (KK.rel_expr -> KK.rel_expr -> KK.formula)
       -> (KK.rel_expr -> KK.rel_expr -> KK.formula) -> bool -> rep -> nut
       -> nut -> KK.rel_expr *)
    and to_set_op connective connective3 set_oper true_set_oper false_set_oper
                  neg_second R u1 u2 =
      let
        val min_R = min_rep (rep_of u1) (rep_of u2)
        val r1 = to_rep min_R u1
        val r2 = to_rep min_R u2
        val unopt_R = unopt_rep R
      in
        rel_expr_from_rel_expr kk unopt_R (unopt_rep min_R)
            (case min_R of
               Opt (Vect (k, Atom _)) => kk_vect_set_op connective k r1 r2
             | Vect (k, Atom _) => kk_vect_set_op connective k r1 r2
             | Func (_, Formula Neut) => set_oper r1 r2
             | Func (Unit, _) => connective3 r1 r2
             | Func (R1, _) =>
               double_rel_rel_let kk
                   (fn r1 => fn r2 =>
                       kk_union
                           (kk_product
                                (true_set_oper (kk_join r1 true_atom)
                                     (kk_join r2 (atom_for_bool bool_j0
                                                             (not neg_second))))
                                true_atom)
                           (kk_product
                                (false_set_oper (kk_join r1 false_atom)
                                     (kk_join r2 (atom_for_bool bool_j0
                                                                neg_second)))
                                false_atom))
                   r1 r2
             | _ => raise REP ("Nitpick_Kodkod.to_set_op", [min_R]))
      end
    (* typ -> rep -> (KK.int_expr -> KK.int_expr) -> KK.rel_expr *)
    and to_bit_word_unary_op T R oper =
      let
        val Ts = strip_type T ||> single |> op @
        (* int -> KK.int_expr *)
        fun int_arg j = int_expr_from_atom kk (nth Ts j) (KK.Var (1, j))
      in
        kk_comprehension (decls_for_atom_schema 0 (atom_schema_of_rep R))
            (KK.FormulaLet
                 (map (fn j => KK.AssignIntReg (j, int_arg j)) (0 upto 1),
                  KK.IntEq (KK.IntReg 1, oper (KK.IntReg 0))))
      end
    (* typ -> rep -> (KK.int_expr -> KK.int_expr -> KK.int_expr -> bool) option
       -> (KK.int_expr -> KK.int_expr -> KK.int_expr) option -> KK.rel_expr *)
    and to_bit_word_binary_op T R opt_guard opt_oper =
      let
        val Ts = strip_type T ||> single |> op @
        (* int -> KK.int_expr *)
        fun int_arg j = int_expr_from_atom kk (nth Ts j) (KK.Var (1, j))
      in
        kk_comprehension (decls_for_atom_schema 0 (atom_schema_of_rep R))
            (KK.FormulaLet
                 (map (fn j => KK.AssignIntReg (j, int_arg j)) (0 upto 2),
                  fold1 kk_and
                        ((case opt_guard of
                            NONE => []
                          | SOME guard =>
                            [guard (KK.IntReg 0) (KK.IntReg 1) (KK.IntReg 2)]) @
                         (case opt_oper of
                            NONE => []
                          | SOME oper =>
                            [KK.IntEq (KK.IntReg 2,
                                       oper (KK.IntReg 0) (KK.IntReg 1))]))))
      end
    (* rep -> rep -> KK.rel_expr -> nut -> KK.rel_expr *)
    and to_apply res_R func_u arg_u =
      case unopt_rep (rep_of func_u) of
        Unit =>
        let val j0 = offset_of_type ofs (type_of func_u) in
          to_guard [arg_u] res_R
                   (rel_expr_from_rel_expr kk res_R (Atom (1, j0)) (KK.Atom j0))
        end
      | Atom (1, j0) =>
        to_guard [arg_u] res_R
                 (rel_expr_from_rel_expr kk res_R (Atom (1, j0)) (to_r func_u))
      | Atom (k, j0) =>
        let
          val dom_card = card_of_rep (rep_of arg_u)
          val ran_R = Atom (exact_root dom_card k,
                            offset_of_type ofs (range_type (type_of func_u)))
        in
          to_apply_vect dom_card ran_R res_R (to_vect dom_card ran_R func_u)
                        arg_u
        end
      | Vect (1, R') =>
        to_guard [arg_u] res_R
                 (rel_expr_from_rel_expr kk res_R R' (to_r func_u))
      | Vect (k, R') => to_apply_vect k R' res_R (to_r func_u) arg_u
      | Func (R, Formula Neut) =>
        to_guard [arg_u] res_R (rel_expr_from_formula kk res_R
                                    (kk_subset (to_opt R arg_u) (to_r func_u)))
      | Func (Unit, R2) =>
        to_guard [arg_u] res_R
                 (rel_expr_from_rel_expr kk res_R R2 (to_r func_u))
      | Func (R1, R2) =>
        rel_expr_from_rel_expr kk res_R R2
            (kk_n_fold_join kk true R1 R2 (to_opt R1 arg_u) (to_r func_u))
        |> body_rep R2 = Formula Neut ? to_guard [arg_u] res_R
      | _ => raise NUT ("Nitpick_Kodkod.to_apply", [func_u])
    (* int -> rep -> rep -> KK.rel_expr -> nut *)
    and to_apply_vect k R' res_R func_r arg_u =
      let
        val arg_R = one_rep ofs (type_of arg_u) (unopt_rep (rep_of arg_u))
        val vect_r = vect_from_rel_expr kk k res_R (Vect (k, R')) func_r
        val vect_rs = unpack_vect_in_chunks kk (arity_of_rep res_R) k vect_r
      in
        kk_case_switch kk arg_R res_R (to_opt arg_R arg_u)
                       (all_singletons_for_rep arg_R) vect_rs
      end
    (* bool -> nut -> KK.formula *)
    and to_could_be_unrep neg u =
      if neg andalso is_opt_rep (rep_of u) then kk_no (to_r u) else KK.False
    (* nut -> KK.rel_expr -> KK.rel_expr *)
    and to_compare_with_unrep u r =
      if is_opt_rep (rep_of u) then
        kk_rel_if (kk_some (to_r u)) r (empty_rel_for_rep (rep_of u))
      else
        r
  in to_f_with_polarity Pos u end

end;
