(*  Title:      Pure/term_ord.ML
    Author:     Tobias Nipkow, TU Muenchen
    Author:     Makarius

Term orderings and scalable collections.
*)

signature ITEMS =
sig
  type key
  type 'a table
  val empty: 'a table
  val build: ('a table -> 'a table) -> 'a table
  val is_empty: 'a table -> bool
  val map: (key -> 'a -> 'b) -> 'a table -> 'b table
  val fold: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val fold_rev: (key * 'b -> 'a -> 'a) -> 'b table -> 'a -> 'a
  val size: 'a table -> int
  val dest: 'a table -> (key * 'a) list
  val keys: 'a table -> key list
  val exists: (key * 'a -> bool) -> 'a table -> bool
  val forall: (key * 'a -> bool) -> 'a table -> bool
  val get_first: (key * 'a -> 'b option) -> 'a table -> 'b option
  val lookup: 'a table -> key -> 'a option
  val defined: 'a table -> key -> bool
  val add: key * 'a -> 'a table -> 'a table
  val make: (key * 'a) list -> 'a table
  type set = unit table
  val add_set: key -> set -> set
  val make_set: key list -> set
  val subset: set * set -> bool
  val eq_set: set * set -> bool
end;

functor Items(Key: KEY): ITEMS =
struct

structure Table = Table(Key);

type key = Table.key;
type 'a table = 'a Table.table;

val empty = Table.empty;
val build = Table.build;
val is_empty = Table.is_empty;
val size = Table.size;
val dest = Table.dest;
val keys = Table.keys;
val exists = Table.exists;
val forall = Table.forall;
val get_first = Table.get_first;
val lookup = Table.lookup;
val defined = Table.defined;

fun add entry = Table.insert (K true) entry;
fun make entries = Table.build (fold add entries);

type set = unit table;

fun add_set x = add (x, ());
fun make_set xs = build (fold add_set xs);

fun subset (A: set, B: set) = forall (defined B o #1) A;
fun eq_set (A: set, B: set) = size A = size B andalso subset (A, B);

val map = Table.map;
val fold = Table.fold;
val fold_rev = Table.fold_rev;

end;

signature BASIC_TERM_ORD =
sig
  structure Vartab: TABLE
  structure Sorttab: TABLE
  structure Typtab: TABLE
  structure Termtab: TABLE
  structure Var_Graph: GRAPH
  structure Sort_Graph: GRAPH
  structure Typ_Graph: GRAPH
  structure Term_Graph: GRAPH
  structure TFrees:
  sig
    include ITEMS
    val add_tfreesT: typ -> set -> set
    val add_tfrees: term -> set -> set
  end
  structure TVars:
  sig
    include ITEMS
    val add_tvarsT: typ -> set -> set
    val add_tvars: term -> set -> set
  end
  structure Frees:
  sig
    include ITEMS
    val add_frees: term -> set -> set
  end
  structure Vars:
  sig
    include ITEMS
    val add_vars: term -> set -> set
  end
  structure Names:
  sig
    include ITEMS
    val add_tfree_namesT: typ -> set -> set
    val add_tfree_names: term -> set -> set
    val add_free_names: term -> set -> set
  end
end;

signature TERM_ORD =
sig
  include BASIC_TERM_ORD
  val fast_indexname_ord: indexname ord
  val sort_ord: sort ord
  val typ_ord: typ ord
  val fast_term_ord: term ord
  val syntax_term_ord: term ord
  val indexname_ord: indexname ord
  val tvar_ord: (indexname * sort) ord
  val var_ord: (indexname * typ) ord
  val term_ord: term ord
  val hd_ord: term ord
  val term_lpo: (term -> int) -> term ord
  val term_cache: (term -> 'a) -> term -> 'a
end;

structure Term_Ord: TERM_ORD =
struct

(* fast syntactic ordering -- tuned for inequalities *)

val fast_indexname_ord =
  pointer_eq_ord (int_ord o apply2 snd ||| fast_string_ord o apply2 fst);

val sort_ord =
  pointer_eq_ord (dict_ord fast_string_ord);

local

fun cons_nr (TVar _) = 0
  | cons_nr (TFree _) = 1
  | cons_nr (Type _) = 2;

in

fun typ_ord TU =
  if pointer_eq TU then EQUAL
  else
    (case TU of
      (Type (a, Ts), Type (b, Us)) =>
        (case fast_string_ord (a, b) of EQUAL => dict_ord typ_ord (Ts, Us) | ord => ord)
    | (TFree (a, S), TFree (b, S')) =>
        (case fast_string_ord (a, b) of EQUAL => sort_ord (S, S') | ord => ord)
    | (TVar (xi, S), TVar (yj, S')) =>
        (case fast_indexname_ord (xi, yj) of EQUAL => sort_ord (S, S') | ord => ord)
    | (T, U) => int_ord (cons_nr T, cons_nr U));

end;

local

fun cons_nr (Const _) = 0
  | cons_nr (Free _) = 1
  | cons_nr (Var _) = 2
  | cons_nr (Bound _) = 3
  | cons_nr (Abs _) = 4
  | cons_nr (_ $ _) = 5;

fun struct_ord (Abs (_, _, t), Abs (_, _, u)) = struct_ord (t, u)
  | struct_ord (t1 $ t2, u1 $ u2) =
      (case struct_ord (t1, u1) of EQUAL => struct_ord (t2, u2) | ord => ord)
  | struct_ord (t, u) = int_ord (cons_nr t, cons_nr u);

fun atoms_ord (Abs (_, _, t), Abs (_, _, u)) = atoms_ord (t, u)
  | atoms_ord (t1 $ t2, u1 $ u2) =
      (case atoms_ord (t1, u1) of EQUAL => atoms_ord (t2, u2) | ord => ord)
  | atoms_ord (Const (a, _), Const (b, _)) = fast_string_ord (a, b)
  | atoms_ord (Free (x, _), Free (y, _)) = fast_string_ord (x, y)
  | atoms_ord (Var (xi, _), Var (yj, _)) = fast_indexname_ord (xi, yj)
  | atoms_ord (Bound i, Bound j) = int_ord (i, j)
  | atoms_ord _ = EQUAL;

fun types_ord (Abs (_, T, t), Abs (_, U, u)) =
      (case typ_ord (T, U) of EQUAL => types_ord (t, u) | ord => ord)
  | types_ord (t1 $ t2, u1 $ u2) =
      (case types_ord (t1, u1) of EQUAL => types_ord (t2, u2) | ord => ord)
  | types_ord (Const (_, T), Const (_, U)) = typ_ord (T, U)
  | types_ord (Free (_, T), Free (_, U)) = typ_ord (T, U)
  | types_ord (Var (_, T), Var (_, U)) = typ_ord (T, U)
  | types_ord _ = EQUAL;

fun comments_ord (Abs (x, _, t), Abs (y, _, u)) =
      (case fast_string_ord (x, y) of EQUAL => comments_ord (t, u) | ord => ord)
  | comments_ord (t1 $ t2, u1 $ u2) =
      (case comments_ord (t1, u1) of EQUAL => comments_ord (t2, u2) | ord => ord)
  | comments_ord _ = EQUAL;

in

val fast_term_ord = pointer_eq_ord (struct_ord ||| atoms_ord ||| types_ord);

val syntax_term_ord = fast_term_ord ||| comments_ord;

end;


(* term_ord *)

(*a linear well-founded AC-compatible ordering for terms:
  s < t <=> 1. size(s) < size(t) or
            2. size(s) = size(t) and s=f(...) and t=g(...) and f<g or
            3. size(s) = size(t) and s=f(s1..sn) and t=f(t1..tn) and
               (s1..sn) < (t1..tn) (lexicographically)*)

val indexname_ord = int_ord o apply2 #2 ||| string_ord o apply2 #1;
val tvar_ord = prod_ord indexname_ord sort_ord;
val var_ord = prod_ord indexname_ord typ_ord;


local

fun hd_depth (t $ _, n) = hd_depth (t, n + 1)
  | hd_depth p = p;

fun dest_hd (Const (a, T)) = (((a, 0), T), 0)
  | dest_hd (Free (a, T)) = (((a, 0), T), 1)
  | dest_hd (Var v) = (v, 2)
  | dest_hd (Bound i) = ((("", i), dummyT), 3)
  | dest_hd (Abs (_, T, _)) = ((("", 0), T), 4);

in

fun term_ord tu =
  if pointer_eq tu then EQUAL
  else
    (case tu of
      (Abs (_, T, t), Abs(_, U, u)) =>
        (case term_ord (t, u) of EQUAL => typ_ord (T, U) | ord => ord)
    | (t, u) =>
        (case int_ord (size_of_term t, size_of_term u) of
          EQUAL =>
            (case prod_ord hd_ord int_ord (hd_depth (t, 0), hd_depth (u, 0)) of
              EQUAL => args_ord (t, u) | ord => ord)
        | ord => ord))
and hd_ord (f, g) =
  prod_ord (prod_ord indexname_ord typ_ord) int_ord (dest_hd f, dest_hd g)
and args_ord (f $ t, g $ u) =
      (case args_ord (f, g) of EQUAL => term_ord (t, u) | ord => ord)
  | args_ord _ = EQUAL;

end;


(* Lexicographic path order on terms *)

(*
  See Baader & Nipkow, Term rewriting, CUP 1998.
  Without variables.  Const, Var, Bound, Free and Abs are treated all as
  constants.

  f_ord maps terms to integers and serves two purposes:
  - Predicate on constant symbols.  Those that are not recognised by f_ord
    must be mapped to ~1.
  - Order on the recognised symbols.  These must be mapped to distinct
    integers >= 0.
  The argument of f_ord is never an application.
*)

local

fun unrecognized (Const (a, T)) = ((1, ((a, 0), T)), 0)
  | unrecognized (Free (a, T)) = ((1, ((a, 0), T)), 0)
  | unrecognized (Var v) = ((1, v), 1)
  | unrecognized (Bound i) = ((1, (("", i), dummyT)), 2)
  | unrecognized (Abs (_, T, _)) = ((1, (("", 0), T)), 3);

fun dest_hd f_ord t =
  let val ord = f_ord t
  in if ord = ~1 then unrecognized t else ((0, (("", ord), fastype_of t)), 0) end;

fun term_lpo f_ord (s, t) =
  let val (f, ss) = strip_comb s and (g, ts) = strip_comb t in
    if forall (fn si => term_lpo f_ord (si, t) = LESS) ss
    then case hd_ord f_ord (f, g) of
        GREATER =>
          if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
          then GREATER else LESS
      | EQUAL =>
          if forall (fn ti => term_lpo f_ord (s, ti) = GREATER) ts
          then list_ord (term_lpo f_ord) (ss, ts)
          else LESS
      | LESS => LESS
    else GREATER
  end
and hd_ord f_ord (f, g) = case (f, g) of
    (Abs (_, T, t), Abs (_, U, u)) =>
      (case term_lpo f_ord (t, u) of EQUAL => typ_ord (T, U) | ord => ord)
  | (_, _) => prod_ord (prod_ord int_ord
                  (prod_ord indexname_ord typ_ord)) int_ord
                (dest_hd f_ord f, dest_hd f_ord g);

in
val term_lpo = term_lpo
end;


(* scalable collections *)

structure Vartab = Table(type key = indexname val ord = fast_indexname_ord);
structure Sorttab = Table(type key = sort val ord = sort_ord);
structure Typtab = Table(type key = typ val ord = typ_ord);
structure Termtab = Table(type key = term val ord = fast_term_ord);

fun term_cache f = Cache.create Termtab.empty Termtab.lookup Termtab.update f;

structure Var_Graph = Graph(type key = indexname val ord = fast_indexname_ord);
structure Sort_Graph = Graph(type key = sort val ord = sort_ord);
structure Typ_Graph = Graph(type key = typ val ord = typ_ord);
structure Term_Graph = Graph(type key = term val ord = fast_term_ord);

structure TFrees =
struct
  structure Items =
    Items(type key = string * sort val ord = pointer_eq_ord (prod_ord fast_string_ord sort_ord));
  open Items;
  val add_tfreesT = fold_atyps (fn TFree v => add_set v | _ => I);
  val add_tfrees = fold_types add_tfreesT;
end;

structure TVars =
struct
  structure Items =
    Items(type key = indexname * sort val ord = pointer_eq_ord (prod_ord fast_indexname_ord sort_ord));
  open Items;
  val add_tvarsT = fold_atyps (fn TVar v => add_set v | _ => I);
  val add_tvars = fold_types add_tvarsT;
end;

structure Frees =
struct
  structure Items =
    Items(type key = string * typ val ord = pointer_eq_ord (prod_ord fast_string_ord typ_ord));
  open Items;
  val add_frees = fold_aterms (fn Free v => add_set v | _ => I);
end;

structure Vars =
struct
  structure Items =
    Items(type key = indexname * typ val ord = pointer_eq_ord (prod_ord fast_indexname_ord typ_ord));
  open Items;
  val add_vars = fold_aterms (fn Var v => add_set v | _ => I);
end;

structure Names =
struct
  structure Items = Items(type key = string val ord = fast_string_ord);
  open Items;
  val add_tfree_namesT = fold_atyps (fn TFree (a, _) => add_set a | _ => I);
  val add_tfree_names = fold_types add_tfree_namesT;
  val add_free_names = fold_aterms (fn Free (x, _) => add_set x | _ => I);
end;

end;

structure Basic_Term_Ord: BASIC_TERM_ORD = Term_Ord;
open Basic_Term_Ord;
