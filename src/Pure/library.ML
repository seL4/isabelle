(*  Title:      Pure/library.ML
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Author:     Markus Wenzel, TU Munich
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Basic library: functions, options, pairs, booleans, lists, integers,
rational numbers, strings, lists as sets, association lists, generic
tables, balanced trees, orders, current directory, misc.
*)

infix |> |>> |>>> ~~ \ \\ ins ins_string ins_int orf andf prefix upto downto
  mem mem_int mem_string union union_int union_string inter inter_int
  inter_string subset subset_int subset_string;

infix 3 oo ooo oooo;

signature LIBRARY =
sig
  (*functions*)
  val curry: ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry: ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val I: 'a -> 'a
  val K: 'a -> 'b -> 'a
  val |> : 'a * ('a -> 'b) -> 'b
  val |>> : ('a * 'b) * ('a -> 'c) -> 'c * 'b
  val |>>> : ('a * 'b) * ('a -> 'c * 'd) -> 'c * ('b * 'd)
  val apl: 'a * ('a * 'b -> 'c) -> 'b -> 'c
  val apr: ('a * 'b -> 'c) * 'b -> 'a -> 'c
  val funpow: int -> ('a -> 'a) -> 'a -> 'a
  val oo: ('a -> 'b) * ('c -> 'd -> 'a) -> 'c -> 'd -> 'b
  val ooo: ('a -> 'b) * ('c -> 'd -> 'e -> 'a) -> 'c -> 'd -> 'e -> 'b
  val oooo: ('a -> 'b) * ('c -> 'd -> 'e -> 'f -> 'a) -> 'c -> 'd -> 'e -> 'f -> 'b

  (*stamps*)
  type stamp
  val stamp: unit -> stamp

  (*options*)
  datatype 'a option = None | Some of 'a
  exception OPTION
  val the: 'a option -> 'a
  val if_none: 'a option -> 'a -> 'a
  val is_some: 'a option -> bool
  val is_none: 'a option -> bool
  val apsome: ('a -> 'b) -> 'a option -> 'b option
  exception ERROR
  val try: ('a -> 'b) -> 'a -> 'b option
  val can: ('a -> 'b) -> 'a -> bool
  datatype 'a result = Result of 'a | Exn of exn
  val capture: ('a -> 'b) -> 'a -> 'b result
  val release: 'a result -> 'a
  val get_result: 'a result -> 'a option
  val get_exn: 'a result -> exn option

  (*pairs*)
  val pair: 'a -> 'b -> 'a * 'b
  val rpair: 'a -> 'b -> 'b * 'a
  val fst: 'a * 'b -> 'a
  val snd: 'a * 'b -> 'b
  val eq_fst: (''a * 'b) * (''a * 'c) -> bool
  val eq_snd: ('a * ''b) * ('c * ''b) -> bool
  val swap: 'a * 'b -> 'b * 'a
  val apfst: ('a -> 'b) -> 'a * 'c -> 'b * 'c
  val apsnd: ('a -> 'b) -> 'c * 'a -> 'c * 'b
  val pairself: ('a -> 'b) -> 'a * 'a -> 'b * 'b

  (*booleans*)
  val equal: ''a -> ''a -> bool
  val not_equal: ''a -> ''a -> bool
  val orf: ('a -> bool) * ('a -> bool) -> 'a -> bool
  val andf: ('a -> bool) * ('a -> bool) -> 'a -> bool
  val exists: ('a -> bool) -> 'a list -> bool
  val forall: ('a -> bool) -> 'a list -> bool
  val set: bool ref -> bool
  val reset: bool ref -> bool
  val toggle: bool ref -> bool
  val change: 'a ref -> ('a -> 'a) -> unit
  val setmp: 'a ref -> 'a -> ('b -> 'c) -> 'b -> 'c
  val conditional: bool -> (unit -> unit) -> unit

  (*lists*)
  exception LIST of string
  val null: 'a list -> bool
  val hd: 'a list -> 'a
  val tl: 'a list -> 'a list
  val cons: 'a -> 'a list -> 'a list
  val single: 'a -> 'a list
  val append: 'a list -> 'a list -> 'a list
  val rev_append: 'a list -> 'a list -> 'a list
  val apply: ('a -> 'a) list -> 'a -> 'a
  val foldl: ('a * 'b -> 'a) -> 'a * 'b list -> 'a
  val foldr: ('a * 'b -> 'b) -> 'a list * 'b -> 'b
  val foldr1: ('a * 'a -> 'a) -> 'a list -> 'a
  val fold: ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val foldl_map: ('a * 'b -> 'a * 'c) -> 'a * 'b list -> 'a * 'c list
  val foldln: ('a * int -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val length: 'a list -> int
  val take: int * 'a list -> 'a list
  val drop: int * 'a list -> 'a list
  val splitAt: int * 'a list -> 'a list * 'a list
  val dropwhile: ('a -> bool) -> 'a list -> 'a list
  val nth_elem: int * 'a list -> 'a
  val map_nth_elem: int -> ('a -> 'a) -> 'a list -> 'a list
  val last_elem: 'a list -> 'a
  val split_last: 'a list -> 'a list * 'a
  val nth_update: 'a -> int * 'a list -> 'a list
  val find_index: ('a -> bool) -> 'a list -> int
  val find_index_eq: ''a -> ''a list -> int
  val find_first: ('a -> bool) -> 'a list -> 'a option
  val get_first: ('a -> 'b option) -> 'a list -> 'b option
  val flat: 'a list list -> 'a list
  val unflat: 'a list list -> 'b list -> 'b list list
  val seq: ('a -> unit) -> 'a list -> unit
  val separate: 'a -> 'a list -> 'a list
  val replicate: int -> 'a -> 'a list
  val multiply: 'a list * 'a list list -> 'a list list
  val product: 'a list -> 'b list -> ('a * 'b) list
  val filter: ('a -> bool) -> 'a list -> 'a list
  val filter_out: ('a -> bool) -> 'a list -> 'a list
  val mapfilter: ('a -> 'b option) -> 'a list -> 'b list
  val map2: ('a * 'b -> 'c) -> 'a list * 'b list -> 'c list
  val exists2: ('a * 'b -> bool) -> 'a list * 'b list -> bool
  val forall2: ('a * 'b -> bool) -> 'a list * 'b list -> bool
  val seq2: ('a * 'b -> unit) -> 'a list * 'b list -> unit
  val ~~ : 'a list * 'b list -> ('a * 'b) list
  val split_list: ('a * 'b) list -> 'a list * 'b list
  val equal_lists: ('a * 'b -> bool) -> 'a list * 'b list -> bool
  val prefix: ''a list * ''a list -> bool
  val take_prefix: ('a -> bool) -> 'a list -> 'a list * 'a list
  val take_suffix: ('a -> bool) -> 'a list -> 'a list * 'a list
  val prefixes1: 'a list -> 'a list list
  val suffixes1: 'a list -> 'a list list

  (*integers*)
  val gcd: int * int -> int
  val lcm: int * int -> int
  val inc: int ref -> int
  val dec: int ref -> int
  val upto: int * int -> int list
  val downto: int * int -> int list
  val downto0: int list * int -> bool
  val radixpand: int * int -> int list
  val radixstring: int * string * int -> string
  val string_of_int: int -> string
  val string_of_indexname: string * int -> string
  val read_radixint: int * string list -> int * string list
  val read_int: string list -> int * string list
  val oct_char: string -> string

  (*rational numbers*)
  type rat
  exception RAT of string
  val rep_rat: rat -> int * int
  val ratadd: rat * rat -> rat
  val ratmul: rat * rat -> rat
  val ratinv: rat -> rat
  val int_ratdiv: int * int -> rat
  val ratneg: rat -> rat
  val rat_of_int: int -> rat

  (*strings*)
  val nth_elem_string: int * string -> string
  val foldl_string: ('a * string -> 'a) -> 'a * string -> 'a
  val exists_string: (string -> bool) -> string -> bool
  val enclose: string -> string -> string -> string
  val unenclose: string -> string
  val quote: string -> string
  val space_implode: string -> string list -> string
  val commas: string list -> string
  val commas_quote: string list -> string
  val cat_lines: string list -> string
  val space_explode: string -> string -> string list
  val split_lines: string -> string list
  val prefix_lines: string -> string -> string
  val untabify: string list -> string list
  val suffix: string -> string -> string
  val unsuffix: string -> string -> string
  val replicate_string: int -> string -> string
  val translate_string: (string -> string) -> string -> string

  (*lists as sets*)
  val mem: ''a * ''a list -> bool
  val mem_int: int * int list -> bool
  val mem_string: string * string list -> bool
  val gen_mem: ('a * 'b -> bool) -> 'a * 'b list -> bool
  val ins: ''a * ''a list -> ''a list
  val ins_int: int * int list -> int list
  val ins_string: string * string list -> string list
  val gen_ins: ('a * 'a -> bool) -> 'a * 'a list -> 'a list
  val union: ''a list * ''a list -> ''a list
  val union_int: int list * int list -> int list
  val union_string: string list * string list -> string list
  val gen_union: ('a * 'a -> bool) -> 'a list * 'a list -> 'a list
  val gen_inter: ('a * 'b -> bool) -> 'a list * 'b list -> 'a list
  val inter: ''a list * ''a list -> ''a list
  val inter_int: int list * int list -> int list
  val inter_string: string list * string list -> string list
  val subset: ''a list * ''a list -> bool
  val subset_int: int list * int list -> bool
  val subset_string: string list * string list -> bool
  val eq_set: ''a list * ''a list -> bool
  val eq_set_string: string list * string list -> bool
  val gen_subset: ('a * 'b -> bool) -> 'a list * 'b list -> bool
  val \ : ''a list * ''a -> ''a list
  val \\ : ''a list * ''a list -> ''a list
  val gen_rem: ('a * 'b -> bool) -> 'a list * 'b -> 'a list
  val gen_rems: ('a * 'b -> bool) -> 'a list * 'b list -> 'a list
  val gen_distinct: ('a * 'a -> bool) -> 'a list -> 'a list
  val distinct: ''a list -> ''a list
  val findrep: ''a list -> ''a list
  val gen_duplicates: ('a * 'a -> bool) -> 'a list -> 'a list
  val duplicates: ''a list -> ''a list

  (*association lists*)
  val assoc: (''a * 'b) list * ''a -> 'b option
  val assoc_int: (int * 'a) list * int -> 'a option
  val assoc_string: (string * 'a) list * string -> 'a option
  val assoc_string_int: ((string * int) * 'a) list * (string * int) -> 'a option
  val assocs: (''a * 'b list) list -> ''a -> 'b list
  val assoc2: (''a * (''b * 'c) list) list * (''a * ''b) -> 'c option
  val gen_assoc: ('a * 'b -> bool) -> ('b * 'c) list * 'a -> 'c option
  val overwrite: (''a * 'b) list * (''a * 'b) -> (''a * 'b) list
  val gen_overwrite: ('a * 'a -> bool) -> ('a * 'b) list * ('a * 'b) -> ('a * 'b) list

  (*lists as tables*)
  val gen_merge_lists: ('a * 'a -> bool) -> 'a list -> 'a list -> 'a list
  val gen_merge_lists': ('a * 'a -> bool) -> 'a list -> 'a list -> 'a list
  val merge_lists: ''a list -> ''a list -> ''a list
  val merge_lists': ''a list -> ''a list -> ''a list
  val merge_alists: (''a * 'b) list -> (''a * 'b) list -> (''a * 'b) list

  (*balanced trees*)
  exception Balance
  val fold_bal: ('a * 'a -> 'a) -> 'a list -> 'a
  val access_bal: ('a -> 'a) * ('a -> 'a) * 'a -> int -> int -> 'a
  val accesses_bal: ('a -> 'a) * ('a -> 'a) * 'a -> int -> 'a list

  (*orders*)
  val rev_order: order -> order
  val make_ord: ('a * 'a -> bool) -> 'a * 'a -> order
  val int_ord: int * int -> order
  val string_ord: string * string -> order
  val prod_ord: ('a * 'b -> order) -> ('c * 'd -> order) -> ('a * 'c) * ('b * 'd) -> order
  val dict_ord: ('a * 'b -> order) -> 'a list * 'b list -> order
  val list_ord: ('a * 'b -> order) -> 'a list * 'b list -> order
  val sort: ('a * 'a -> order) -> 'a list -> 'a list
  val sort_strings: string list -> string list
  val sort_wrt: ('a -> string) -> 'a list -> 'a list
  val unique_strings: string list -> string list

  (*random numbers*)
  exception RANDOM
  val random: unit -> real
  val random_range: int -> int -> int
  val one_of: 'a list -> 'a
  val frequency: (int * 'a) list -> 'a

  (*current directory*)
  val cd: string -> unit
  val pwd: unit -> string

  (*misc*)
  val make_keylist: ('a -> 'b) -> 'a list -> ('a * 'b) list
  val keyfilter: ('a * ''b) list -> ''b -> 'a list
  val partition: ('a -> bool) -> 'a list -> 'a list * 'a list
  val partition_eq: ('a * 'a -> bool) -> 'a list -> 'a list list
  val partition_list: (int -> 'a -> bool) -> int -> int -> 'a list -> 'a list list
  val gensym: string -> string
  val scanwords: (string -> bool) -> string list -> string list
end;

structure Library: LIBRARY =
struct


(** functions **)

(*handy combinators*)
fun curry f x y = f (x, y);
fun uncurry f (x, y) = f x y;
fun I x = x;
fun K x y = x;

(*reverse apply*)
fun (x |> f) = f x;
fun ((x, y) |>> f) = (f x, y);
fun ((x, y) |>>> f) = let val (x', z) = f x in (x', (y, z)) end;

(*application of (infix) operator to its left or right argument*)
fun apl (x, f) y = f (x, y);
fun apr (f, y) x = f (x, y);

(*function exponentiation: f(...(f x)...) with n applications of f*)
fun funpow n f x =
  let fun rep (0, x) = x
        | rep (n, x) = rep (n - 1, f x)
  in rep (n, x) end;

(*concatenation: 2 and 3 args*)
fun (f oo g) x y = f (g x y);
fun (f ooo g) x y z = f (g x y z);
fun (f oooo g) x y z w = f (g x y z w);



(** stamps **)

type stamp = unit ref;
val stamp: unit -> stamp = ref;



(** options **)

datatype 'a option = None | Some of 'a;

exception OPTION;

fun the (Some x) = x
  | the None = raise OPTION;

(*strict!*)
fun if_none None y = y
  | if_none (Some x) _ = x;

fun is_some (Some _) = true
  | is_some None = false;

fun is_none (Some _) = false
  | is_none None = true;

fun apsome f (Some x) = Some (f x)
  | apsome _ None = None;


(* exception handling *)

exception ERROR;

fun try f x = Some (f x)
  handle Interrupt => raise Interrupt | ERROR => raise ERROR | _ => None;

fun can f x = is_some (try f x);


datatype 'a result =
  Result of 'a |
  Exn of exn;

fun capture f x = Result (f x) handle e => Exn e;

fun release (Result y) = y
  | release (Exn e) = raise e;

fun get_result (Result x) = Some x
  | get_result _ = None;

fun get_exn (Exn exn) = Some exn
  | get_exn _ = None;



(** pairs **)

fun pair x y = (x, y);
fun rpair x y = (y, x);

fun fst (x, y) = x;
fun snd (x, y) = y;

fun eq_fst ((x1, _), (x2, _)) = x1 = x2;
fun eq_snd ((_, y1), (_, y2)) = y1 = y2;

fun swap (x, y) = (y, x);

(*apply function to components*)
fun apfst f (x, y) = (f x, y);
fun apsnd f (x, y) = (x, f y);
fun pairself f (x, y) = (f x, f y);



(** booleans **)

(* equality *)

fun equal x y = x = y;
fun not_equal x y = x <> y;


(* operators for combining predicates *)

fun (p orf q) = fn x => p x orelse q x;
fun (p andf q) = fn x => p x andalso q x;


(* predicates on lists *)

(*exists pred [x1, ..., xn] ===> pred x1 orelse ... orelse pred xn*)
fun exists (pred: 'a -> bool) : 'a list -> bool =
  let fun boolf [] = false
        | boolf (x :: xs) = pred x orelse boolf xs
  in boolf end;

(*forall pred [x1, ..., xn] ===> pred x1 andalso ... andalso pred xn*)
fun forall (pred: 'a -> bool) : 'a list -> bool =
  let fun boolf [] = true
        | boolf (x :: xs) = pred x andalso boolf xs
  in boolf end;


(* flags *)

fun set flag = (flag := true; true);
fun reset flag = (flag := false; false);
fun toggle flag = (flag := not (! flag); ! flag);

fun change r f = r := f (! r);

(*temporarily set flag, handling exceptions*)
fun setmp flag value f x =
  let
    val orig_value = ! flag;
    fun return y = (flag := orig_value; y);
  in
    flag := value;
    return (f x handle exn => (return (); raise exn))
  end;


(* conditional execution *)

fun conditional b f = if b then f () else ();



(** lists **)

exception LIST of string;

fun null [] = true
  | null (_ :: _) = false;

fun hd [] = raise LIST "hd"
  | hd (x :: _) = x;

fun tl [] = raise LIST "tl"
  | tl (_ :: xs) = xs;

fun cons x xs = x :: xs;
fun single x = [x];

fun append xs ys = xs @ ys;

(* tail recursive version *)
fun rev_append [] ys = ys
  | rev_append (x :: xs) ys = rev_append xs (x :: ys);

fun apply [] x = x
  | apply (f :: fs) x = apply fs (f x);


(* fold *)

(*the following versions of fold are designed to fit nicely with infixes*)

(*  (op @) (e, [x1, ..., xn])  ===>  ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
fun foldl (f: 'a * 'b -> 'a) : 'a * 'b list -> 'a =
  let fun itl (e, [])  = e
        | itl (e, a::l) = itl (f(e, a), l)
  in  itl end;

(*  (op @) ([x1, ..., xn], e)  ===>   x1 @ (x2 ... @ (xn @ e))
    for operators that associate to the right (not tail recursive)*)
fun foldr f (l, e) =
  let fun itr [] = e
        | itr (a::l) = f(a, itr l)
  in  itr l  end;

(*  (op @) [x1, ..., xn]  ===>   x1 @ (x2 ... @ (x[n-1] @ xn))
    for n > 0, operators that associate to the right (not tail recursive)*)
fun foldr1 f l =
  let fun itr [x] = x
        | itr (x::l) = f(x, itr l)
  in  itr l  end;

fun fold f xs y = foldl (fn (y', x) => f x y') (y, xs);

fun foldl_map _ (x, []) = (x, [])
  | foldl_map f (x, y :: ys) =
      let
        val (x', y') = f (x, y);
        val (x'', ys') = foldl_map f (x', ys);
      in (x'', y' :: ys') end;

fun foldln f xs e = fst (foldl (fn ((e,i), x) => (f (x,i) e, i+1)) ((e,1),xs));

(* basic list functions *)

(*length of a list, should unquestionably be a standard function*)
local fun length1 (n, [])  = n   (*TAIL RECURSIVE*)
        | length1 (n, x :: xs) = length1 (n + 1, xs)
in  fun length l = length1 (0, l) end;

(*take the first n elements from a list*)
fun take (n, []) = []
  | take (n, x :: xs) =
      if n > 0 then x :: take (n - 1, xs) else [];

(*drop the first n elements from a list*)
fun drop (n, []) = []
  | drop (n, x :: xs) =
      if n > 0 then drop (n - 1, xs) else x :: xs;

fun splitAt(n,[]) = ([],[])
  | splitAt(n,xs as x::ys) =
      if n>0 then let val (ps,qs) = splitAt(n-1,ys) in (x::ps,qs) end
      else ([],xs)

fun dropwhile P [] = []
  | dropwhile P (ys as x::xs) = if P x then dropwhile P xs else ys;

(*return nth element of a list, where 0 designates the first element;
  raise EXCEPTION if list too short*)
fun nth_elem NL =
  (case drop NL of
    [] => raise LIST "nth_elem"
  | x :: _ => x);

fun map_nth_elem 0 f (x :: xs) = f x :: xs
  | map_nth_elem n f (x :: xs) = x :: map_nth_elem (n - 1) f xs
  | map_nth_elem _ _ [] = raise LIST "map_nth_elem";

(*last element of a list*)
fun last_elem [] = raise LIST "last_elem"
  | last_elem [x] = x
  | last_elem (_ :: xs) = last_elem xs;

(*rear decomposition*)
fun split_last [] = raise LIST "split_last"
  | split_last [x] = ([], x)
  | split_last (x :: xs) = apfst (cons x) (split_last xs);

(*update nth element*)
fun nth_update x n_xs =
    (case splitAt n_xs of
      (_,[]) => raise LIST "nth_update"
    | (prfx, _ :: sffx') => prfx @ (x :: sffx'))

(*find the position of an element in a list*)
fun find_index pred =
  let fun find _ [] = ~1
        | find n (x :: xs) = if pred x then n else find (n + 1) xs;
  in find 0 end;

fun find_index_eq x = find_index (equal x);

(*find first element satisfying predicate*)
fun find_first _ [] = None
  | find_first pred (x :: xs) =
      if pred x then Some x else find_first pred xs;

(*get first element by lookup function*)
fun get_first _ [] = None
  | get_first f (x :: xs) =
      (case f x of
        None => get_first f xs
      | some => some);

(*flatten a list of lists to a list*)
fun flat (ls: 'c list list) : 'c list = foldr (op @) (ls, []);

fun unflat (xs :: xss) ys =
      let val (ps,qs) = splitAt(length xs,ys)
      in ps :: unflat xss qs end
  | unflat [] [] = []
  | unflat _ _ = raise LIST "unflat";

(*like Lisp's MAPC -- seq proc [x1, ..., xn] evaluates
  (proc x1; ...; proc xn) for side effects*)
fun seq (proc: 'a -> unit) : 'a list -> unit =
  let fun seqf [] = ()
        | seqf (x :: xs) = (proc x; seqf xs)
  in seqf end;

(*separate s [x1, x2, ..., xn]  ===>  [x1, s, x2, s, ..., s, xn]*)
fun separate s (x :: (xs as _ :: _)) = x :: s :: separate s xs
  | separate _ xs = xs;

(*make the list [x, x, ..., x] of length n*)
fun replicate n (x: 'a) : 'a list =
  let fun rep (0, xs) = xs
        | rep (n, xs) = rep (n - 1, x :: xs)
  in
    if n < 0 then raise LIST "replicate"
    else rep (n, [])
  end;

fun translate_string f = String.translate (f o String.str);

(*multiply [a, b, c, ...] * [xs, ys, zs, ...]*)
fun multiply ([], _) = []
  | multiply (x :: xs, yss) = map (cons x) yss @ multiply (xs, yss);

(*direct product*)
fun product _ [] = []
  | product [] _ = []
  | product (x :: xs) ys = map (pair x) ys @ product xs ys;


(* filter *)

(*copy the list preserving elements that satisfy the predicate*)
fun filter (pred: 'a->bool) : 'a list -> 'a list =
  let fun filt [] = []
        | filt (x :: xs) = if pred x then x :: filt xs else filt xs
  in filt end;

fun filter_out f = filter (not o f);

fun mapfilter (f: 'a -> 'b option) ([]: 'a list) = [] : 'b list
  | mapfilter f (x :: xs) =
      (case f x of
        None => mapfilter f xs
      | Some y => y :: mapfilter f xs);


(* lists of pairs *)

fun map2 _ ([], []) = []
  | map2 f (x :: xs, y :: ys) = (f (x, y) :: map2 f (xs, ys))
  | map2 _ _ = raise LIST "map2";

fun exists2 _ ([], []) = false
  | exists2 pred (x :: xs, y :: ys) = pred (x, y) orelse exists2 pred (xs, ys)
  | exists2 _ _ = raise LIST "exists2";

fun forall2 _ ([], []) = true
  | forall2 pred (x :: xs, y :: ys) = pred (x, y) andalso forall2 pred (xs, ys)
  | forall2 _ _ = raise LIST "forall2";

fun seq2 _ ([], []) = ()
  | seq2 f (x :: xs, y :: ys) = (f (x, y); seq2 f (xs, ys))
  | seq2 _ _ = raise LIST "seq2";

(*combine two lists forming a list of pairs:
  [x1, ..., xn] ~~ [y1, ..., yn]  ===>  [(x1, y1), ..., (xn, yn)]*)
fun [] ~~ [] = []
  | (x :: xs) ~~ (y :: ys) = (x, y) :: (xs ~~ ys)
  | _ ~~ _ = raise LIST "~~";

(*inverse of ~~; the old 'split':
  [(x1, y1), ..., (xn, yn)]  ===>  ([x1, ..., xn], [y1, ..., yn])*)
fun split_list (l: ('a * 'b) list) = (map #1 l, map #2 l);

fun equal_lists eq (xs, ys) = length xs = length ys andalso forall2 eq (xs, ys);


(* prefixes, suffixes *)

fun [] prefix _ = true
  | (x :: xs) prefix (y :: ys) = x = y andalso (xs prefix ys)
  | _ prefix _ = false;

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., x(i-1)], [xi, ..., xn])
   where xi is the first element that does not satisfy the predicate*)
fun take_prefix (pred : 'a -> bool)  (xs: 'a list) : 'a list * 'a list =
  let fun take (rxs, []) = (rev rxs, [])
        | take (rxs, x :: xs) =
            if  pred x  then  take(x :: rxs, xs)  else  (rev rxs, x :: xs)
  in  take([], xs)  end;

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., xi], [x(i+1), ..., xn])
   where xi is the last element that does not satisfy the predicate*)
fun take_suffix _ [] = ([], [])
  | take_suffix pred (x :: xs) =
      (case take_suffix pred xs of
        ([], sffx) => if pred x then ([], x :: sffx) else ([x], sffx)
      | (prfx, sffx) => (x :: prfx, sffx));

fun prefixes1 [] = []
  | prefixes1 (x :: xs) = map (cons x) ([] :: prefixes1 xs);

fun suffixes1 xs = map rev (prefixes1 (rev xs));



(** integers **)

fun gcd(x,y) =
  let fun gxd x y =
    if y = 0 then x else gxd y (x mod y)
  in if x < y then gxd y x else gxd x y end;

fun lcm(x,y) = (x * y) div gcd(x,y);

fun inc i = (i := ! i + 1; ! i);
fun dec i = (i := ! i - 1; ! i);


(* lists of integers *)

(*make the list [from, from + 1, ..., to]*)
fun (from upto to) =
  if from > to then [] else from :: ((from + 1) upto to);

(*make the list [from, from - 1, ..., to]*)
fun (from downto to) =
  if from < to then [] else from :: ((from - 1) downto to);

(*predicate: downto0 (is, n) <=> is = [n, n - 1, ..., 0]*)
fun downto0 (i :: is, n) = i = n andalso downto0 (is, n - 1)
  | downto0 ([], n) = n = ~1;


(* convert integers to strings *)

(*expand the number in the given base;
  example: radixpand (2, 8) gives [1, 0, 0, 0]*)
fun radixpand (base, num) : int list =
  let
    fun radix (n, tail) =
      if n < base then n :: tail
      else radix (n div base, (n mod base) :: tail)
  in radix (num, []) end;

(*expands a number into a string of characters starting from "zerochar";
  example: radixstring (2, "0", 8) gives "1000"*)
fun radixstring (base, zerochar, num) =
  let val offset = ord zerochar;
      fun chrof n = chr (offset + n)
  in implode (map chrof (radixpand (base, num))) end;


val string_of_int = Int.toString;

fun string_of_indexname (a,0) = a
  | string_of_indexname (a,i) = a ^ "_" ^ Int.toString i;


(* read integers *)

fun read_radixint (radix: int, cs) : int * string list =
  let val zero = ord"0"
      val limit = zero+radix
      fun scan (num,[]) = (num,[])
        | scan (num, c::cs) =
              if  zero <= ord c  andalso  ord c < limit
              then scan(radix*num + ord c - zero, cs)
              else (num, c::cs)
  in  scan(0,cs)  end;

fun read_int cs = read_radixint (10, cs);

fun oct_char s = chr (#1 (read_radixint (8, explode s)));



(** strings **)

(*functions tuned for strings, avoiding explode*)

fun nth_elem_string (i, str) =
  (case try String.substring (str, i, 1) of
    Some s => s
  | None => raise LIST "nth_elem_string");

fun foldl_string f (x0, str) =
  let
    val n = size str;
    fun fold (x, i) =
      if i < n then fold (f (x, String.substring (str, i, 1)), i + 1) else x;
  in fold (x0, 0) end;

fun exists_string pred str =
  let
    val n = size str;
    fun ex i = i < n andalso (pred (String.substring (str, i, 1)) orelse ex (i + 1));
  in ex 0 end;

(*enclose in brackets*)
fun enclose lpar rpar str = lpar ^ str ^ rpar;
fun unenclose str = String.substring (str, 1, size str - 2);

(*simple quoting (does not escape special chars)*)
val quote = enclose "\"" "\"";

(*space_implode "..." (explode "hello") = "h...e...l...l...o"*)
fun space_implode a bs = implode (separate a bs);

val commas = space_implode ", ";
val commas_quote = commas o map quote;

(*concatenate messages, one per line, into a string*)
val cat_lines = space_implode "\n";

(*space_explode "." "h.e..l.lo" = ["h", "e", "", "l", "lo"]*)
fun space_explode _ "" = []
  | space_explode sep str =
      let
        fun expl chs =
          (case take_prefix (not_equal sep) chs of
            (cs, []) => [implode cs]
          | (cs, _ :: cs') => implode cs :: expl cs');
      in expl (explode str) end;

val split_lines = space_explode "\n";

fun prefix_lines "" txt = txt
  | prefix_lines prfx txt = txt |> split_lines |> map (fn s => prfx ^ s) |> cat_lines;

(*untabify*)
fun untabify chs =
  let
    val tab_width = 8;

    fun untab (_, "\n") = (0, ["\n"])
      | untab (pos, "\t") =
          let val d = tab_width - (pos mod tab_width) in (pos + d, replicate d " ") end
      | untab (pos, c) = (pos + 1, [c]);
  in
    if not (exists (equal "\t") chs) then chs
    else flat (#2 (foldl_map untab (0, chs)))
  end;

(*append suffix*)
fun suffix sfx s = s ^ sfx;

(*remove suffix*)
fun unsuffix sfx s =
  let
    val cs = explode s;
    val prfx_len = size s - size sfx;
  in
    if prfx_len >= 0 andalso implode (drop (prfx_len, cs)) = sfx then
      implode (take (prfx_len, cs))
    else raise LIST "unsuffix"
  end;

fun replicate_string 0 _ = ""
  | replicate_string 1 a = a
  | replicate_string k a =
      if k mod 2 = 0 then replicate_string (k div 2) (a ^ a)
      else replicate_string (k div 2) (a ^ a) ^ a;



(** lists as sets **)

(*membership in a list*)
fun x mem [] = false
  | x mem (y :: ys) = x = y orelse x mem ys;

(*membership in a list, optimized version for ints*)
fun (x:int) mem_int [] = false
  | x mem_int (y :: ys) = x = y orelse x mem_int ys;

(*membership in a list, optimized version for strings*)
fun (x:string) mem_string [] = false
  | x mem_string (y :: ys) = x = y orelse x mem_string ys;

(*generalized membership test*)
fun gen_mem eq (x, []) = false
  | gen_mem eq (x, y :: ys) = eq (x, y) orelse gen_mem eq (x, ys);


(*insertion into list if not already there*)
fun (x ins xs) = if x mem xs then xs else x :: xs;

(*insertion into list, optimized version for ints*)
fun (x ins_int xs) = if x mem_int xs then xs else x :: xs;

(*insertion into list, optimized version for strings*)
fun (x ins_string xs) = if x mem_string xs then xs else x :: xs;

(*generalized insertion*)
fun gen_ins eq (x, xs) = if gen_mem eq (x, xs) then xs else x :: xs;


(*union of sets represented as lists: no repetitions*)
fun xs union [] = xs
  | [] union ys = ys
  | (x :: xs) union ys = xs union (x ins ys);

(*union of sets, optimized version for ints*)
fun (xs:int list) union_int [] = xs
  | [] union_int ys = ys
  | (x :: xs) union_int ys = xs union_int (x ins_int ys);

(*union of sets, optimized version for strings*)
fun (xs:string list) union_string [] = xs
  | [] union_string ys = ys
  | (x :: xs) union_string ys = xs union_string (x ins_string ys);

(*generalized union*)
fun gen_union eq (xs, []) = xs
  | gen_union eq ([], ys) = ys
  | gen_union eq (x :: xs, ys) = gen_union eq (xs, gen_ins eq (x, ys));


(*intersection*)
fun [] inter ys = []
  | (x :: xs) inter ys =
      if x mem ys then x :: (xs inter ys) else xs inter ys;

(*intersection, optimized version for ints*)
fun ([]:int list) inter_int ys = []
  | (x :: xs) inter_int ys =
      if x mem_int ys then x :: (xs inter_int ys) else xs inter_int ys;

(*intersection, optimized version for strings *)
fun ([]:string list) inter_string ys = []
  | (x :: xs) inter_string ys =
      if x mem_string ys then x :: (xs inter_string ys) else xs inter_string ys;

(*generalized intersection*)
fun gen_inter eq ([], ys) = []
  | gen_inter eq (x::xs, ys) =
      if gen_mem eq (x,ys) then x :: gen_inter eq (xs, ys)
                           else      gen_inter eq (xs, ys);


(*subset*)
fun [] subset ys = true
  | (x :: xs) subset ys = x mem ys andalso xs subset ys;

(*subset, optimized version for ints*)
fun ([]:int list) subset_int ys = true
  | (x :: xs) subset_int ys = x mem_int ys andalso xs subset_int ys;

(*subset, optimized version for strings*)
fun ([]:string list) subset_string ys = true
  | (x :: xs) subset_string ys = x mem_string ys andalso xs subset_string ys;

(*set equality*)
fun eq_set (xs, ys) =
  xs = ys orelse (xs subset ys andalso ys subset xs);

(*set equality for strings*)
fun eq_set_string ((xs:string list), ys) =
  xs = ys orelse (xs subset_string ys andalso ys subset_string xs);

fun gen_subset eq (xs, ys) = forall (fn x => gen_mem eq (x, ys)) xs;


(*removing an element from a list WITHOUT duplicates*)
fun (y :: ys) \ x = if x = y then ys else y :: (ys \ x)
  | [] \ x = [];

fun ys \\ xs = foldl (op \) (ys,xs);

(*removing an element from a list -- possibly WITH duplicates*)
fun gen_rem eq (xs, y) = filter_out (fn x => eq (x, y)) xs;
fun gen_rems eq (xs, ys) = filter_out (fn x => gen_mem eq (x, ys)) xs;


(*makes a list of the distinct members of the input; preserves order, takes
  first of equal elements*)
fun gen_distinct eq lst =
  let
    val memb = gen_mem eq;

    fun dist (rev_seen, []) = rev rev_seen
      | dist (rev_seen, x :: xs) =
          if memb (x, rev_seen) then dist (rev_seen, xs)
          else dist (x :: rev_seen, xs);
  in
    dist ([], lst)
  end;

fun distinct l = gen_distinct (op =) l;


(*returns the tail beginning with the first repeated element, or []*)
fun findrep [] = []
  | findrep (x :: xs) = if x mem xs then x :: xs else findrep xs;


(*returns a list containing all repeated elements exactly once; preserves
  order, takes first of equal elements*)
fun gen_duplicates eq lst =
  let
    val memb = gen_mem eq;

    fun dups (rev_dups, []) = rev rev_dups
      | dups (rev_dups, x :: xs) =
          if memb (x, rev_dups) orelse not (memb (x, xs)) then
            dups (rev_dups, xs)
          else dups (x :: rev_dups, xs);
  in
    dups ([], lst)
  end;

fun duplicates l = gen_duplicates (op =) l;



(** association lists **)

(*association list lookup*)
fun assoc ([], key) = None
  | assoc ((keyi, xi) :: pairs, key) =
      if key = keyi then Some xi else assoc (pairs, key);

(*association list lookup, optimized version for ints*)
fun assoc_int ([], (key:int)) = None
  | assoc_int ((keyi, xi) :: pairs, key) =
      if key = keyi then Some xi else assoc_int (pairs, key);

(*association list lookup, optimized version for strings*)
fun assoc_string ([], (key:string)) = None
  | assoc_string ((keyi, xi) :: pairs, key) =
      if key = keyi then Some xi else assoc_string (pairs, key);

(*association list lookup, optimized version for string*ints*)
fun assoc_string_int ([], (key:string*int)) = None
  | assoc_string_int ((keyi, xi) :: pairs, key) =
      if key = keyi then Some xi else assoc_string_int (pairs, key);

fun assocs ps x =
  (case assoc (ps, x) of
    None => []
  | Some ys => ys);

(*two-fold association list lookup*)
fun assoc2 (aal, (key1, key2)) =
  (case assoc (aal, key1) of
    Some al => assoc (al, key2)
  | None => None);

(*generalized association list lookup*)
fun gen_assoc eq ([], key) = None
  | gen_assoc eq ((keyi, xi) :: pairs, key) =
      if eq (key, keyi) then Some xi else gen_assoc eq (pairs, key);

(*association list update*)
fun overwrite (al, p as (key, _)) =
  let fun over ((q as (keyi, _)) :: pairs) =
            if keyi = key then p :: pairs else q :: (over pairs)
        | over [] = [p]
  in over al end;

fun gen_overwrite eq (al, p as (key, _)) =
  let fun over ((q as (keyi, _)) :: pairs) =
            if eq (keyi, key) then p :: pairs else q :: (over pairs)
        | over [] = [p]
  in over al end;


(* lists as tables *)

fun gen_merge_lists _ xs [] = xs
  | gen_merge_lists _ [] ys = ys
  | gen_merge_lists eq xs ys = xs @ gen_rems eq (ys, xs);

fun gen_merge_lists' _ xs [] = xs
  | gen_merge_lists' _ [] ys = ys
  | gen_merge_lists' eq xs ys = gen_rems eq (ys, xs) @ xs;

fun merge_lists xs ys = gen_merge_lists (op =) xs ys;
fun merge_lists' xs ys = gen_merge_lists' (op =) xs ys;
fun merge_alists al = gen_merge_lists eq_fst al;



(** balanced trees **)

exception Balance;      (*indicates non-positive argument to balancing fun*)

(*balanced folding; avoids deep nesting*)
fun fold_bal f [x] = x
  | fold_bal f [] = raise Balance
  | fold_bal f xs =
      let val (ps,qs) = splitAt(length xs div 2, xs)
      in  f (fold_bal f ps, fold_bal f qs)  end;

(*construct something of the form f(...g(...(x)...)) for balanced access*)
fun access_bal (f, g, x) n i =
  let fun acc n i =     (*1<=i<=n*)
          if n=1 then x else
          let val n2 = n div 2
          in  if i<=n2 then f (acc n2 i)
                       else g (acc (n-n2) (i-n2))
          end
  in  if 1<=i andalso i<=n then acc n i else raise Balance  end;

(*construct ALL such accesses; could try harder to share recursive calls!*)
fun accesses_bal (f, g, x) n =
  let fun acc n =
          if n=1 then [x] else
          let val n2 = n div 2
              val acc2 = acc n2
          in  if n-n2=n2 then map f acc2 @ map g acc2
                         else map f acc2 @ map g (acc (n-n2)) end
  in  if 1<=n then acc n else raise Balance  end;



(** orders **)

fun rev_order LESS = GREATER
  | rev_order EQUAL = EQUAL
  | rev_order GREATER = LESS;

(*assume rel is a linear strict order*)
fun make_ord rel (x, y) =
  if rel (x, y) then LESS
  else if rel (y, x) then GREATER
  else EQUAL;

(*Better to use Int.compare*)
fun int_ord (i, j: int) =
  if i < j then LESS
  else if i = j then EQUAL
  else GREATER;

(*Better to use String.compare*)
fun string_ord (a, b: string) =
  if a < b then LESS
  else if a = b then EQUAL
  else GREATER;

(*lexicographic product*)
fun prod_ord a_ord b_ord ((x, y), (x', y')) =
  (case a_ord (x, x') of EQUAL => b_ord (y, y') | ord => ord);

(*dictionary order -- in general NOT well-founded!*)
fun dict_ord _ ([], []) = EQUAL
  | dict_ord _ ([], _ :: _) = LESS
  | dict_ord _ (_ :: _, []) = GREATER
  | dict_ord elem_ord (x :: xs, y :: ys) =
      (case elem_ord (x, y) of EQUAL => dict_ord elem_ord (xs, ys) | ord => ord);

(*lexicographic product of lists*)
fun list_ord elem_ord (xs, ys) =
  prod_ord int_ord (dict_ord elem_ord) ((length xs, xs), (length ys, ys));


(* sorting *)

(*quicksort (stable, i.e. does not reorder equal elements)*)
fun sort ord =
  let
    fun qsort xs =
      let val len = length xs in
        if len <= 1 then xs
        else
          let val (lts, eqs, gts) = part (nth_elem (len div 2, xs)) xs in
            qsort lts @ eqs @ qsort gts
          end
      end
    and part _ [] = ([], [], [])
      | part pivot (x :: xs) = add (ord (x, pivot)) x (part pivot xs)
    and add LESS x (lts, eqs, gts) = (x :: lts, eqs, gts)
      | add EQUAL x (lts, eqs, gts) = (lts, x :: eqs, gts)
      | add GREATER x (lts, eqs, gts) = (lts, eqs, x :: gts);
  in qsort end;

(*sort strings*)
val sort_strings = sort string_ord;
fun sort_wrt sel xs = sort (string_ord o pairself sel) xs;

fun unique_strings ([]: string list) = []
  | unique_strings [x] = [x]
  | unique_strings (x :: y :: ys) =
      if x = y then unique_strings (y :: ys)
      else x :: unique_strings (y :: ys);


(** random numbers **)

exception RANDOM;

fun rmod x y = x - y * Real.realFloor (x / y);

local
  val a = 16807.0;
  val m = 2147483647.0;
  val random_seed = ref 1.0;
in

fun random () =
  let val r = rmod (a * !random_seed) m
  in (random_seed := r; r) end;

end;

fun random_range l h =
  if h < l orelse l < 0 then raise RANDOM
  else l + Real.floor (rmod (random ()) (real (h - l + 1)));

fun one_of xs = nth_elem (random_range 0 (length xs - 1), xs);

fun frequency xs =
  let
    val sum = foldl op + (0, map fst xs);
    fun pick n ((k, x) :: xs) =
      if n <= k then x else pick (n - k) xs
  in pick (random_range 1 sum) xs end;


(** current directory **)

val cd = OS.FileSys.chDir;
val pwd = OS.FileSys.getDir;



(** rational numbers **)

datatype rat = Rat of bool * int * int

exception RAT of string;

fun rep_rat(Rat(a,p,q)) = (if a then p else ~p,q)

fun ratnorm(a,p,q) = if p=0 then Rat(a,0,1) else
  let val absp = abs p
      val m = gcd(absp,q)
  in Rat(a = (0 <= p), absp div m, q div m) end;

fun ratadd(Rat(a,p,q),Rat(b,r,s)) =
  let val den = lcm(q,s)
      val p = p*(den div q) and r = r*(den div s)
      val num = (if a then p else ~p) + (if b then r else ~r)
  in ratnorm(true,num,den) end;

fun ratmul(Rat(a,p,q),Rat(b,r,s)) = ratnorm(a=b,p*r,q*s)

fun ratinv(Rat(a,p,q)) = if p=0 then raise RAT "ratinv" else Rat(a,q,p)

fun int_ratdiv(p,q) =
  if q=0 then raise RAT "int_ratdiv" else ratnorm(0<=q, p, abs q)

fun ratneg(Rat(b,p,q)) = Rat(not b,p,q);

fun rat_of_int i = if i < 0 then Rat(false,abs i,1) else Rat(true,i,1);


(** misc **)

(*use the keyfun to make a list of (x, key) pairs*)
fun make_keylist (keyfun: 'a->'b) : 'a list -> ('a * 'b) list =
  let fun keypair x = (x, keyfun x)
  in map keypair end;

(*given a list of (x, key) pairs and a searchkey
  return the list of xs from each pair whose key equals searchkey*)
fun keyfilter [] searchkey = []
  | keyfilter ((x, key) :: pairs) searchkey =
      if key = searchkey then x :: keyfilter pairs searchkey
      else keyfilter pairs searchkey;


(*Partition list into elements that satisfy predicate and those that don't.
  Preserves order of elements in both lists.*)
fun partition (pred: 'a->bool) (ys: 'a list) : ('a list * 'a list) =
    let fun part ([], answer) = answer
          | part (x::xs, (ys, ns)) = if pred(x)
            then  part (xs, (x::ys, ns))
            else  part (xs, (ys, x::ns))
    in  part (rev ys, ([], []))  end;


fun partition_eq (eq:'a * 'a -> bool) =
    let fun part [] = []
          | part (x::ys) = let val (xs, xs') = partition (apl(x, eq)) ys
                           in (x::xs)::(part xs') end
    in part end;


(*Partition a list into buckets  [ bi, b(i+1), ..., bj ]
   putting x in bk if p(k)(x) holds.  Preserve order of elements if possible.*)
fun partition_list p i j =
  let fun part k xs =
            if k>j then
              (case xs of [] => []
                         | _ => raise LIST "partition_list")
            else
            let val (ns, rest) = partition (p k) xs;
            in  ns :: part(k+1)rest  end
  in  part i end;


(* generating identifiers *)

(** Freshly generated identifiers; supplied prefix MUST start with a letter **)
local
(*Maps 0-63 to A-Z, a-z, 0-9 or _ or ' for generating random identifiers*)
fun char i =      if i<26 then chr (ord "A" + i)
             else if i<52 then chr (ord "a" + i - 26)
             else if i<62 then chr (ord"0" + i - 52)
             else if i=62 then "_"
             else  (*i=63*)    "'";

val charVec = Vector.tabulate (64, char);

fun newid n =
  let
  in  implode (map (fn i => Vector.sub(charVec,i)) (radixpand (64,n)))  end;

val seedr = ref 0;

in

fun gensym pre = pre ^ (#1(newid (!seedr), inc seedr));

end;


(* lexical scanning *)

(*scan a list of characters into "words" composed of "letters" (recognized by
  is_let) and separated by any number of non-"letters"*)
fun scanwords is_let cs =
  let fun scan1 [] = []
        | scan1 cs =
            let val (lets, rest) = take_prefix is_let cs
            in implode lets :: scanwords is_let rest end;
  in scan1 (#2 (take_prefix (not o is_let) cs)) end;


end;

open Library;
