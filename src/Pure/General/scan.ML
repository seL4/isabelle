(*  Title:      Pure/General/scan.ML
    ID:         $Id$
    Author:     Markus Wenzel and Tobias Nipkow, TU Muenchen

Generic scanners (for potentially infinite input).
*)

infix 5 -- :-- |-- --| ^^;
infix 3 >>;
infix 0 ||;

signature BASIC_SCAN =
sig
  (*error msg handler*)
  val !! : ('a * string option -> string) -> ('a -> 'b) -> 'a -> 'b
  (*apply function*)
  val >> : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
  (*alternative*)
  val || : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  (*sequential pairing*)
  val -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  (*dependent pairing*)
  val :-- : ('a -> 'b * 'c) * ('b -> 'c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  (*forget fst*)
  val |-- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'd * 'e
  (*forget snd*)
  val --| : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'b * 'e
  (*concatenation*)
  val ^^ : ('a -> string * 'b) * ('b -> string * 'c) -> 'a -> string * 'c
  (*one element literal*)
  val $$ : string -> string list -> string * string list
  val ~$$ : string -> string list -> string * string list
end;

signature SCAN =
sig
  include BASIC_SCAN
  val fail: 'a -> 'b
  val fail_with: ('a -> string) -> 'a -> 'b
  val succeed: 'a -> 'b -> 'a * 'b
  val some: ('a -> 'b option) -> 'a list -> 'b * 'a list
  val one: ('a -> bool) -> 'a list -> 'a * 'a list
  val this: string list -> string list -> string list * string list
  val this_string: string -> string list -> string * string list
  val any: ('a -> bool) -> 'a list -> 'a list * 'a list
  val any1: ('a -> bool) -> 'a list -> 'a list * 'a list
  val optional: ('a -> 'b * 'a) -> 'b -> 'a -> 'b * 'a
  val option: ('a -> 'b * 'a) -> 'a -> 'b option * 'a
  val repeat: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val repeat1: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val max: ('a * 'a -> bool) -> ('b -> 'a * 'b) -> ('b -> 'a * 'b) -> 'b -> 'a * 'b
  val ahead: ('a -> 'b * 'c) -> 'a -> 'b * 'a
  val unless: ('a -> 'b * 'a) -> ('a -> 'c * 'd) -> 'a -> 'c * 'd
  val first: ('a -> 'b) list -> 'a -> 'b
  val state: 'a * 'b -> 'a * ('a * 'b)
  val depend: ('a -> 'b -> ('c * 'd) * 'e) -> 'a * 'b -> 'd * ('c * 'e)
  val peek: ('a -> 'b -> 'c * 'd) -> 'a * 'b -> 'c * ('a * 'd)
  val pass: 'a -> ('a * 'b -> 'c * ('d * 'e)) -> 'b -> 'c * 'e
  val lift: ('a -> 'b * 'c) -> 'd * 'a -> 'b * ('d * 'c)
  val trace': ('a * 'b list -> 'c * ('d * 'e list)) -> 'a * 'b list ->
    ('c * 'b list) * ('d * 'e list)
  val trace: ('a list -> 'b * 'c list) -> 'a list -> ('b * 'a list) * 'c list
  val try: ('a -> 'b) -> 'a -> 'b
  val force: ('a -> 'b) -> 'a -> 'b
  val prompt: string -> ('a -> 'b) -> 'a -> 'b
  val finite': 'a * ('a -> bool) -> ('b * 'a list -> 'c * ('d * 'a list))
    -> 'b * 'a list -> 'c * ('d * 'a list)
  val finite: 'a * ('a -> bool) -> ('a list -> 'b * 'a list) -> 'a list -> 'b * 'a list
  val read: 'a * ('a -> bool) -> ('a list -> 'b * 'a list) -> 'a list -> 'b option
  val catch: ('a -> 'b) -> 'a -> 'b
  val error: ('a -> 'b) -> 'a -> 'b
  val source': string -> (string -> 'a -> 'b list * 'a) -> ('b list * 'a -> 'c) ->
    'b * ('b -> bool) -> ('d * 'b list -> 'e list * ('d * 'b list)) ->
    ('d * 'b list -> 'e list * ('d * 'b list)) option -> 'd * 'a -> 'e list * ('d * 'c)
  val source: string -> (string -> 'a -> 'b list * 'a) -> ('b list * 'a -> 'c) ->
    'b * ('b -> bool) -> ('b list -> 'd list * 'b list) ->
    ('b list -> 'd list * 'b list) option -> 'a -> 'd list * 'c
  val single: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  val bulk: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  type lexicon
  val dest_lexicon: lexicon -> string list
  val make_lexicon: string list list -> lexicon
  val empty_lexicon: lexicon
  val extend_lexicon: lexicon -> string list list -> lexicon
  val merge_lexicons: lexicon -> lexicon -> lexicon
  val is_literal: lexicon -> string list -> bool
  val literal: lexicon -> string list -> string list * string list
end;

structure Scan: SCAN =
struct


(** scanners **)

exception MORE of string option;        (*need more input (prompt)*)
exception FAIL of string option;        (*try alternatives (reason of failure)*)
exception ABORT of string;              (*dead end*)


(* scanner combinators *)

fun (scan >> f) xs = scan xs |>> f;

fun (scan1 || scan2) xs = scan1 xs handle FAIL _ => scan2 xs;

fun (scan1 :-- scan2) xs =
  let
    val (x, ys) = scan1 xs;
    val (y, zs) = scan2 x ys;
  in ((x, y), zs) end;

fun (scan1 -- scan2) = scan1 :-- (fn _ => scan2);
fun (scan1 |-- scan2) = scan1 -- scan2 >> #2;
fun (scan1 --| scan2) = scan1 -- scan2 >> #1;
fun (scan1 ^^ scan2) = scan1 -- scan2 >> op ^;


(* generic scanners *)

fun fail _ = raise FAIL NONE;
fun fail_with msg_of xs = raise FAIL (SOME (msg_of xs));
fun succeed y xs = (y, xs);

fun some _ [] = raise MORE NONE
  | some f (x :: xs) =
      (case f x of SOME y => (y, xs) | _ => raise FAIL NONE);

fun one _ [] = raise MORE NONE
  | one pred (x :: xs) =
      if pred x then (x, xs) else raise FAIL NONE;

fun $$ a = one (fn s: string => s = a);
fun ~$$ a = one (fn s: string => s <> a);

fun this ys xs =
  let
    fun drop_prefix [] xs = xs
      | drop_prefix (_ :: _) [] = raise MORE NONE
      | drop_prefix (y :: ys) (x :: xs) =
          if (y: string) = x then drop_prefix ys xs else raise FAIL NONE;
  in (ys, drop_prefix ys xs) end;

fun this_string s = this (explode s) >> K s;  (*primitive string -- no symbols here!*)

fun any _ [] = raise MORE NONE
  | any pred (lst as x :: xs) =
      if pred x then apfst (cons x) (any pred xs)
      else ([], lst);

fun any1 pred = one pred -- any pred >> op ::;

fun optional scan def = scan || succeed def;
fun option scan = (scan >> SOME) || succeed NONE;

fun repeat scan =
  let
    fun rep ys xs =
      (case (SOME (scan xs) handle FAIL _ => NONE) of
        NONE => (rev ys, xs)
      | SOME (y, xs') => rep (y :: ys) xs');
  in rep [] end;

fun repeat1 scan = scan -- repeat scan >> op ::;

fun max leq scan1 scan2 xs =
  (case (option scan1 xs, option scan2 xs) of
    ((NONE, _), (NONE, _)) => raise FAIL NONE           (*looses FAIL msg!*)
  | ((SOME tok1, xs'), (NONE, _)) => (tok1, xs')
  | ((NONE, _), (SOME tok2, xs')) => (tok2, xs')
  | ((SOME tok1, xs1'), (SOME tok2, xs2')) =>
      if leq (tok2, tok1) then (tok1, xs1') else (tok2, xs2'));

fun ahead scan xs = (fst (scan xs), xs);

fun unless test scan =
  ahead (option test) :-- (fn NONE => scan | _ => fail) >> #2;

fun first [] = fail
  | first (scan :: scans) = scan || first scans;


(* state based scanners *)

fun state (st, xs) = (st, (st, xs));

fun depend scan (st, xs) =
  let val ((st', y), xs') = scan st xs
  in (y, (st', xs')) end;

fun peek scan = depend (fn st => scan st >> pair st);

fun pass st scan xs =
  let val (y, (_, xs')) = scan (st, xs)
  in (y, xs') end;

fun lift scan (st, xs) =
  let val (y, xs') = scan xs
  in (y, (st, xs')) end;

fun unlift scan = pass () scan;


(* trace input *)

fun trace' scan (st, xs) =
  let val (y, (st', xs')) = scan (st, xs)
  in ((y, Library.take (length xs - length xs', xs)), (st', xs')) end;

fun trace scan = unlift (trace' (lift scan));


(* exception handling *)

fun !! err scan xs = scan xs handle FAIL msg => raise ABORT (err (xs, msg));
fun try scan xs = scan xs handle MORE _ => raise FAIL NONE | ABORT _ => raise FAIL NONE;
fun force scan xs = scan xs handle MORE _ => raise FAIL NONE;
fun prompt str scan xs = scan xs handle MORE NONE => raise MORE (SOME str);
fun catch scan xs = scan xs handle ABORT msg => raise FAIL (SOME msg);
fun error scan xs = scan xs handle ABORT msg => Library.error msg;


(* finite scans *)

fun finite' (stopper, is_stopper) scan (state, input) =
  let
    fun lost () = raise ABORT "Scanner bug: lost stopper of finite scan!";

    fun stop [] = lost ()
      | stop lst =
          let val (xs, x) = split_last lst
          in if is_stopper x then ((), xs) else lost () end;
  in
    if exists is_stopper input then
      raise ABORT "Stopper may not occur in input of finite scan!"
    else (force scan --| lift stop) (state, input @ [stopper])
  end;

fun finite stopper scan = unlift (finite' stopper (lift scan));

fun read stopper scan xs =
  (case error (finite stopper (option scan)) xs of
    (y as SOME _, []) => y
  | _ => NONE);


(* infinite scans -- draining state-based source *)

fun drain def_prmpt get stopper scan ((state, xs), src) =
  (scan (state, xs), src) handle MORE prmpt =>
    (case get (the_default def_prmpt prmpt) src of
      ([], _) => (finite' stopper scan (state, xs), src)
    | (xs', src') => drain def_prmpt get stopper scan ((state, xs @ xs'), src'));

fun source' def_prmpt get unget stopper scanner opt_recover (state, src) =
  let
    val drain_with = drain def_prmpt get stopper;

    fun drain_loop recover inp =
      drain_with (catch scanner) inp handle FAIL msg =>
        (Output.error_msg (the_default "Syntax error." msg); drain_with recover inp);

    val ((ys, (state', xs')), src') =
      (case (get def_prmpt src, opt_recover) of
        (([], s), _) => (([], (state, [])), s)
      | ((xs, s), NONE) => drain_with (error scanner) ((state, xs), s)
      | ((xs, s), SOME r) => drain_loop (unless (lift (one (#2 stopper))) r) ((state, xs), s));
  in (ys, (state', unget (xs', src'))) end;

fun source def_prmpt get unget stopper scan opt_recover =
  unlift (source' def_prmpt get unget stopper (lift scan) (Option.map lift opt_recover));

fun single scan = scan >> (fn x => [x]);
fun bulk scan = scan -- repeat (try scan) >> (op ::);



(** datatype lexicon **)

datatype lexicon =
  Empty |
  Branch of string * string list * lexicon * lexicon * lexicon;

val no_literal = [];


(* dest_lexicon *)

fun dest_lex Empty = []
  | dest_lex (Branch (_, [], lt, eq, gt)) =
      dest_lex lt @ dest_lex eq @ dest_lex gt
  | dest_lex (Branch (_, cs, lt, eq, gt)) =
      dest_lex lt @ [cs] @ dest_lex eq @ dest_lex gt;

val dest_lexicon = map implode o dest_lex;


(* empty, extend, make, merge lexicons *)

val empty_lexicon = Empty;

fun extend_lexicon lexicon [] = lexicon
  | extend_lexicon lexicon chrss =
      let
        fun ext chrs lex =
          let
            fun add (chs as c :: cs) (Branch (d, a, lt, eq, gt)) =
                  (case fast_string_ord (c, d) of
                    LESS => Branch (d, a, add chs lt, eq, gt)
                  | EQUAL => Branch (d, if null cs then chrs else a, lt, add cs eq, gt)
                  | GREATER => Branch (d, a, lt, eq, add chs gt))
              | add [c] Empty = Branch (c, chrs, Empty, Empty, Empty)
              | add (c :: cs) Empty = Branch (c, no_literal, Empty, add cs Empty, Empty)
              | add [] lex = lex;
          in add chrs lex end;
      in lexicon |> fold ext (chrss |> subtract (op =) (dest_lex lexicon)) end;

val make_lexicon = extend_lexicon empty_lexicon;

fun merge_lexicons lex1 lex2 =
  let
    val chss1 = dest_lex lex1;
    val chss2 = dest_lex lex2;
  in
    if chss2 subset chss1 then lex1
    else if chss1 subset chss2 then lex2
    else extend_lexicon lex1 chss2
  end;


(* is_literal *)

fun is_literal Empty _ = false
  | is_literal _ [] = false
  | is_literal (Branch (d, a, lt, eq, gt)) (chs as c :: cs) =
      (case fast_string_ord (c, d) of
        LESS => is_literal lt chs
      | EQUAL => a <> no_literal andalso null cs orelse is_literal eq cs
      | GREATER => is_literal gt chs);


(* scan literal *)

fun literal lex chrs =
  let
    fun lit Empty res _ = res
      | lit (Branch _) _ [] = raise MORE NONE
      | lit (Branch (d, a, lt, eq, gt)) res (chs as c :: cs) =
          (case fast_string_ord (c, d) of
            LESS => lit lt res chs
          | EQUAL => lit eq (if a = no_literal then res else SOME (a, cs)) cs
          | GREATER => lit gt res chs);
  in
    (case lit lex NONE chrs of
      NONE => raise FAIL NONE
    | SOME res => res)
  end;

end;

structure BasicScan: BASIC_SCAN = Scan;
open BasicScan;
