(*  Title:      Pure/General/scan.ML
    ID:         $Id$
    Author:     Markus Wenzel and Tobias Nipkow, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

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
  val $$ : ''a -> ''a list -> ''a * ''a list
  (*literal list*)
  val list: ''a list -> ''a list -> ''a list * ''a list
end;

signature SCAN =
sig
  include BASIC_SCAN
  val fail: 'a -> 'b
  val fail_with: ('a -> string) -> 'a -> 'b
  val succeed: 'a -> 'b -> 'a * 'b
  val one: ('a -> bool) -> 'a list -> 'a * 'a list
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
  val lift: ('a -> 'b * 'c) -> 'd * 'a -> 'b * ('d * 'c)
  val pass: 'a -> ('a * 'b -> 'c * ('d * 'e)) -> 'b -> 'c * 'e
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

(*dependent pairing*)
fun (sc1 :-- sc2) toks =
  let
    val (x, toks2) = sc1 toks
    val (y, toks3) = sc2 x toks2
  in ((x, y), toks3) end;

(*sequential pairing*)
fun (sc1 -- sc2) toks =
  let
    val (x, toks2) = sc1 toks
    val (y, toks3) = sc2 toks2
  in ((x, y), toks3) end;

(*application*)
fun (sc >> f) toks =
  let val (x, toks2) = sc toks
  in (f x, toks2) end;

(*forget snd*)
fun (sc1 --| sc2) toks =
  let
    val (x, toks2) = sc1 toks
    val (_, toks3) = sc2 toks2
  in (x, toks3) end;

(*forget fst*)
fun (sc1 |-- sc2) toks =
  let val (_, toks2) = sc1 toks
  in sc2 toks2 end;

(*concatenation*)
fun (sc1 ^^ sc2) toks =
  let
    val (x, toks2) = sc1 toks
    val (y, toks3) = sc2 toks2
  in (x ^ y, toks3) end;

(*alternative*)
fun (scan1 || scan2) xs = scan1 xs handle FAIL _ => scan2 xs;


(* generic scanners *)

fun fail _ = raise FAIL None;
fun fail_with msg_of xs = raise FAIL (Some (msg_of xs));
fun succeed y xs = (y, xs);

fun one _ [] = raise MORE None
  | one pred (x :: xs) =
      if pred x then (x, xs) else raise FAIL None;

fun $$ _ [] = raise MORE None
  | $$ a (x :: xs) =
      if a = x then (x, xs) else raise FAIL None;

fun list ys xs =
  let
    fun drop_prefix [] xs = xs
      | drop_prefix (_ :: _) [] = raise MORE None
      | drop_prefix (y :: ys) (x :: xs) =
          if y = x then drop_prefix ys xs else raise FAIL None;
  in (ys, drop_prefix ys xs) end;

fun any _ [] = raise MORE None
  | any pred (lst as x :: xs) =
      if pred x then apfst (cons x) (any pred xs)
      else ([], lst);

fun any1 p toks =
  let
    val (x, toks2) = one p toks
    val (xs,toks3) = any p toks2
  in (x :: xs, toks3) end;

fun optional scan def =  scan || succeed def
fun option scan = (scan >> Some) || succeed None

fun repeat scan =
  let fun rep ys xs = (case (Some (scan xs) handle FAIL _ => None) of
    None => (rev ys, xs) | Some (y, xs') => rep (y :: ys) xs')
  in rep [] end;

fun repeat1 scan toks =
  let
    val (x, toks2) = scan toks
    val (xs, toks3) = repeat scan toks2
  in (x :: xs, toks3) end;

fun max leq scan1 scan2 xs =
  (case (option scan1 xs, option scan2 xs) of
    ((None, _), (None, _)) => raise FAIL None           (*looses FAIL msg!*)
  | ((Some tok1, xs'), (None, _)) => (tok1, xs')
  | ((None, _), (Some tok2, xs')) => (tok2, xs')
  | ((Some tok1, xs1'), (Some tok2, xs2')) =>
      if leq (tok2, tok1) then (tok1, xs1') else (tok2, xs2'));

fun ahead scan xs = (fst (scan xs), xs);

fun unless test scan =
  ahead (option test) :-- (fn None => scan | _ => fail) >> #2;

fun first [] = fail
  | first (scan :: scans) = scan || first scans;


(* state based scanners *)

fun state (st, xs) = (st, (st, xs));

fun depend scan (st, xs) =
  let val ((st', y), xs') = scan st xs
  in (y, (st', xs')) end;

fun lift scan (st, xs) =
  let val (y, xs') = scan xs
  in (y, (st, xs')) end;

fun pass st scan xs =
  let val (y, (_, xs')) = scan (st, xs)
  in (y, xs') end;


(* exception handling *)

fun !! err scan xs = scan xs handle FAIL msg => raise ABORT (err (xs, msg));
fun try scan xs = scan xs handle MORE _ => raise FAIL None | ABORT _ => raise FAIL None;
fun force scan xs = scan xs handle MORE _ => raise FAIL None;
fun prompt str scan xs = scan xs handle MORE None => raise MORE (Some str);
fun catch scan xs = scan xs handle ABORT msg => raise FAIL (Some msg);
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
    else (force scan --| lift stop) (state, rev_append (rev input) [stopper])
  end;

fun finite stopper scan xs =
  let val (y, ((), xs')) = finite' stopper (lift scan) ((), xs)
  in (y, xs') end;

fun read stopper scan xs =
  (case error (finite stopper (option scan)) xs of
    (y as Some _, []) => y
  | _ => None);


(* infinite scans -- draining state-based source *)

fun drain def_prmpt get stopper scan ((state, xs), src) =
  (scan (state, xs), src) handle MORE prmpt =>
    (case get (if_none prmpt def_prmpt) src of
      ([], _) => (finite' stopper scan (state, xs), src)
    | (xs', src') => drain def_prmpt get stopper scan ((state, xs @ xs'), src'));

fun source' def_prmpt get unget stopper scanner opt_recover (state, src) =
  let
    val drain_with = drain def_prmpt get stopper;

    fun drain_loop recover inp =
      drain_with (catch scanner) inp handle FAIL msg =>
        (error_msg (if_none msg "Syntax error."); drain_with recover inp);

    val ((ys, (state', xs')), src') =
      (case (get def_prmpt src, opt_recover) of
        (([], s), _) => (([], (state, [])), s)
      | ((xs, s), None) => drain_with (error scanner) ((state, xs), s)
      | ((xs, s), Some r) => drain_loop (unless (lift (one (#2 stopper))) r) ((state, xs), s));
  in (ys, (state', unget (xs', src'))) end;

fun source def_prmpt get unget stopper scan opt_recover src =
  let val (ys, ((), src')) =
    source' def_prmpt get unget stopper (lift scan) (apsome lift opt_recover) ((), src)
  in (ys, src') end;

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
        fun ext (lex, chrs) =
          let
            fun add (Branch (d, a, lt, eq, gt)) (chs as c :: cs) =
                  (case String.compare (c, d) of
                    LESS => Branch (d, a, add lt chs, eq, gt)
                  | EQUAL => Branch (d, if null cs then chrs else a, lt, add eq cs, gt)
                  | GREATER => Branch (d, a, lt, eq, add gt chs))
              | add Empty [c] =
                  Branch (c, chrs, Empty, Empty, Empty)
              | add Empty (c :: cs) =
                  Branch (c, no_literal, Empty, add Empty cs, Empty)
              | add lex [] = lex;
          in add lex chrs end;
      in foldl ext (lexicon, chrss \\ dest_lex lexicon) end;

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
      (case String.compare (c, d) of
        LESS => is_literal lt chs
      | EQUAL => a <> no_literal andalso null cs orelse is_literal eq cs
      | GREATER => is_literal gt chs);


(* scan literal *)

fun literal lex chrs =
  let
    fun lit Empty res _ = res
      | lit (Branch _) _ [] = raise MORE None
      | lit (Branch (d, a, lt, eq, gt)) res (chs as c :: cs) =
          (case String.compare (c, d) of
            LESS => lit lt res chs
          | EQUAL => lit eq (if a = no_literal then res else Some (a, cs)) cs
          | GREATER => lit gt res chs);
  in
    (case lit lex None chrs of
      None => raise FAIL None
    | Some res => res)
  end;


end;


structure BasicScan: BASIC_SCAN = Scan;
open BasicScan;
