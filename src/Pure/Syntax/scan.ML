(*  Title:	Pure/Syntax/scan.ML
    ID:		$Id$
    Author:	Markus Wenzel and Tobias Nipkow, TU Muenchen

Generic scanners (for potentially infinite input).
*)

infix 5 -- |-- --| ^^;
infix 3 >>;
infix 0 ||;

signature BASIC_SCAN =
sig
  val !! : ('a -> string) -> ('a -> 'b) -> 'a -> 'b
  val >> : ('a -> 'b * 'c) * ('b -> 'd) -> 'a -> 'd * 'c
  val || : ('a -> 'b) * ('a -> 'b) -> 'a -> 'b
  val -- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> ('b * 'd) * 'e
  val |-- : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'd * 'e
  val --| : ('a -> 'b * 'c) * ('c -> 'd * 'e) -> 'a -> 'b * 'e
  val ^^ : ('a -> string * 'b) * ('b -> string * 'c) -> 'a -> string * 'c
  val $$ : ''a -> ''a list -> ''a * ''a list
end;

signature SCAN =
sig
  include BASIC_SCAN
  val fail: 'a -> 'b
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
  val depend: ('a -> 'b -> ('c * 'd) * 'e) -> 'a * 'b -> 'd * ('c * 'e)
  val lift: ('a -> 'b * 'c) -> 'd * 'a -> 'b * ('d * 'c)
  val pass: 'a -> ('a * 'b -> 'c * ('d * 'e)) -> 'b -> 'c * 'e
  val try: ('a -> 'b) -> 'a -> 'b
  val force: ('a -> 'b) -> 'a -> 'b
  val prompt: string -> ('a -> 'b) -> 'a -> 'b
  val finite': ''a -> ('b * ''a list -> 'c * ('d * ''a list))
    -> 'b * ''a list -> 'c * ('d * ''a list)
  val finite: ''a -> (''a list -> 'b * ''a list) -> ''a list -> 'b * ''a list
  val error: ('a -> 'b) -> 'a -> 'b
  val source: string -> (string -> 'a -> 'b list * 'a)
    -> ('c * 'a -> 'd) -> ('b list -> 'e * 'c) -> 'a -> 'e * 'd
  val single: ('a -> 'b * 'c) -> 'a -> 'b list * 'c
  val many: ('a -> 'b * 'a) -> 'a -> 'b list * 'a
  type lexicon
  val dest_lexicon: lexicon -> string list list
  val make_lexicon: string list list -> lexicon
  val empty_lexicon: lexicon
  val extend_lexicon: lexicon -> string list list -> lexicon
  val merge_lexicons: lexicon -> lexicon -> lexicon
  val literal: lexicon -> string list -> string list * string list
end;

structure Scan: SCAN =
struct


(** scanners **)

exception MORE of string option;	(*need more input (use prompt)*)
exception FAIL;				(*try alternatives*)
exception ABORT of string;		(*dead end*)


(* scanner combinators *)

fun (scan >> f) xs = apfst f (scan xs);

fun (scan1 || scan2) xs = scan1 xs handle FAIL => scan2 xs;

fun (scan1 -- scan2) xs =
  let
    val (x, ys) = scan1 xs;
    val (y, zs) = scan2 ys;
  in ((x, y), zs) end;

fun (scan1 |-- scan2) = scan1 -- scan2 >> #2;
fun (scan1 --| scan2) = scan1 -- scan2 >> #1;

fun (scan1 ^^ scan2) = scan1 -- scan2 >> op ^;


(* generic scanners *)

fun fail _ = raise FAIL;
fun succeed y xs = (y, xs);

fun one _ [] = raise MORE None
  | one pred (x :: xs) =
      if pred x then (x, xs) else raise FAIL;

fun $$ _ [] = raise MORE None
  | $$ a (x :: xs) =
      if a = x then (x, xs) else raise FAIL;

fun any _ [] = raise MORE None
  | any pred (lst as x :: xs) =
      if pred x then apfst (cons x) (any pred xs)
      else ([], lst);

fun any1 pred = one pred -- any pred >> op ::;

fun optional scan def = scan || succeed def;
fun option scan = optional (scan >> Some) None;

fun repeat scan xs = (scan -- repeat scan >> op :: || succeed []) xs;
fun repeat1 scan = scan -- repeat scan >> op ::;

fun max leq scan1 scan2 xs =
  (case (option scan1 xs, option scan2 xs) of
    ((None, _), (None, _)) => raise FAIL
  | ((Some tok1, xs'), (None, _)) => (tok1, xs')
  | ((None, _), (Some tok2, xs')) => (tok2, xs')
  | ((Some tok1, xs1'), (Some tok2, xs2')) =>
      if leq (tok2, tok1) then (tok1, xs1') else (tok2, xs2'));

fun ahead scan xs = (fst (scan xs), xs);


(* state based scanners *)

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

fun !! err scan xs = scan xs handle FAIL => raise ABORT (err xs);
fun try scan xs = scan xs handle MORE _ => raise FAIL | ABORT _ => raise FAIL;
fun force scan xs = scan xs handle MORE _ => raise FAIL;
fun prompt str scan xs = scan xs handle MORE None => raise MORE (Some str);
fun error scan xs = scan xs handle ABORT msg => Library.error msg;


(* finite scans *)

fun finite' stopper scan (state, input) =
  let
    fun lost () = raise ABORT "Scanner bug: lost stopper of finite scan!";

    fun stop [] = lost ()
      | stop lst =
          let val (xs, x) = split_last lst
          in if x = stopper then ((), xs) else lost () end;
  in
    if exists (equal stopper) input then
      raise ABORT "Stopper may not occur in input of finite scan!"
    else (force scan --| lift stop) (state, input @ [stopper])
  end;

fun finite stopper scan xs =
  let val (y, ((), xs')) = finite' stopper (lift scan) ((), xs)
  in (y, xs') end;


(* infinite scans *)

fun source def_prmpt get unget scan src =
  let
    fun drain (xs, s) =
      (scan xs, s)
        handle MORE prmpt =>
          let val (more_xs, s') = get (if_none prmpt def_prmpt) s in
            if null more_xs then raise ABORT "Input source exhausted"
            else drain (xs @ more_xs, s')
          end;
    val ((ys, xs'), src') = drain (get def_prmpt src);
  in (ys, unget (xs', src')) end;

fun single scan = scan >> (fn x => [x]);
fun many scan = scan -- repeat (try scan) >> (op ::);



(** datatype lexicon **)

datatype lexicon =
  Empty |
  Branch of string * string list * lexicon * lexicon * lexicon;

val no_literal = [];


(* dest_lexicon *)

fun dest_lexicon Empty = []
  | dest_lexicon (Branch (_, [], lt, eq, gt)) =
      dest_lexicon lt @ dest_lexicon eq @ dest_lexicon gt
  | dest_lexicon (Branch (_, cs, lt, eq, gt)) =
      dest_lexicon lt @ [cs] @ dest_lexicon eq @ dest_lexicon gt;


(* empty, extend, make, merge lexicons *)

val empty_lexicon = Empty;

fun extend_lexicon lexicon chrss =
  let
    fun ext (lex, chrs) =
      let
	fun add (Branch (d, a, lt, eq, gt)) (chs as c :: cs) =
	      if c < d then Branch (d, a, add lt chs, eq, gt)
	      else if c > d then Branch (d, a, lt, eq, add gt chs)
	      else Branch (d, if null cs then chrs else a, lt, add eq cs, gt)
	  | add Empty [c] =
	      Branch (c, chrs, Empty, Empty, Empty)
	  | add Empty (c :: cs) =
	      Branch (c, no_literal, Empty, add Empty cs, Empty)
	  | add lex [] = lex;
      in add lex chrs end;
  in foldl ext (lexicon, chrss \\ dest_lexicon lexicon) end;

val make_lexicon = extend_lexicon empty_lexicon;

fun merge_lexicons lex1 lex2 =
  let
    val chss1 = dest_lexicon lex1;
    val chss2 = dest_lexicon lex2;
  in
    if chss2 subset chss1 then lex1
    else if chss1 subset chss2 then lex2
    else extend_lexicon lex1 chss2
  end;


(* scan literal *)

fun literal lex chrs =
  let
    fun lit Empty res _ = res
      | lit (Branch _) _ [] = raise MORE None
      | lit (Branch (d, a, lt, eq, gt)) res (chs as c :: cs) =
	  if c < d then lit lt res chs
	  else if c > d then lit gt res chs
	  else lit eq (if a = no_literal then res else Some (a, cs)) cs;
  in
    (case lit lex None chrs of
      None => raise FAIL
    | Some res => res)
  end;


end;


structure BasicScan: BASIC_SCAN = Scan;
open BasicScan;
