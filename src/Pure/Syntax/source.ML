(*  Title:      Isar/source.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Co-algebraic data sources.

TODO:
  - proper handling of interrupts (?);
  - recovery from scan errors (?);
  - make prompt part of source (?);
*)

signature SOURCE =
sig
  type ('a, 'b) source
  val get: string -> ('a, 'b) source -> 'a list * ('a, 'b) source
  val unget: 'a list * ('a, 'b) source -> ('a, 'b) source
  val get_single: string -> ('a, 'b) source -> 'a * ('a, 'b) source
  val exhaust: string -> ('a, 'b) source -> 'a list
  val filter: ('a -> bool) -> ('a, 'b) source -> ('a, ('a, 'b) source) source
  val of_list: int option -> 'a list -> ('a, 'a list) source
  val of_string: int option -> string -> (string, string list) source
  val of_stream: TextIO.instream -> TextIO.outstream -> (string, unit) source
  val tty: (string, unit) source
  val state_source: 'a -> 'b * ('b -> bool) -> ('a * 'b list -> 'c list * ('a * 'b list))
    -> ('b, 'd) source -> ('c, 'a * ('b, 'd) source) source
  val source: 'a * ('a -> bool) -> ('a list -> 'b list * 'a list)
    -> ('a, 'c) source -> ('b, ('a, 'c) source) source
  val test: ('a -> string) -> ('a, 'b) source -> unit
end;

structure Source: SOURCE =
struct


(** datatype source **)

datatype ('a, 'b) source =
  Source of
   {buffer: 'a list,
    info: 'b,
    drain: string -> 'b -> 'a list * 'b};

fun make_source buffer info drain =
  Source {buffer = buffer, info = info, drain = drain};


(* get / unget *)

fun get prompt (Source {buffer = [], info, drain}) =
      let val (xs, info') = drain prompt info
      in (xs, make_source [] info' drain) end
  | get _ (Source {buffer, info, drain}) =
      (buffer, make_source [] info drain);

fun unget (xs, Source {buffer, info, drain}) =
  make_source (xs @ buffer) info drain;


fun get_single prompt src =
  (case get prompt src of
    ([], _) => error "Input source exhausted!"
  | (x :: xs, src') => (x, unget (xs, src')));

fun exhaust prompt src =
  (case get prompt src of
    ([], _) => []
  | (xs, src') => xs @ exhaust prompt src');


(* filter *)

fun drain_filter pred prompt src =
  let
    val (xs, src') = get prompt src;
    val xs' = Library.filter pred xs;
  in
    if null xs then (xs, src')
    else if null xs' then drain_filter pred prompt src'
    else (xs', src')
  end;

fun filter pred src = make_source [] src (drain_filter pred);



(** build sources **)

(* list source *)

fun drain_list _ xs = (xs, []);
fun drain_list_limit n _ xs = (take (n, xs), drop (n, xs));

fun of_list None xs = make_source [] xs drain_list
  | of_list (Some n) xs = make_source [] xs (drain_list_limit (Int.max (n, 1)));

fun of_string limit str = of_list limit (explode str);


(* stream source *)

fun drain_stream instream outstream prompt () =
  (TextIO.output (outstream, prompt);
    TextIO.flushOut outstream;
    (explode (TextIO.inputLine instream), ()));

fun of_stream instream outstream =
  make_source [] () (drain_stream instream outstream);

val tty = of_stream TextIO.stdIn TextIO.stdOut;



(** compose sources **)

(* make state-based *)

fun drain_state_source stopper scan prompt state_src =
  Scan.source prompt get unget stopper scan state_src;

fun state_source init_state stopper scan src =
  make_source [] (init_state, src) (drain_state_source stopper scan);


(* not state-based *)

fun drain_source stopper scan prompt src =
  apsnd snd (Scan.source prompt get unget stopper (Scan.lift scan) ((), src));

fun source stopper scan src =
   make_source [] src (drain_source stopper scan);



(** test source interactively **)

fun test str_of src =
  (case get ">> " src handle Interrupt => ([], src) of
    ([], _) => writeln "Terminated."
  | (xs, src') => (seq writeln (map str_of xs); test str_of src'));


end;
