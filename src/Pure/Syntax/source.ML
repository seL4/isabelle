(*  Title:      Isar/source.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Co-algebraic data sources.
*)

signature SOURCE =
sig
  type ('a, 'b) source
  val set_prompt: string -> ('a, 'b) source -> ('a, 'b) source
  val get: ('a, 'b) source -> 'a list * ('a, 'b) source
  val unget: 'a list * ('a, 'b) source -> ('a, 'b) source
  val get_single: ('a, 'b) source -> 'a * ('a, 'b) source
  val exhaust: ('a, 'b) source -> 'a list
  val filter: ('a -> bool) -> ('a, 'b) source -> ('a, ('a, 'b) source) source
  val of_list: 'a list -> ('a, 'a list) source
  val of_string: string -> (string, string list) source
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
    prompt: string option,
    drain: string -> 'b -> 'a list * 'b};

fun make_source buffer info prompt drain =
  Source {buffer = buffer, info = info, prompt = prompt, drain = drain};


(* prompt *)

val default_prompt = "> ";

fun set_prompt prompt (Source {buffer, info, prompt = _, drain}) =
  make_source buffer info (Some prompt) drain;


(* get / unget *)

fun get (Source {buffer = [], info, prompt, drain}) =
      let val (xs, info') = drain (if_none prompt default_prompt) info
      in (xs, make_source [] info' prompt drain) end
  | get (Source {buffer, info, prompt, drain}) =
      (buffer, make_source [] info prompt drain);

fun unget (xs, Source {buffer, info, prompt, drain}) =
  make_source (xs @ buffer) info prompt drain;


(* variations on get *)

fun get_prompt prompt src = get (set_prompt prompt src);

fun get_single src =
  (case get src of
    ([], _) => error "Input source exhausted!"
  | (x :: xs, src') => (x, unget (xs, src')));

fun exhaust src =
  (case get src of
    ([], _) => []
  | (xs, src') => xs @ exhaust src');


(* filter *)

fun drain_filter pred prompt src =
  let
    val (xs, src') = get src;
    val xs' = Library.filter pred xs;
  in
    if null xs then (xs, src')
    else if null xs' then drain_filter pred prompt src'
    else (xs', src')
  end;

fun filter pred src = make_source [] src None (drain_filter pred);



(** build sources **)

(* list source *)

(*limiting the master input buffer considerably improves performance*)
val limit = 4000;

fun drain_list _ xs = (take (limit, xs), drop (limit, xs));

fun of_list xs = make_source [] xs None drain_list;
fun of_string str = of_list (explode str);


(* stream source *)

fun drain_stream instream outstream prompt () =
  (TextIO.output (outstream, prompt);
    TextIO.flushOut outstream;
    (explode (TextIO.inputLine instream), ()));

fun of_stream instream outstream =
  make_source [] () None (drain_stream instream outstream);

val tty = of_stream TextIO.stdIn TextIO.stdOut;



(** compose sources **)

(* make state-based *)

fun drain_state_source stopper scan prompt state_src =
  Scan.source prompt get_prompt unget stopper scan state_src;

fun state_source init_state stopper scan src =
  make_source [] (init_state, src) None (drain_state_source stopper scan);


(* not state-based *)

fun drain_source stopper scan prompt src =
  apsnd snd (Scan.source prompt get_prompt unget stopper (Scan.lift scan) ((), src));

fun source stopper scan src =
   make_source [] src None (drain_source stopper scan);



(** test source interactively **)

fun test str_of src =
  (case get src handle Interrupt => ([], src) of
    ([], _) => writeln "Terminated."
  | (xs, src') => (seq writeln (map str_of xs); test str_of src'));


end;
