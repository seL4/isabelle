(*  Title:      Pure/General/source.ML
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
  val get_single: ('a, 'b) source -> ('a * ('a, 'b) source) option
  val exhaust: ('a, 'b) source -> 'a list
  val mapfilter: ('a -> 'b option) -> ('a, 'c) source -> ('b, ('a, 'c) source) source
  val filter: ('a -> bool) -> ('a, 'b) source -> ('a, ('a, 'b) source) source
  val of_list: 'a list -> ('a, 'a list) source
  val of_string: string -> (string, string list) source
  val decorate_prompt_fn: (string -> string) ref
  val of_stream: TextIO.instream -> TextIO.outstream -> (string, unit) source
  val tty: (string, unit) source
  val source': 'a -> 'b * ('b -> bool) -> ('a * 'b list -> 'c list * ('a * 'b list)) ->
    ('a * 'b list -> 'd * ('a * 'b list)) option ->
    ('b, 'e) source -> ('c, 'a * ('b, 'e) source) source
  val source: 'a * ('a -> bool) -> ('a list -> 'b list * 'a list) ->
    ('a list -> 'c * 'a list) option ->
    ('a, 'd) source -> ('b, ('a, 'd) source) source
end;

structure Source: SOURCE =
struct


(** datatype source **)

datatype ('a, 'b) source =
  Source of
   {buffer: 'a list,
    info: 'b,
    prompt: string,
    drain: string -> 'b -> 'a list * 'b};

fun make_source buffer info prompt drain =
  Source {buffer = buffer, info = info, prompt = prompt, drain = drain};


(* prompt *)

val default_prompt = "> ";

fun set_prompt prompt (Source {buffer, info, prompt = _, drain}) =
  make_source buffer info prompt drain;


(* get / unget *)

fun get (Source {buffer = [], info, prompt, drain}) =
      let val (xs, info') = drain prompt info
      in (xs, make_source [] info' prompt drain) end
  | get (Source {buffer, info, prompt, drain}) =
      (buffer, make_source [] info prompt drain);

fun unget (xs, Source {buffer, info, prompt, drain}) =
  make_source (xs @ buffer) info prompt drain;


(* variations on get *)

fun get_prompt prompt src = get (set_prompt prompt src);

fun get_single src =
  (case get src of
    ([], _) => None
  | (x :: xs, src') => Some (x, unget (xs, src')));

fun exhaust src =
  (case get src of
    ([], _) => []
  | (xs, src') => xs @ exhaust src');


(* (map)filter *)

fun drain_mapfilter f prompt src =
  let
    val (xs, src') = get_prompt prompt src;
    val xs' = Library.mapfilter f xs;
  in
    if null xs orelse not (null xs') then (xs', src')
    else drain_mapfilter f prompt src'
  end;

fun mapfilter f src = make_source [] src default_prompt (drain_mapfilter f);
fun filter pred = mapfilter (fn x => if pred x then Some x else None);



(** build sources **)

(* list source *)

(*limiting the input buffer considerably improves performance*)
val limit = 4000;

fun drain_list _ xs = (take (limit, xs), drop (limit, xs));

fun of_list xs = make_source [] xs default_prompt drain_list;
val of_string = of_list o explode;


(* stream source *)

val decorate_prompt_fn = ref (fn s:string => s);

fun drain_stream instream outstream prompt () =
  (TextIO.output (outstream, ! decorate_prompt_fn prompt);
    TextIO.flushOut outstream;
    (explode (TextIO.inputLine instream), ()));

fun of_stream instream outstream =
  make_source [] () default_prompt (drain_stream instream outstream);

val tty = of_stream TextIO.stdIn TextIO.stdOut;



(** compose sources **)

fun drain_source source stopper scan recover prompt src =
  source prompt get_prompt unget stopper scan recover src;


(* state-based *)

fun source' init_state stopper scan recover src =
  make_source [] (init_state, src) default_prompt
    (drain_source Scan.source' stopper scan recover);


(* non state-based *)

fun source stopper scan recover src =
  make_source [] src default_prompt
    (drain_source Scan.source stopper scan recover);


end;
