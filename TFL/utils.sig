signature Utils_sig =
sig
  (* General error format and reporting mechanism *)
  exception ERR of {module:string,func:string, mesg:string}
  val Raise : exn -> 'a

  (* infix 3 ## *)
  val ## : ('a -> 'b) * ('c -> 'd) -> 'a * 'c -> 'b * 'd
  val can   : ('a -> 'b) -> 'a -> bool
  val holds : ('a -> bool) -> 'a -> bool
  val assert: ('a -> bool) -> 'a -> 'a
  val W : ('a -> 'a -> 'b) -> 'a -> 'b
  val C : ('a -> 'b -> 'c) -> 'b -> 'a -> 'c
  val I : 'a -> 'a
  val curry : ('a * 'b -> 'c) -> 'a -> 'b -> 'c
  val uncurry : ('a -> 'b -> 'c) -> 'a * 'b -> 'c
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b

  (* option type *)
  datatype 'a option = SOME of 'a | NONE

  (* Set operations *)
  val mem : ('a -> 'a -> bool) -> 'a -> 'a list -> bool
  val union : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val Union : ('a -> 'a -> bool) -> 'a list list ->  'a list
  val intersect : ('a -> 'a -> bool) -> 'a list -> 'a list -> 'a list
  val set_diff : ('a -> 'b -> bool) -> 'a list -> 'b list -> 'a list
  val mk_set : ('a -> 'a -> bool) -> 'a list -> 'a list
  val set_eq : ('a -> 'a -> bool) -> 'a list -> 'a list -> bool

  val map2 : ('a -> 'b -> 'c) -> 'a list -> 'b list -> 'c list
  val itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val rev_itlist : ('a -> 'b -> 'b) -> 'a list -> 'b -> 'b
  val end_itlist : ('a -> 'a -> 'a) -> 'a list -> 'a
  val itlist2 :('a -> 'b -> 'c -> 'c) -> 'a list -> 'b list -> 'c -> 'c
  val filter : ('a -> bool) -> 'a list -> 'a list
  val mapfilter : ('a -> 'b) -> 'a list -> 'b list
  val pluck : ('a -> bool) -> 'a list -> 'a * 'a list
  val assoc1 : ('a*'a->bool) -> 'a -> ('a * 'b) list -> ('a * 'b) option
  val front_back : 'a list -> 'a list * 'a
  val all : ('a -> bool) -> 'a list -> bool
  val exists : ('a -> bool) -> 'a list -> bool
  val zip : 'a list -> 'b list -> ('a*'b) list
  val zip3 : 'a list -> 'b list -> 'c list -> ('a*'b*'c) list
  val unzip : ('a*'b) list -> ('a list * 'b list)
  val take  : ('a -> 'b) -> int * 'a list -> 'b list
  val sort  : ('a -> 'a -> bool) -> 'a list -> 'a list

  val int_to_string : int -> string
  val concat : string -> string -> string
  val quote : string -> string

end;

