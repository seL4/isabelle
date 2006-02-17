(*  Title:      HOL/Import/lazy_seq.ML
    ID:         $Id$
    Author:     Sebastian Skalberg, TU Muenchen

Alternative version of lazy sequences.
*)

signature LAZY_SEQ =
sig

    include EXTENDED_SCANNER_SEQ

    (* From LIST *)

    val fromString : string -> string seq
    val @ : 'a seq * 'a seq -> 'a seq
    val hd : 'a seq -> 'a
    val tl : 'a seq -> 'a seq
    val last : 'a seq -> 'a
    val getItem : 'a seq -> ('a * 'a seq) option
    val nth : 'a seq * int -> 'a
    val take : 'a seq * int -> 'a seq
    val drop : 'a seq * int -> 'a seq
    val rev : 'a seq -> 'a seq
    val concat : 'a seq seq -> 'a seq
    val revAppend : 'a seq * 'a seq -> 'a seq
    val app : ('a -> unit) -> 'a seq -> unit
    val map : ('a -> 'b) -> 'a seq -> 'b seq
    val mapPartial : ('a -> 'b option) -> 'a seq -> 'b seq
    val find : ('a -> bool) -> 'a seq -> 'a option
    val filter : ('a -> bool) -> 'a seq -> 'a seq
    val partition : ('a -> bool)
                      -> 'a seq -> 'a seq * 'a seq
    val foldl : ('a * 'b -> 'b) -> 'b -> 'a seq -> 'b
    val foldr : ('a * 'b -> 'b) -> 'b -> 'a seq -> 'b
    val exists : ('a -> bool) -> 'a seq -> bool
    val all : ('a -> bool) -> 'a seq -> bool
    val tabulate : int * (int -> 'a) -> 'a seq
    val collate : ('a * 'a -> order)
                    -> 'a seq * 'a seq -> order 

    (* Miscellaneous *)

    val cycle      : ((unit ->'a seq) -> 'a seq) -> 'a seq
    val iterates   : ('a -> 'a) -> 'a -> 'a seq
    val of_function: (unit -> 'a option) -> 'a seq
    val of_string  : string -> char seq
    val of_instream: TextIO.instream -> char seq

    (* From SEQ *)

    val make: (unit -> ('a * 'a seq) option) -> 'a seq
    val empty: 'a -> 'a seq
    val cons: 'a * 'a seq -> 'a seq
    val single: 'a -> 'a seq
    val try: ('a -> 'b) -> 'a -> 'b seq
    val chop: int * 'a seq -> 'a list * 'a seq
    val list_of: 'a seq -> 'a list
    val of_list: 'a list -> 'a seq
    val mapp: ('a -> 'b) -> 'a seq -> 'b seq -> 'b seq
    val interleave: 'a seq * 'a seq -> 'a seq
    val print: (int -> 'a -> unit) -> int -> 'a seq -> unit
    val it_right : ('a * 'b seq -> 'b seq) -> 'a seq * 'b seq -> 'b seq
    val commute: 'a seq list -> 'a list seq
    val succeed: 'a -> 'a seq
    val fail: 'a -> 'b seq
    val THEN: ('a -> 'b seq) * ('b -> 'c seq) -> 'a -> 'c seq
    val ORELSE: ('a -> 'b seq) * ('a -> 'b seq) -> 'a -> 'b seq
    val APPEND: ('a -> 'b seq) * ('a -> 'b seq) -> 'a -> 'b seq
    val EVERY: ('a -> 'a seq) list -> 'a -> 'a seq
    val FIRST: ('a -> 'b seq) list -> 'a -> 'b seq
    val TRY: ('a -> 'a seq) -> 'a -> 'a seq
    val REPEAT: ('a -> 'a seq) -> 'a -> 'a seq
    val REPEAT1: ('a -> 'a seq) -> 'a -> 'a seq
    val INTERVAL: (int -> 'a -> 'a seq) -> int -> int -> 'a -> 'a seq
    val DETERM: ('a -> 'b seq) -> 'a -> 'b seq

end

structure LazySeq :> LAZY_SEQ =
struct

open Susp

datatype 'a seq = Seq of ('a * 'a seq) option susp

exception Empty

fun getItem (Seq s) = force s
val pull = getItem
fun make f = Seq (delay f)

fun null s = is_none (getItem s)

local
    fun F n NONE = n
      | F n (SOME(_,s)) = F (n+1) (getItem s)
in
fun length s = F 0 (getItem s)
end

fun s1 @ s2 =
    let
	fun F NONE = getItem s2
	  | F (SOME(x,s1')) = SOME(x,F' s1')
	and F' s = make (fn () => F (getItem s))
    in
	F' s1
    end

local
    fun F NONE = raise Empty
      | F (SOME arg) = arg
in
fun hd s = #1 (F (getItem s))
fun tl s = #2 (F (getItem s))
end

local
    fun F x NONE = x
      | F _ (SOME(x,s)) = F x (getItem s)
    fun G NONE = raise Empty
      | G (SOME(x,s)) = F x (getItem s)
in
fun last s = G (getItem s)
end

local
    fun F NONE _ = raise Subscript
      | F (SOME(x,_)) 0 = x
      | F (SOME(_,s)) n = F (getItem s) (n-1)
in
fun nth(s,n) =
    if n < 0
    then raise Subscript
    else F (getItem s) n
end

local
    fun F NONE _ = raise Subscript
      | F (SOME(x,s)) n = SOME(x,F' s (n-1))
    and F' s 0 = Seq (value NONE)
      | F' s n = make (fn () => F (getItem s) n)
in
fun take (s,n) =
    if n < 0
    then raise Subscript
    else F' s n
end

fun take_at_most s n = 
    if n <= 0 then [] else
    case getItem s of 
	NONE => []
      | SOME (x,s') => x::(take_at_most s' (n-1))

local
    fun F s 0 = s
      | F NONE _ = raise Subscript
      | F (SOME(_,s)) n = F (getItem s) (n-1)
in
fun drop (s,0) = s
  | drop (s,n) = 
    if n < 0
    then raise Subscript
    else make (fn () => F (getItem s) n)
end

local
    fun F s NONE = s
      | F s (SOME(x,s')) = F (SOME(x, Seq (value s))) (getItem s')
in
fun rev s = make (fn () => F NONE (getItem s))
end

local
    fun F s NONE = getItem s
      | F s (SOME(x,s')) = F (Seq (value (SOME(x,s)))) (getItem s')
in
fun revAppend (s1,s2) = make (fn () => F s2 (getItem s1))
end

local
    fun F NONE = NONE
      | F (SOME(s1,s2)) =
	let
	    fun G NONE = F (getItem s2)
	      | G (SOME(x,s)) = SOME(x,make (fn () => G (getItem s)))
	in
	    G (getItem s1)
	end
in
fun concat s = make (fn () => F (getItem s))
end

fun app f =
    let
	fun F NONE = ()
	  | F (SOME(x,s)) =
	    (f x;
	     F (getItem s))
    in
	F o getItem
    end

fun map f =
    let
	fun F NONE = NONE
	  | F (SOME(x,s)) = SOME(f x,F' s)
	and F' s = make (fn() => F (getItem s))
    in
	F'
    end

fun mapPartial f =
    let
	fun F NONE = NONE
	  | F (SOME(x,s)) =
	    (case f x of
		 SOME y => SOME(y,F' s)
	       | NONE => F (getItem s))
	and F' s = make (fn()=> F (getItem s))
    in
	F'
    end

fun find P =
    let
	fun F NONE = NONE
	  | F (SOME(x,s)) =
	    if P x
	    then SOME x
	    else F (getItem s)
    in
	F o getItem
    end

(*fun filter p = mapPartial (fn x => if p x then SOME x else NONE)*)

fun filter P =
    let
	fun F NONE = NONE
	  | F (SOME(x,s)) =
	    if P x
	    then SOME(x,F' s)
	    else F (getItem s)
	and F' s = make (fn () => F (getItem s))
    in
	F'
    end

fun partition f s =
    let
	val s' = map (fn x => (x,f x)) s
    in
	(mapPartial (fn (x,true) => SOME x | _ => NONE) s',
	 mapPartial (fn (x,false) => SOME x | _ => NONE) s')
    end

fun exists P =
    let
	fun F NONE = false
	  | F (SOME(x,s)) = P x orelse F (getItem s)
    in
	F o getItem
    end

fun all P =
    let
	fun F NONE = true
	  | F (SOME(x,s)) = P x andalso F (getItem s)
    in
	F o getItem
    end

(*fun tabulate f = map f (iterates (fn x => x + 1) 0)*)

fun tabulate (n,f) =
    let
	fun F n = make (fn () => SOME(f n,F (n+1)))
    in
	F n
    end

fun collate c (s1,s2) =
    let
	fun F NONE _ = LESS
	  | F _ NONE = GREATER
	  | F (SOME(x,s1)) (SOME(y,s2)) =
	    (case c (x,y) of
		 LESS => LESS
	       | GREATER => GREATER
	       | EQUAL => F' s1 s2)
	and F' s1 s2 = F (getItem s1) (getItem s2)
    in
	F' s1 s2
    end

fun empty  _ = Seq (value NONE)
fun single x = Seq(value (SOME(x,Seq (value NONE))))
fun cons a = Seq(value (SOME a))

fun cycle seqfn =
    let
	val knot = ref (Seq (value NONE))
    in
	knot := seqfn (fn () => !knot);
	!knot
    end

fun iterates f =
    let
	fun F x = make (fn() => SOME(x,F (f x)))
    in
	F
    end

fun interleave (s1,s2) =
    let
	fun F NONE = getItem s2
	  | F (SOME(x,s1')) = SOME(x,interleave(s2,s1'))
    in
	make (fn()=> F (getItem s1))
    end

(* val force_all = app ignore *)

local
    fun F NONE = ()
      | F (SOME(x,s)) = F (getItem s)
in
fun force_all s = F (getItem s)
end

fun of_function f =
    let
	fun F () = case f () of
		       SOME x => SOME(x,make F)
		     | NONE => NONE
    in
	make F
    end

local
    fun F [] = NONE
      | F (x::xs) = SOME(x,F' xs)
    and F' xs = make (fn () => F xs)
in
fun of_list xs = F' xs
end

val of_string = of_list o String.explode

fun of_instream is =
    let
	val buffer : char list ref = ref []
	fun get_input () =
	    case !buffer of
		(c::cs) => (buffer:=cs;
			    SOME c)
	      |	[] => (case String.explode (TextIO.input is) of
			   [] => NONE
			 | (c::cs) => (buffer := cs;
				       SOME c))
    in
	of_function get_input
    end

local
    fun F k NONE = k []
      | F k (SOME(x,s)) = F (fn xs => k (x::xs)) (getItem s)
in
fun list_of s = F (fn x => x) (getItem s)
end

(* Adapted from seq.ML *)

val succeed = single
fun fail _ = Seq (value NONE)

(* fun op THEN (f, g) x = flat (map g (f x)) *)

fun op THEN (f, g) =
    let
	fun F NONE = NONE
	  | F (SOME(x,xs)) =
	    let
		fun G NONE = F (getItem xs)
		  | G (SOME(y,ys)) = SOME(y,make (fn () => G (getItem ys)))
	    in
		G (getItem (g x))
	    end
    in
	fn x => make (fn () => F (getItem (f x)))
    end

fun op ORELSE (f, g) x =
    make (fn () =>
	     case getItem (f x) of
		 NONE => getItem (g x)
	       | some => some)

fun op APPEND (f, g) x =
    let
	fun copy s =
	    case getItem s of
		NONE => getItem (g x)
	      | SOME(x,xs) => SOME(x,make (fn () => copy xs))
    in
	make (fn () => copy (f x))
    end

fun EVERY fs = foldr (op THEN) succeed fs
fun FIRST fs = foldr (op ORELSE) fail fs

fun TRY f x =
    make (fn () =>
	     case getItem (f x) of
		 NONE => SOME(x,Seq (value NONE))
	       | some => some)

fun REPEAT f =
    let
	fun rep qs x =
	    case getItem (f x) of
		NONE => SOME(x, make (fn () => repq qs))
	      | SOME (x', q) => rep (q :: qs) x'
	and repq [] = NONE
	  | repq (q :: qs) =
            case getItem q of
		NONE => repq qs
              | SOME (x, q) => rep (q :: qs) x
    in
     fn x => make (fn () => rep [] x)
    end

fun REPEAT1 f = op THEN (f, REPEAT f);

fun INTERVAL f i =
    let
	fun F j =
	    if i > j
	    then single
	    else op THEN (f j, F (j - 1))
    in F end

fun DETERM f x =
    make (fn () =>
	     case getItem (f x) of
		 NONE => NONE
	       | SOME (x', _) => SOME(x',Seq (value NONE)))

(*partial function as procedure*)
fun try f x =
    make (fn () =>
	     case Library.try f x of
		 SOME y => SOME(y,Seq (value NONE))
	       | NONE => NONE)

(*functional to print a sequence, up to "count" elements;
  the function prelem should print the element number and also the element*)
fun print prelem count seq =
    let
	fun pr k xq =
	    if k > count
	    then ()
	    else
		case getItem xq of
		    NONE => ()
		  | SOME (x, xq') =>
		    (prelem k x;
		     writeln "";
		     pr (k + 1) xq')
    in
	pr 1 seq
    end

(*accumulating a function over a sequence; this is lazy*)
fun it_right f (xq, yq) =
    let
	fun its s =
	    make (fn () =>
		     case getItem s of
			 NONE => getItem yq
		       | SOME (a, s') => getItem(f (a, its s')))
    in
	its xq
    end

(*map over a sequence s1, append the sequence s2*)
fun mapp f s1 s2 =
    let
	fun F NONE = getItem s2
	  | F (SOME(x,s1')) = SOME(f x,F' s1')
	and F' s = make (fn () => F (getItem s))
    in
	F' s1
    end

(*turn a list of sequences into a sequence of lists*)
local
    fun F [] = SOME([],Seq (value NONE))
      | F (xq :: xqs) =
        case getItem xq of
            NONE => NONE
          | SOME (x, xq') =>
            (case F xqs of
		 NONE => NONE
	       | SOME (xs, xsq) =>
		 let
		     fun G s =
			 make (fn () =>
				  case getItem s of
				      NONE => F (xq' :: xqs)
				    | SOME(ys,ysq) => SOME(x::ys,G ysq))
		 in
		     SOME (x :: xs, G xsq)
		 end)
in
fun commute xqs = make (fn () => F xqs)
end

(*the list of the first n elements, paired with rest of sequence;
  if length of list is less than n, then sequence had less than n elements*)
fun chop (n, xq) =
    if n <= 0
    then ([], xq)
    else
	case getItem xq of
	    NONE => ([], xq)
	  | SOME (x, xq') => apfst (Library.cons x) (chop (n - 1, xq'))

fun foldl f e s =
    let
	fun F k NONE = k e
	  | F k (SOME(x,s)) = F (fn y => k (f(x,y))) (getItem s)
    in
	F (fn x => x) (getItem s)
    end

fun foldr f e s =
    let
	fun F e NONE = e
	  | F e (SOME(x,s)) = F (f(x,e)) (getItem s)
    in
	F e (getItem s)
    end

fun fromString s = of_list (explode s)

end

structure LazyScan = Scanner (structure Seq = LazySeq)

