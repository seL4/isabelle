signature LAZY_SEQ =
sig

    type 'a seq

    (* From LIST *)

    val null : 'a seq -> bool
    val length : 'a seq -> int
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
fun make f = Seq (delay f)

fun null s = is_some (getItem s)

local
    fun F n None = n
      | F n (Some(_,s)) = F (n+1) (getItem s)
in
fun length s = F 0 (getItem s)
end

fun s1 @ s2 =
    let
	fun F None = getItem s2
	  | F (Some(x,s1')) = Some(x,F' s1')
	and F' s = make (fn () => F (getItem s))
    in
	F' s1
    end

local
    fun F None = raise Empty
      | F (Some arg) = arg
in
fun hd s = #1 (F (getItem s))
fun tl s = #2 (F (getItem s))
end

local
    fun F x None = x
      | F _ (Some(x,s)) = F x (getItem s)
    fun G None = raise Empty
      | G (Some(x,s)) = F x (getItem s)
in
fun last s = G (getItem s)
end

local
    fun F None _ = raise Subscript
      | F (Some(x,_)) 0 = x
      | F (Some(_,s)) n = F (getItem s) (n-1)
in
fun nth(s,n) =
    if n < 0
    then raise Subscript
    else F (getItem s) n
end

local
    fun F None _ = raise Subscript
      | F (Some(x,s)) n = Some(x,F' s (n-1))
    and F' s 0 = Seq (value None)
      | F' s n = make (fn () => F (getItem s) n)
in
fun take (s,n) =
    if n < 0
    then raise Subscript
    else F' s n
end

local
    fun F s 0 = s
      | F None _ = raise Subscript
      | F (Some(_,s)) n = F (getItem s) (n-1)
in
fun drop (s,0) = s
  | drop (s,n) = 
    if n < 0
    then raise Subscript
    else make (fn () => F (getItem s) n)
end

local
    fun F s None = s
      | F s (Some(x,s')) = F (Some(x, Seq (value s))) (getItem s')
in
fun rev s = make (fn () => F None (getItem s))
end

local
    fun F s None = getItem s
      | F s (Some(x,s')) = F (Seq (value (Some(x,s)))) (getItem s')
in
fun revAppend (s1,s2) = make (fn () => F s2 (getItem s1))
end

local
    fun F None = None
      | F (Some(s1,s2)) =
	let
	    fun G None = F (getItem s2)
	      | G (Some(x,s)) = Some(x,make (fn () => G (getItem s)))
	in
	    G (getItem s1)
	end
in
fun concat s = make (fn () => F (getItem s))
end

fun app f =
    let
	fun F None = ()
	  | F (Some(x,s)) =
	    (f x;
	     F (getItem s))
    in
	F o getItem
    end

fun map f =
    let
	fun F None = None
	  | F (Some(x,s)) = Some(f x,F' s)
	and F' s = make (fn() => F (getItem s))
    in
	F'
    end

fun mapPartial f =
    let
	fun F None = None
	  | F (Some(x,s)) =
	    (case f x of
		 Some y => Some(y,F' s)
	       | None => F (getItem s))
	and F' s = make (fn()=> F (getItem s))
    in
	F'
    end

fun find P =
    let
	fun F None = None
	  | F (Some(x,s)) =
	    if P x
	    then Some x
	    else F (getItem s)
    in
	F o getItem
    end

(*fun filter p = mapPartial (fn x => if p x then Some x else None)*)

fun filter P =
    let
	fun F None = None
	  | F (Some(x,s)) =
	    if P x
	    then Some(x,F' s)
	    else F (getItem s)
	and F' s = make (fn () => F (getItem s))
    in
	F'
    end

fun partition f s =
    let
	val s' = map (fn x => (x,f x)) s
    in
	(mapPartial (fn (x,true) => Some x | _ => None) s',
	 mapPartial (fn (x,false) => Some x | _ => None) s')
    end

fun exists P =
    let
	fun F None = false
	  | F (Some(x,s)) = P x orelse F (getItem s)
    in
	F o getItem
    end

fun all P =
    let
	fun F None = true
	  | F (Some(x,s)) = P x andalso F (getItem s)
    in
	F o getItem
    end

(*fun tabulate f = map f (iterates (fn x => x + 1) 0)*)

fun tabulate (n,f) =
    let
	fun F n = make (fn () => Some(f n,F (n+1)))
    in
	F n
    end

fun collate c (s1,s2) =
    let
	fun F None _ = LESS
	  | F _ None = GREATER
	  | F (Some(x,s1)) (Some(y,s2)) =
	    (case c (x,y) of
		 LESS => LESS
	       | GREATER => GREATER
	       | EQUAL => F' s1 s2)
	and F' s1 s2 = F (getItem s1) (getItem s2)
    in
	F' s1 s2
    end

fun empty  _ = Seq (value None)
fun single x = Seq(value (Some(x,Seq (value None))))
fun cons a = Seq(value (Some a))

fun cycle seqfn =
    let
	val knot = ref (Seq (value None))
    in
	knot := seqfn (fn () => !knot);
	!knot
    end

fun iterates f =
    let
	fun F x = make (fn() => Some(x,F (f x)))
    in
	F
    end

fun interleave (s1,s2) =
    let
	fun F None = getItem s2
	  | F (Some(x,s1')) = Some(x,interleave(s2,s1'))
    in
	make (fn()=> F (getItem s1))
    end

(* val force_all = app ignore *)

local
    fun F None = ()
      | F (Some(x,s)) = F (getItem s)
in
val force_all = F o getItem
end

fun of_function f =
    let
	fun F () = case f () of
		       Some x => Some(x,make F)
		     | None => None
    in
	make F
    end

local
    fun F [] = None
      | F (x::xs) = Some(x,F' xs)
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
			    Some c)
	      |	[] => (case String.explode (TextIO.input is) of
			   [] => None
			 | (c::cs) => (buffer := cs;
				       Some c))
    in
	of_function get_input
    end

local
    fun F k None = k []
      | F k (Some(x,s)) = F (fn xs => k (x::xs)) (getItem s)
in
fun list_of s = F (fn x => x) (getItem s)
end

(* Adapted from seq.ML *)

val succeed = single
fun fail _ = Seq (value None)

(* fun op THEN (f, g) x = flat (map g (f x)) *)

fun op THEN (f, g) =
    let
	fun F None = None
	  | F (Some(x,xs)) =
	    let
		fun G None = F (getItem xs)
		  | G (Some(y,ys)) = Some(y,make (fn () => G (getItem ys)))
	    in
		G (getItem (g x))
	    end
    in
	fn x => make (fn () => F (getItem (f x)))
    end

fun op ORELSE (f, g) x =
    make (fn () =>
	     case getItem (f x) of
		 None => getItem (g x)
	       | some => some)

fun op APPEND (f, g) x =
    let
	fun copy s =
	    case getItem s of
		None => getItem (g x)
	      | Some(x,xs) => Some(x,make (fn () => copy xs))
    in
	make (fn () => copy (f x))
    end

fun EVERY fs = foldr THEN (fs, succeed)
fun FIRST fs = foldr ORELSE (fs, fail)

fun TRY f x =
    make (fn () =>
	     case getItem (f x) of
		 None => Some(x,Seq (value None))
	       | some => some)

fun REPEAT f =
    let
	fun rep qs x =
	    case getItem (f x) of
		None => Some(x, make (fn () => repq qs))
	      | Some (x', q) => rep (q :: qs) x'
	and repq [] = None
	  | repq (q :: qs) =
            case getItem q of
		None => repq qs
              | Some (x, q) => rep (q :: qs) x
    in
     fn x => make (fn () => rep [] x)
    end

fun REPEAT1 f = THEN (f, REPEAT f);

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
		 None => None
	       | Some (x', _) => Some(x',Seq (value None)))

(*partial function as procedure*)
fun try f x =
    make (fn () =>
	     case Library.try f x of
		 Some y => Some(y,Seq (value None))
	       | None => None)

(*functional to print a sequence, up to "count" elements;
  the function prelem should print the element number and also the element*)
fun print prelem count seq =
    let
	fun pr k xq =
	    if k > count
	    then ()
	    else
		case getItem xq of
		    None => ()
		  | Some (x, xq') =>
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
			 None => getItem yq
		       | Some (a, s') => getItem(f (a, its s')))
    in
	its xq
    end

(*map over a sequence s1, append the sequence s2*)
fun mapp f s1 s2 =
    let
	fun F None = getItem s2
	  | F (Some(x,s1')) = Some(f x,F' s1')
	and F' s = make (fn () => F (getItem s))
    in
	F' s1
    end

(*turn a list of sequences into a sequence of lists*)
local
    fun F [] = Some([],Seq (value None))
      | F (xq :: xqs) =
        case getItem xq of
            None => None
          | Some (x, xq') =>
            (case F xqs of
		 None => None
	       | Some (xs, xsq) =>
		 let
		     fun G s =
			 make (fn () =>
				  case getItem s of
				      None => F (xq' :: xqs)
				    | Some(ys,ysq) => Some(x::ys,G ysq))
		 in
		     Some (x :: xs, G xsq)
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
	    None => ([], xq)
	  | Some (x, xq') => apfst (Library.cons x) (chop (n - 1, xq'))

fun foldl f e s =
    let
	fun F k None = k e
	  | F k (Some(x,s)) = F (fn y => k (f(x,y))) (getItem s)
    in
	F (fn x => x) (getItem s)
    end

fun foldr f e s =
    let
	fun F e None = e
	  | F e (Some(x,s)) = F (f(x,e)) (getItem s)
    in
	F e (getItem s)
    end

end
