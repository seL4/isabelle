(* $Id$ *)

signature LAZY_SCAN =
sig

    exception SyntaxError

    type ('a,'b) scanner = 'a LazySeq.seq -> 'b * 'a LazySeq.seq

    val :--      : ('a,'b) scanner * ('b -> ('a,'c) scanner)
		   -> ('a,'b*'c) scanner
    val --       : ('a,'b) scanner * ('a,'c) scanner -> ('a,'b*'c) scanner
    val >>       : ('a,'b) scanner * ('b -> 'c) -> ('a,'c) scanner
    val --|      : ('a,'b) scanner * ('a,'c) scanner -> ('a,'b) scanner
    val |--      : ('a,'b) scanner * ('a,'c) scanner -> ('a,'c) scanner
    val ^^       : ('a,string) scanner * ('a,string) scanner
		   -> ('a,string) scanner
    val ||       : ('a,'b) scanner * ('a,'b) scanner -> ('a,'b) scanner
    val one      : ('a -> bool) -> ('a,'a) scanner
    val succeed  : 'b -> ('a,'b) scanner
    val any      : ('a -> bool) -> ('a,'a list) scanner
    val any1     : ('a -> bool) -> ('a,'a list) scanner
    val optional : ('a,'b) scanner -> 'b -> ('a,'b) scanner
    val option   : ('a,'b) scanner -> ('a,'b option) scanner
    val repeat   : ('a,'b) scanner -> ('a,'b list) scanner
    val repeat1  : ('a,'b) scanner -> ('a,'b list) scanner
    val ahead    : ('a,'b) scanner -> ('a,'b) scanner
    val unless   : ('a LazySeq.seq -> bool) -> ('a,'b) scanner -> ('a,'b) scanner
    val $$       : ''a -> (''a,''a) scanner
    val !!       : ('a LazySeq.seq -> string) -> ('a,'b) scanner -> ('a,'b) scanner
    val scan_full: ('a,'b) scanner -> 'a LazySeq.seq -> 'b LazySeq.seq

end

structure LazyScan :> LAZY_SCAN =
struct

infix 7 |-- --|
infix 5 :-- -- ^^
infix 3 >>
infix 0 ||

exception SyntaxError
exception Fail of string

type ('a,'b) scanner = 'a LazySeq.seq -> 'b * 'a LazySeq.seq

fun (sc1 :-- sc2) toks =
    let
	val (x,toks2) = sc1 toks
	val (y,toks3) = sc2 x toks2
    in
	((x,y),toks3)
    end

fun (sc1 -- sc2) toks =
    let
	val (x,toks2) = sc1 toks
	val (y,toks3) = sc2 toks2
    in
	((x,y),toks3)
    end

fun (sc >> f) toks =
    let
	val (x,toks2) = sc toks
    in
	(f x,toks2)
    end

fun (sc1 --| sc2) toks =
    let
	val (x,toks2) = sc1 toks
	val (_,toks3) = sc2 toks2
    in
	(x,toks3)
    end

fun (sc1 |-- sc2) toks =
    let
	val (_,toks2) = sc1 toks
    in
	sc2 toks2
    end

fun (sc1 ^^ sc2) toks =
    let
	val (x,toks2) = sc1 toks
	val (y,toks3) = sc2 toks2
    in
	(x^y,toks3)
    end

fun (sc1 || sc2) toks =
    (sc1 toks)
    handle SyntaxError => sc2 toks

fun one p toks =
    case LazySeq.getItem toks of
	None => raise SyntaxError
      | Some(t,toks) => if p t
			then (t,toks)
			else raise SyntaxError

fun succeed e toks = (e,toks)

fun any p toks =
    case LazySeq.getItem toks of
	None =>  ([],toks)
      | Some(x,toks2) => if p x
			 then
			     let
				 val (xs,toks3) = any p toks2
			     in
				 (x::xs,toks3)
			     end
			 else ([],toks)

fun any1 p toks =
    let
	val (x,toks2) = one p toks
	val (xs,toks3) = any p toks2
    in
	(x::xs,toks3)
    end

fun optional sc def =  sc || succeed def
fun option sc = (sc >> Some) || succeed None

(*
fun repeat sc =
    let
	fun R toks =
	    let
		val (x,toks2) = sc toks
		val (xs,toks3) = R toks2
	    in
		(x::xs,toks3)
	    end
	    handle SyntaxError => ([],toks)
    in
	R
    end
*)

(* A tail-recursive version of repeat.  It is (ever so) slightly slower
 * than the above, non-tail-recursive version (due to the garbage generation
 * associated with the reversal of the list).  However,  this version will be
 * able to process input where the former version must give up (due to stack
 * overflow).  The slowdown seems to be around the one percent mark.
 *)
fun repeat sc =
    let
	fun R xs toks =
	    case Some (sc toks) handle SyntaxError => None of
		Some (x,toks2) => R (x::xs) toks2
	      | None => (List.rev xs,toks)
    in
	R []
    end

fun repeat1 sc toks =
    let
	val (x,toks2) = sc toks
	val (xs,toks3) = repeat sc toks2
    in
	(x::xs,toks3)
    end

fun ahead (sc:'a->'b*'a) toks = (#1 (sc toks),toks)

fun unless test sc toks =
    let
	val test_failed = (test toks;false) handle SyntaxError => true
    in
	if test_failed
	then sc toks
	else raise SyntaxError
    end

fun $$ arg = one (fn x => x = arg)

fun !! f sc toks = (sc toks
		    handle SyntaxError => raise Fail (f toks))

fun scan_full sc toks =
    let
	fun F toks =
	    if LazySeq.null toks
	    then None
	    else
		let
		    val (x,toks') = sc toks
		in
		    Some(x,LazySeq.make (fn () => F toks'))
		end
    in
	LazySeq.make (fn () => F toks)
    end

end
