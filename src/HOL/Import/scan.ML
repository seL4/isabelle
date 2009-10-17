(*  Title:      HOL/Import/scan.ML
    Author:     Sebastian Skalberg, TU Muenchen / Steven Obua, TU Muenchen

Scanner combinators for sequences.
*)

signature SCANNER =
sig

    include SCANNER_SEQ

    exception SyntaxError

    type ('a,'b) scanner = 'a seq -> 'b * 'a seq

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
    val anyone   : ('a,'a) scanner
    val succeed  : 'b -> ('a,'b) scanner
    val any      : ('a -> bool) -> ('a,'a list) scanner
    val any1     : ('a -> bool) -> ('a,'a list) scanner
    val optional : ('a,'b) scanner -> 'b -> ('a,'b) scanner
    val option   : ('a,'b) scanner -> ('a,'b option) scanner
    val repeat   : ('a,'b) scanner -> ('a,'b list) scanner
    val repeat1  : ('a,'b) scanner -> ('a,'b list) scanner
    val repeat_fixed : int -> ('a, 'b) scanner -> ('a, 'b list) scanner  
    val ahead    : ('a,'b) scanner -> ('a,'b) scanner
    val unless   : ('a, 'b) scanner -> ('a,'c) scanner -> ('a,'c) scanner
    val $$       : ''a -> (''a,''a) scanner
    val !!       : ('a seq -> string) -> ('a,'b) scanner -> ('a,'b) scanner
    
    val scan_id : (string, string) scanner
    val scan_nat : (string, int) scanner

    val this : ''a list -> (''a, ''a list) scanner
    val this_string : string -> (string, string) scanner
end

functor Scanner (structure Seq : SCANNER_SEQ) : SCANNER =
struct

infix 7 |-- --|
infix 5 :-- -- ^^
infix 3 >>
infix 0 ||

exception SyntaxError
exception Fail of string

type 'a seq = 'a Seq.seq
type ('a,'b) scanner = 'a seq -> 'b * 'a seq

val pull = Seq.pull

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

fun anyone toks = case pull toks of NONE => raise SyntaxError | SOME x => x

fun one p toks = case anyone toks of x as (t, toks) => if p t then x else raise SyntaxError

fun succeed e toks = (e,toks)

fun any p toks =
    case pull toks of
        NONE =>  ([],toks)
      | SOME(x,toks2) => if p x
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
fun option sc = (sc >> SOME) || succeed NONE

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
            case SOME (sc toks) handle SyntaxError => NONE of
                SOME (x,toks2) => R (x::xs) toks2
              | NONE => (List.rev xs,toks)
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

fun repeat_fixed n sc =
    let
        fun R n xs toks =
            if (n <= 0) then (List.rev xs, toks)
            else case (sc toks) of (x, toks2) => R (n-1) (x::xs) toks2
    in
        R n []
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

val scan_id = one Symbol.is_letter ^^ (any Symbol.is_letdig >> implode);

val nat_of_list = the o Int.fromString o implode 

val scan_nat = repeat1 (one Symbol.is_digit) >> nat_of_list 

fun this [] = (fn toks => ([], toks))
  | this (xs' as (x::xs)) = one (fn y => x=y) -- this xs >> K xs'

fun this_string s = this (explode s) >> K s

end

