(*  Title:      HOL/Import/mono_scan.ML
    ID:         $Id$
    Author:     Steven Obua, TU Muenchen

    Monomorphic scanner combinators for monomorphic sequences.
*)

signature MONO_SCANNER =
sig

    include MONO_SCANNER_SEQ

    exception SyntaxError

    type 'a scanner = seq -> 'a * seq

    val :--      : 'a scanner * ('a -> 'b scanner)
                   -> ('a*'b) scanner
    val --       : 'a scanner * 'b scanner -> ('a * 'b) scanner
    val >>       : 'a scanner * ('a -> 'b) -> 'b scanner
    val --|      : 'a scanner * 'b scanner -> 'a scanner
    val |--      : 'a scanner * 'b scanner -> 'b scanner
    val ^^       : string scanner * string scanner
                   -> string scanner 
    val ||       : 'a scanner * 'a scanner -> 'a scanner
    val one      : (item -> bool) -> item scanner
    val anyone   : item scanner
    val succeed  : 'a -> 'a scanner
    val any      : (item -> bool) -> item list scanner
    val any1     : (item -> bool) -> item list scanner
    val optional : 'a scanner -> 'a -> 'a scanner
    val option   : 'a scanner -> 'a option scanner
    val repeat   : 'a scanner -> 'a list scanner
    val repeat1  : 'a scanner -> 'a list scanner
    val repeat_fixed : int -> 'a scanner -> 'a list scanner  
    val ahead    : 'a scanner -> 'a scanner
    val unless   : 'a scanner -> 'b scanner -> 'b scanner
    val !!       : (seq -> string) -> 'a scanner -> 'a scanner

end

signature STRING_SCANNER =
sig

    include MONO_SCANNER  where type item = string

    val $$       : item -> item scanner
    
    val scan_id : string scanner
    val scan_nat : int scanner

    val this : item list -> item list scanner
    val this_string : string -> string scanner                                      

end    

functor MonoScanner (structure Seq : MONO_SCANNER_SEQ) : MONO_SCANNER =
struct

infix 7 |-- --|
infix 5 :-- -- ^^
infix 3 >>
infix 0 ||

exception SyntaxError
exception Fail of string

type seq = Seq.seq
type item = Seq.item
type 'a scanner = seq -> 'a * seq

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

fun !! f sc toks = (sc toks
                    handle SyntaxError => raise Fail (f toks))

end


structure StringScanner : STRING_SCANNER =
struct

structure Scan = MonoScanner(structure Seq = StringScannerSeq)
open Scan

fun $$ arg = one (fn x => x = arg)

val scan_id = one Symbol.is_letter ^^ (any Symbol.is_letdig >> implode);

val nat_of_list = the o Int.fromString o implode 

val scan_nat = repeat1 (one Symbol.is_digit) >> nat_of_list 

fun this [] = (fn toks => ([], toks))
  | this (xs' as (x::xs)) = one (fn y => x=y) -- this xs >> K xs'

fun this_string s = this (explode s) >> K s

end