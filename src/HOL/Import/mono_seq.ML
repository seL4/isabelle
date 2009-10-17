(*  Title:      HOL/Import/mono_seq.ML
    ID:         $Id$
    Author:     Steven Obua, TU Muenchen

    Monomorphic sequences.
*)

(* The trouble is that signature / structures cannot depend on type variable parameters ... *)

signature MONO_SCANNER_SEQ =
sig
    type seq
    type item
    
    val pull : seq -> (item * seq) option 
end

signature MONO_EXTENDED_SCANNER_SEQ =
sig

  include MONO_SCANNER_SEQ

  val null : seq -> bool
  val length : seq -> int
  val take_at_most : seq -> int -> item list

end

functor MonoExtendScannerSeq (structure Seq : MONO_SCANNER_SEQ) : MONO_EXTENDED_SCANNER_SEQ =
struct
  
type seq = Seq.seq
type item = Seq.item
val pull = Seq.pull

fun null s = is_none (pull s)

fun take_at_most s n = 
    if n <= 0 then [] else
    case pull s of 
        NONE => []
      | SOME (x,s') => x::(take_at_most s' (n-1))

fun length' s n = 
    case pull s of
        NONE => n
      | SOME (_, s') => length' s' (n+1)

fun length s = length' s 0
                
end  


structure StringScannerSeq : 
          sig 
              include MONO_EXTENDED_SCANNER_SEQ 
              val fromString : string -> seq
          end
  =
struct

structure Incubator : MONO_SCANNER_SEQ =
struct

type seq = string * int * int
type item = string

fun pull (s, len, i) = if i >= len then NONE else SOME (String.substring (s, i, 1), (s, len, i+1))
end

structure Extended = MonoExtendScannerSeq (structure Seq = Incubator)
open Extended

fun fromString s = (s, String.size s, 0)

end

