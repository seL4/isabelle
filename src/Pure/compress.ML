(*  Title:      Pure/compress.ML
    ID:         $Id$
    Author:     Lawrence C Paulson and Makarius

Compression of terms and types by sharing common subtrees.  Saves
50-75% on storage requirements.  As it is a bit slow, it should be
called only for axioms, stored theorems, etc.
*)

signature COMPRESS =
sig
  val init_data: theory -> theory
  val typ: theory -> typ -> typ
  val term: theory -> term -> term
end;

structure Compress: COMPRESS =
struct


(* theory data *)

structure CompressData = TheoryDataFun
(struct
  val name = "Pure/compress";
  type T = typ Typtab.table ref * term Termtab.table ref;
  val empty : T = (ref Typtab.empty, ref Termtab.empty);
  fun copy (ref typs, ref terms) : T = (ref typs, ref terms);
  val extend = copy;
  fun merge _ ((ref typs1, ref terms1), (ref typs2, ref terms2)) : T =
   (ref (Typtab.merge (K true) (typs1, typs2)),
    ref (Termtab.merge (K true) (terms1, terms2)));
  fun print _ _ = ();
end);

val init_data = CompressData.init;


(* compress types *)

fun typ thy =
  let
    val typs = #1 (CompressData.get thy);
    fun compress T =
      (case Typtab.lookup (! typs, T) of
        SOME T' => T'
      | NONE =>
          let val T' = (case T of Type (a, Ts) => Type (a, map compress Ts) | _ => T)
          in change typs (curry Typtab.update (T', T')); T' end);
  in compress end;


(* compress atomic terms *)

fun term thy =
  let
    val terms = #2 (CompressData.get thy);
    fun compress (t $ u) = compress t $ compress u
      | compress (Abs (a, T, t)) = Abs (a, T, compress t)
      | compress t =
          (case Termtab.lookup (! terms, t) of
            SOME t' => t'
          | NONE => (change terms (curry Termtab.update (t, t)); t));
  in compress o map_term_types (typ thy) end;

end;
