(*  Title:      Pure/morphism.ML
    ID:         $Id$
    Author:     Makarius

Abstract morphisms on formal entities.
*)

infix 1 $>

signature BASIC_MORPHISM =
sig
  type morphism
  val $> : morphism * morphism -> morphism
end

signature MORPHISM =
sig
  include BASIC_MORPHISM
  val var: morphism -> string * mixfix -> string * mixfix
  val name: morphism -> string -> string
  val typ: morphism -> typ -> typ
  val term: morphism -> term -> term
  val thm: morphism -> thm -> thm
  val morphism:
   {name: string -> string,
    var: string * mixfix -> string * mixfix,
    typ: typ -> typ,
    term: term -> term,
    thm: thm -> thm} -> morphism
  val comp: morphism -> morphism -> morphism
  val identity: morphism
  val transfer: theory -> morphism
end;

structure Morphism: MORPHISM =
struct

datatype morphism = Morphism of
 {name: string -> string,
  var: string * mixfix -> string * mixfix,
  typ: typ -> typ,
  term: term -> term,
  thm: thm -> thm};

fun name (Morphism {name, ...}) = name;
fun var (Morphism {var, ...}) = var;
fun typ (Morphism {typ, ...}) = typ;
fun term (Morphism {term, ...}) = term;
fun thm (Morphism {thm, ...}) = thm;

val morphism = Morphism;

fun comp
    (Morphism {name = name1, var = var1, typ = typ1, term = term1, thm = thm1})
    (Morphism {name = name2, var = var2, typ = typ2, term = term2, thm = thm2}) =
  morphism {name = name1 o name2, var = var1 o var2,
    typ = typ1 o typ2, term = term1 o term2, thm = thm1 o thm2};

fun phi1 $> phi2 = comp phi2 phi1;

val identity = morphism {name = I, var = I, typ = I, term = I, thm = I};

fun transfer thy = morphism {name = I, var = I, typ = I, term = I, thm = Thm.transfer thy};

end;

structure BasicMorphism: BASIC_MORPHISM = Morphism;
open BasicMorphism;

