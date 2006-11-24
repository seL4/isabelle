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
  val fact: morphism -> thm list -> thm list
  val thm: morphism -> thm -> thm
  val morphism:
   {name: string -> string,
    var: string * mixfix -> string * mixfix,
    typ: typ -> typ,
    term: term -> term,
    fact: thm list -> thm list} -> morphism
  val name_morphism: (string -> string) -> morphism
  val var_morphism: (string * mixfix -> string * mixfix) -> morphism
  val typ_morphism: (typ -> typ) -> morphism
  val term_morphism: (term -> term) -> morphism
  val fact_morphism: (thm list -> thm list) -> morphism
  val thm_morphism: (thm -> thm) -> morphism
  val identity: morphism
  val comp: morphism -> morphism -> morphism
end;

structure Morphism: MORPHISM =
struct

datatype morphism = Morphism of
 {name: string -> string,
  var: string * mixfix -> string * mixfix,
  typ: typ -> typ,
  term: term -> term,
  fact: thm list -> thm list};

fun name (Morphism {name, ...}) = name;
fun var (Morphism {var, ...}) = var;
fun typ (Morphism {typ, ...}) = typ;
fun term (Morphism {term, ...}) = term;
fun fact (Morphism {fact, ...}) = fact;
val thm = singleton o fact;

val morphism = Morphism;

fun name_morphism name = morphism {name = name, var = I, typ = I, term = I, fact = I};
fun var_morphism var = morphism {name = I, var = var, typ = I, term = I, fact = I};
fun typ_morphism typ = morphism {name = I, var = I, typ = typ, term = I, fact = I};
fun term_morphism term = morphism {name = I, var = I, typ = I, term = term, fact = I};
fun fact_morphism fact = morphism {name = I, var = I, typ = I, term = I, fact = fact};
fun thm_morphism thm = morphism {name = I, var = I, typ = I, term = I, fact = map thm};

val identity = morphism {name = I, var = I, typ = I, term = I, fact = I};

fun comp
    (Morphism {name = name1, var = var1, typ = typ1, term = term1, fact = fact1})
    (Morphism {name = name2, var = var2, typ = typ2, term = term2, fact = fact2}) =
  morphism {name = name1 o name2, var = var1 o var2,
    typ = typ1 o typ2, term = term1 o term2, fact = fact1 o fact2};

fun phi1 $> phi2 = comp phi2 phi1;

end;

structure BasicMorphism: BASIC_MORPHISM = Morphism;
open BasicMorphism;
