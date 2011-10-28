(*  Title:      Pure/morphism.ML
    Author:     Makarius

Abstract morphisms on formal entities.
*)

infix 1 $>

signature BASIC_MORPHISM =
sig
  type morphism
  type declaration = morphism -> Context.generic -> Context.generic
  val $> : morphism * morphism -> morphism
end

signature MORPHISM =
sig
  include BASIC_MORPHISM
  type 'a funs = ('a -> 'a) list
  val binding: morphism -> binding -> binding
  val typ: morphism -> typ -> typ
  val term: morphism -> term -> term
  val fact: morphism -> thm list -> thm list
  val thm: morphism -> thm -> thm
  val cterm: morphism -> cterm -> cterm
  val morphism:
   {binding: binding funs,
    typ: typ funs,
    term: term funs,
    fact: thm list funs} -> morphism
  val binding_morphism: (binding -> binding) -> morphism
  val typ_morphism: (typ -> typ) -> morphism
  val term_morphism: (term -> term) -> morphism
  val fact_morphism: (thm list -> thm list) -> morphism
  val thm_morphism: (thm -> thm) -> morphism
  val identity: morphism
  val compose: morphism -> morphism -> morphism
  val transform: morphism -> (morphism -> 'a) -> morphism -> 'a
  val form: (morphism -> 'a) -> 'a
end;

structure Morphism: MORPHISM =
struct

type 'a funs = ('a -> 'a) list;
fun apply fs = fold_rev (fn f => fn x => f x) fs;

datatype morphism = Morphism of
 {binding: binding funs,
  typ: typ funs,
  term: term funs,
  fact: thm list funs};

type declaration = morphism -> Context.generic -> Context.generic;

fun binding (Morphism {binding, ...}) = apply binding;
fun typ (Morphism {typ, ...}) = apply typ;
fun term (Morphism {term, ...}) = apply term;
fun fact (Morphism {fact, ...}) = apply fact;
val thm = singleton o fact;
val cterm = Drule.cterm_rule o thm;

val morphism = Morphism;

fun binding_morphism binding = morphism {binding = [binding], typ = [], term = [], fact = []};
fun typ_morphism typ = morphism {binding = [], typ = [typ], term = [], fact = []};
fun term_morphism term = morphism {binding = [], typ = [], term = [term], fact = []};
fun fact_morphism fact = morphism {binding = [], typ = [], term = [], fact = [fact]};
fun thm_morphism thm = morphism {binding = [], typ = [], term = [], fact = [map thm]};

val identity = morphism {binding = [], typ = [], term = [], fact = []};

fun compose
    (Morphism {binding = binding1, typ = typ1, term = term1, fact = fact1})
    (Morphism {binding = binding2, typ = typ2, term = term2, fact = fact2}) =
  morphism {binding = binding1 @ binding2, typ = typ1 @ typ2,
    term = term1 @ term2, fact = fact1 @ fact2};

fun phi1 $> phi2 = compose phi2 phi1;

fun transform phi f = fn psi => f (phi $> psi);
fun form f = f identity;

end;

structure Basic_Morphism: BASIC_MORPHISM = Morphism;
open Basic_Morphism;
