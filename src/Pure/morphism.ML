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
  exception MORPHISM of string * exn
  val morphism: string ->
   {binding: (binding -> binding) list,
    typ: (typ -> typ) list,
    term: (term -> term) list,
    fact: (thm list -> thm list) list} -> morphism
  val pretty: morphism -> Pretty.T
  val binding: morphism -> binding -> binding
  val binding_prefix: morphism -> (string * bool) list
  val typ: morphism -> typ -> typ
  val term: morphism -> term -> term
  val fact: morphism -> thm list -> thm list
  val thm: morphism -> thm -> thm
  val cterm: morphism -> cterm -> cterm
  val identity: morphism
  val compose: morphism -> morphism -> morphism
  val transform: morphism -> (morphism -> 'a) -> morphism -> 'a
  val form: (morphism -> 'a) -> 'a
  val binding_morphism: string -> (binding -> binding) -> morphism
  val typ_morphism: string -> (typ -> typ) -> morphism
  val term_morphism: string -> (term -> term) -> morphism
  val fact_morphism: string -> (thm list -> thm list) -> morphism
  val thm_morphism: string -> (thm -> thm) -> morphism
  val transfer_morphism: theory -> morphism
  val transfer_morphism': Proof.context -> morphism
  val transfer_morphism'': Context.generic -> morphism
  val trim_context_morphism: morphism
  val instantiate_frees_morphism:
    ((string * sort) * ctyp) list * ((string * typ) * cterm) list -> morphism
  val instantiate_morphism:
    ((indexname * sort) * ctyp) list * ((indexname * typ) * cterm) list -> morphism
end;

structure Morphism: MORPHISM =
struct

(* named functions *)

type 'a funs = (string * ('a -> 'a)) list;

exception MORPHISM of string * exn;

fun app (name, f) x = f x
  handle exn =>
    if Exn.is_interrupt exn then Exn.reraise exn else raise MORPHISM (name, exn);

fun apply fs = fold_rev app fs;


(* type morphism *)

datatype morphism = Morphism of
 {names: string list,
  binding: binding funs,
  typ: typ funs,
  term: term funs,
  fact: thm list funs};

type declaration = morphism -> Context.generic -> Context.generic;

fun morphism a {binding, typ, term, fact} =
  Morphism {
    names = if a = "" then [] else [a],
    binding = map (pair a) binding,
    typ = map (pair a) typ,
    term = map (pair a) term,
    fact = map (pair a) fact};

fun pretty (Morphism {names, ...}) = Pretty.enum ";" "{" "}" (map Pretty.str (rev names));

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_polyml o pretty);

fun binding (Morphism {binding, ...}) = apply binding;
fun binding_prefix morph = Binding.name "x" |> binding morph |> Binding.prefix_of;
fun typ (Morphism {typ, ...}) = apply typ;
fun term (Morphism {term, ...}) = apply term;
fun fact (Morphism {fact, ...}) = apply fact;
val thm = singleton o fact;
val cterm = Drule.cterm_rule o thm;


(* morphism combinators *)

val identity = morphism "" {binding = [], typ = [], term = [], fact = []};

fun compose
    (Morphism {names = names1, binding = binding1, typ = typ1, term = term1, fact = fact1})
    (Morphism {names = names2, binding = binding2, typ = typ2, term = term2, fact = fact2}) =
  Morphism {
    names = names1 @ names2,
    binding = binding1 @ binding2,
    typ = typ1 @ typ2,
    term = term1 @ term2,
    fact = fact1 @ fact2};

fun phi1 $> phi2 = compose phi2 phi1;

fun transform phi f = fn psi => f (phi $> psi);
fun form f = f identity;


(* concrete morphisms *)

fun binding_morphism a binding = morphism a {binding = [binding], typ = [], term = [], fact = []};
fun typ_morphism a typ = morphism a {binding = [], typ = [typ], term = [], fact = []};
fun term_morphism a term = morphism a {binding = [], typ = [], term = [term], fact = []};
fun fact_morphism a fact = morphism a {binding = [], typ = [], term = [], fact = [fact]};
fun thm_morphism a thm = morphism a {binding = [], typ = [], term = [], fact = [map thm]};

val transfer_morphism = thm_morphism "transfer" o Thm.join_transfer;
val transfer_morphism' = transfer_morphism o Proof_Context.theory_of;
val transfer_morphism'' = transfer_morphism o Context.theory_of;

val trim_context_morphism = thm_morphism "trim_context" Thm.trim_context;


(* instantiate *)

fun instantiate_frees_morphism ([], []) = identity
  | instantiate_frees_morphism (cinstT, cinst) =
      let
        val instT =
          Term_Subst.TFrees.build
            (cinstT |> fold (fn (v, cT) => Term_Subst.TFrees.add (v, Thm.typ_of cT)));
        val inst =
          Term_Subst.Frees.build
            (cinst |> fold (fn (v, ct) => Term_Subst.Frees.add (v, Thm.term_of ct)));
      in
        morphism "instantiate_frees"
          {binding = [],
           typ =
            if Term_Subst.TFrees.is_empty instT then []
            else [Term_Subst.instantiateT_frees instT],
           term = [Term_Subst.instantiate_frees (instT, inst)],
           fact = [map (Thm.instantiate_frees (cinstT, cinst))]}
      end;

fun instantiate_morphism ([], []) = identity
  | instantiate_morphism (cinstT, cinst) =
      let
        val instT =
          Term_Subst.TVars.build (cinstT |> fold (fn (v, cT) =>
            Term_Subst.TVars.add (v, Thm.typ_of cT)));
        val inst =
          Term_Subst.Vars.build (cinst |> fold (fn (v, ct) =>
            Term_Subst.Vars.add (v, Thm.term_of ct)));
      in
        morphism "instantiate"
          {binding = [],
           typ =
            if Term_Subst.TVars.is_empty instT then []
            else [Term_Subst.instantiateT instT],
           term = [Term_Subst.instantiate (instT, inst)],
           fact = [map (Thm.instantiate (cinstT, cinst))]}
      end;

end;

structure Basic_Morphism: BASIC_MORPHISM = Morphism;
open Basic_Morphism;
