(*  Title:      Pure/morphism.ML
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
  exception MORPHISM of string * exn
  val the_theory: theory option -> theory
  val set_context: theory -> morphism -> morphism
  val set_context': Proof.context -> morphism -> morphism
  val set_context'': Context.generic -> morphism -> morphism
  val reset_context: morphism -> morphism
  val morphism: string ->
   {binding: (theory option -> binding -> binding) list,
    typ: (theory option -> typ -> typ) list,
    term: (theory option -> term -> term) list,
    fact: (theory option -> thm list -> thm list) list} -> morphism
  val is_identity: morphism -> bool
  val is_empty: morphism -> bool
  val pretty: morphism -> Pretty.T
  val binding: morphism -> binding -> binding
  val binding_prefix: morphism -> (string * bool) list
  val typ: morphism -> typ -> typ
  val term: morphism -> term -> term
  val fact: morphism -> thm list -> thm list
  val thm: morphism -> thm -> thm
  val cterm: morphism -> cterm -> cterm
  val identity: morphism
  val default: morphism option -> morphism
  val compose: morphism -> morphism -> morphism
  type 'a entity
  val entity: (morphism -> 'a) -> 'a entity
  val entity_reset_context: 'a entity -> 'a entity
  val entity_set_context: theory -> 'a entity -> 'a entity
  val entity_set_context': Proof.context -> 'a entity -> 'a entity
  val entity_set_context'': Context.generic -> 'a entity -> 'a entity
  val transform: morphism -> 'a entity -> 'a entity
  val transform_reset_context: morphism -> 'a entity -> 'a entity
  val form: 'a entity -> 'a
  val form_entity: (morphism -> 'a) -> 'a
  val form_context: theory -> (theory -> 'a) entity -> 'a
  val form_context': Proof.context -> (Proof.context -> 'a) entity -> 'a
  val form_context'': Context.generic -> (Context.generic -> 'a) entity -> 'a
  type declaration = morphism -> Context.generic -> Context.generic
  type declaration_entity = (Context.generic -> Context.generic) entity
  val binding_morphism: string -> (binding -> binding) -> morphism
  val typ_morphism': string -> (theory -> typ -> typ) -> morphism
  val typ_morphism: string -> (typ -> typ) -> morphism
  val term_morphism': string -> (theory -> term -> term) -> morphism
  val term_morphism: string -> (term -> term) -> morphism
  val fact_morphism': string -> (theory -> thm list -> thm list) -> morphism
  val fact_morphism: string -> (thm list -> thm list) -> morphism
  val thm_morphism': string -> (theory -> thm -> thm) -> morphism
  val thm_morphism: string -> (thm -> thm) -> morphism
  val transfer_morphism: theory -> morphism
  val transfer_morphism': Proof.context -> morphism
  val transfer_morphism'': Context.generic -> morphism
  val trim_context_morphism: morphism
  val set_trim_context: theory -> morphism -> morphism
  val set_trim_context': Proof.context -> morphism -> morphism
  val set_trim_context'': Context.generic -> morphism -> morphism
  val instantiate_frees_morphism: ctyp TFrees.table * cterm Frees.table -> morphism
  val instantiate_morphism: ctyp TVars.table * cterm Vars.table -> morphism
end;

structure Morphism: MORPHISM =
struct

(* named functions *)

type 'a funs = (string * (theory option -> 'a -> 'a)) list;

exception MORPHISM of string * exn;

fun app context (name, f) x =
  Isabelle_Thread.try_catch (fn () => f context x)
    (fn exn => raise MORPHISM (name, exn));


(* optional context *)

fun the_theory (SOME thy) = thy
  | the_theory NONE = raise Fail "Morphism lacks theory context";

fun join_transfer (SOME thy) = Thm.join_transfer thy
  | join_transfer NONE = I;

val join_context = join_options Context.join_certificate_theory;


(* type morphism *)

datatype morphism = Morphism of
 {context: theory option,
  names: string list,
  binding: binding funs,
  typ: typ funs,
  term: term funs,
  fact: thm list funs};

fun rep (Morphism args) = args;

fun apply which phi =
  let val args = rep phi
  in fold_rev (app (#context args)) (which args) end;

fun put_context context (Morphism {context = _, names, binding, typ, term, fact}) =
  Morphism {context = context, names = names, binding = binding, typ = typ, term = term, fact = fact};

val set_context = put_context o SOME;
val set_context' = set_context o Proof_Context.theory_of;
val set_context'' = set_context o Context.theory_of;
val reset_context = put_context NONE;

fun morphism a {binding, typ, term, fact} =
  Morphism {
    context = NONE,
    names = if a = "" then [] else [a],
    binding = map (pair a) binding,
    typ = map (pair a) typ,
    term = map (pair a) term,
    fact = map (pair a) fact};

(*syntactic test only!*)
fun is_identity (Morphism {context = _, names, binding, typ, term, fact}) =
  null names andalso null binding andalso null typ andalso null term andalso null fact;

fun is_empty phi = is_none (#context (rep phi)) andalso is_identity phi;

fun pretty phi = Pretty.enum ";" "{" "}" (map Pretty.str (rev (#names (rep phi))));

val _ = ML_system_pp (fn _ => fn _ => Pretty.to_ML o pretty);

val binding = apply #binding;
fun binding_prefix morph = Binding.name "x" |> binding morph |> Binding.prefix_of;
val typ = apply #typ;
val term = apply #term;
fun fact phi = map (join_transfer (#context (rep phi))) #> apply #fact phi;
val thm = singleton o fact;
val cterm = Drule.cterm_rule o thm;


(* morphism combinators *)

val identity = morphism "" {binding = [], typ = [], term = [], fact = []};

val default = the_default identity;

fun compose phi1 phi2 =
  if is_empty phi1 then phi2
  else if is_empty phi2 then phi1
  else
    let
      val {context = context1, names = names1, binding = binding1,
        typ = typ1, term = term1, fact = fact1} = rep phi1;
      val {context = context2, names = names2, binding = binding2,
        typ = typ2, term = term2, fact = fact2} = rep phi2;
    in
      Morphism {
        context = join_context (context1, context2),
        names = names1 @ names2,
        binding = binding1 @ binding2,
        typ = typ1 @ typ2,
        term = term1 @ term2,
        fact = fact1 @ fact2}
    end;

fun phi1 $> phi2 = compose phi2 phi1;


(* abstract entities *)

datatype 'a entity = Entity of (morphism -> 'a) * morphism;
fun entity f = Entity (f, identity);

fun entity_morphism g (Entity (f, phi)) = Entity (f, g phi);
fun entity_reset_context a = entity_morphism reset_context a;
fun entity_set_context thy a = entity_morphism (set_context thy) a;
fun entity_set_context' ctxt a = entity_morphism (set_context' ctxt) a;
fun entity_set_context'' context a = entity_morphism (set_context'' context) a;

fun transform phi = entity_morphism (compose phi);
fun transform_reset_context phi = entity_morphism (reset_context o compose phi);

fun form (Entity (f, phi)) = f phi;
fun form_entity f = f identity;

fun form_context thy x = form (entity_set_context thy x) thy;
fun form_context' ctxt x = form (entity_set_context' ctxt x) ctxt;
fun form_context'' context x = form (entity_set_context'' context x) context;

type declaration = morphism -> Context.generic -> Context.generic;
type declaration_entity = (Context.generic -> Context.generic) entity;


(* concrete morphisms *)

fun binding_morphism a binding = morphism a {binding = [K binding], typ = [], term = [], fact = []};
fun typ_morphism' a typ = morphism a {binding = [], typ = [typ o the_theory], term = [], fact = []};
fun typ_morphism a typ = morphism a {binding = [], typ = [K typ], term = [], fact = []};
fun term_morphism' a term = morphism a {binding = [], typ = [], term = [term o the_theory], fact = []};
fun term_morphism a term = morphism a {binding = [], typ = [], term = [K term], fact = []};
fun fact_morphism' a fact = morphism a {binding = [], typ = [], term = [], fact = [fact o the_theory]};
fun fact_morphism a fact = morphism a {binding = [], typ = [], term = [], fact = [K fact]};
fun thm_morphism' a thm = morphism a {binding = [], typ = [], term = [], fact = [map o thm o the_theory]};
fun thm_morphism a thm = morphism a {binding = [], typ = [], term = [], fact = [K (map thm)]};

fun transfer_morphism thy = fact_morphism "transfer" I |> set_context thy;
val transfer_morphism' = transfer_morphism o Proof_Context.theory_of;
val transfer_morphism'' = transfer_morphism o Context.theory_of;

val trim_context_morphism = thm_morphism "trim_context" Thm.trim_context;

fun set_trim_context thy phi = set_context thy phi $> trim_context_morphism;
val set_trim_context' = set_trim_context o Proof_Context.theory_of;
val set_trim_context'' = set_trim_context o Context.theory_of;


(* instantiate *)

fun instantiate_frees_morphism (cinstT, cinst) =
  if TFrees.is_empty cinstT andalso Frees.is_empty cinst then identity
  else
    let
      val instT = TFrees.map (K Thm.typ_of) cinstT;
      val inst = Frees.map (K Thm.term_of) cinst;
    in
      morphism "instantiate_frees"
        {binding = [],
         typ =
          if TFrees.is_empty instT then []
          else [K (Term_Subst.instantiateT_frees instT)],
         term = [K (Term_Subst.instantiate_frees (instT, inst))],
         fact = [K (map (Thm.instantiate_frees (cinstT, cinst)))]}
    end;

fun instantiate_morphism (cinstT, cinst) =
  if TVars.is_empty cinstT andalso Vars.is_empty cinst then identity
  else
    let
      val instT = TVars.map (K Thm.typ_of) cinstT;
      val inst = Vars.map (K Thm.term_of) cinst;
    in
      morphism "instantiate"
        {binding = [],
         typ =
          if TVars.is_empty instT then []
          else [K (Term_Subst.instantiateT instT)],
         term = [K (Term_Subst.instantiate (instT, inst))],
         fact = [K (map (Thm.instantiate (cinstT, cinst)))]}
    end;

end;

structure Basic_Morphism: BASIC_MORPHISM = Morphism;
open Basic_Morphism;
