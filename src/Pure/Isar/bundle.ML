(*  Title:      Pure/Isar/bundle.ML
    Author:     Makarius

Bundled declarations (notes etc.).
*)

signature BUNDLE =
sig
  type bundle = (thm list * Args.src list) list
  val the_bundle: Proof.context -> string -> bundle
  val check: Proof.context -> xstring * Position.T -> string
  val bundle: binding * (thm list * Args.src list) list ->
    (binding * typ option * mixfix) list -> local_theory -> local_theory
  val bundle_cmd: binding * (Facts.ref * Args.src list) list ->
    (binding * string option * mixfix) list -> local_theory -> local_theory
  val include_: string -> Proof.state -> Proof.state
  val include_cmd: xstring * Position.T -> Proof.state -> Proof.state
  val including: string -> Proof.state -> Proof.state
  val including_cmd: xstring * Position.T -> Proof.state -> Proof.state
  val print_bundles: Proof.context -> unit
end;

structure Bundle: BUNDLE =
struct

(* maintain bundles *)

type bundle = (thm list * Args.src list) list;

fun transform_bundle phi : bundle -> bundle =
  map (fn (fact, atts) => (Morphism.fact phi fact, map (Args.transform_values phi) atts));

structure Data = Generic_Data
(
  type T = bundle Name_Space.table;
  val empty : T = Name_Space.empty_table "bundle";
  val extend = I;
  val merge = Name_Space.merge_tables;
);

val get_bundles = Data.get o Context.Proof;

fun the_bundle ctxt name =
  (case Symtab.lookup (#2 (get_bundles ctxt)) name of
    SOME bundle => bundle
  | NONE => error ("Unknown bundle " ^ quote name));

fun check ctxt = #1 o Name_Space.check (Context.Proof ctxt) (get_bundles ctxt);


(* define bundle *)

local

fun gen_bundle prep_fact prep_att prep_vars (binding, raw_bundle) fixes lthy =
  let
    val (_, ctxt') = lthy |> prep_vars fixes |-> Proof_Context.add_fixes;
    val bundle0 = raw_bundle
      |> map (fn (fact, atts) => (prep_fact lthy fact, map (prep_att lthy) atts));
    val bundle =
      Attrib.partial_evaluation ctxt' [(Attrib.empty_binding, bundle0)] |> map snd |> flat
      |> transform_bundle (Proof_Context.export_morphism ctxt' lthy);
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true}
      (fn phi => fn context =>
        context |> Data.map
          (#2 o Name_Space.define context true
            (Morphism.binding phi binding, transform_bundle phi bundle)))
  end;

in

val bundle = gen_bundle (K I) (K I) Proof_Context.cert_vars;
val bundle_cmd =
  gen_bundle Proof_Context.get_fact (Attrib.intern_src o Proof_Context.theory_of)
    Proof_Context.read_vars;

end;


(* include bundle *)

fun gen_include prep raw_name =
  Proof.map_context (fn ctxt =>
    let
      val bundle = the_bundle ctxt (prep ctxt raw_name);
      val attrib = Attrib.attribute_i (Proof_Context.theory_of ctxt);
      val note = ((Binding.empty, []), map (apsnd (map attrib)) bundle);
    in #2 (Proof_Context.note_thmss "" [note] ctxt) end);

fun include_ name = Proof.assert_forward #> gen_include (K I) name #> Proof.put_facts NONE;
fun include_cmd name = Proof.assert_forward #> gen_include check name #> Proof.put_facts NONE;
fun including name = Proof.assert_backward #> gen_include (K I) name;
fun including_cmd name = Proof.assert_backward #> gen_include check name;


(* print_bundles *)

fun print_bundles ctxt =
  let
    val prt_thm = Pretty.backquote o Display.pretty_thm ctxt;

    fun prt_fact (ths, []) = map prt_thm ths
      | prt_fact (ths, atts) = Pretty.enclose "(" ")"
          (Pretty.breaks (map prt_thm ths)) :: Attrib.pretty_attribs ctxt atts;

    fun prt_bundle (name, bundle) =
      Pretty.block (Pretty.command "bundle" :: Pretty.str " " :: Pretty.str name ::
        Pretty.breaks (Pretty.str " =" :: maps prt_fact bundle));
  in
    map prt_bundle (Name_Space.extern_table ctxt (get_bundles ctxt))
  end |> Pretty.chunks |> Pretty.writeln;

end;

