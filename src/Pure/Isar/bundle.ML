(*  Title:      Pure/Isar/bundle.ML
    Author:     Makarius

Bundled declarations (notes etc.).
*)

signature BUNDLE =
sig
  type name = string
  val bundle_space: Context.generic -> Name_Space.T
  val check: Proof.context -> xstring * Position.T -> string
  val get: Proof.context -> name -> Attrib.thms
  val read: Proof.context -> xstring * Position.T -> Attrib.thms
  val extern: Proof.context -> string -> xstring
  val print_bundles: bool -> Proof.context -> unit
  val unbundle: name list -> local_theory -> local_theory
  val unbundle_cmd: (xstring * Position.T) list -> local_theory -> local_theory
  val includes: name list -> Proof.context -> Proof.context
  val includes_cmd: (xstring * Position.T) list -> Proof.context -> Proof.context
  val include_: name list -> Proof.state -> Proof.state
  val include_cmd: (xstring * Position.T) list -> Proof.state -> Proof.state
  val including: name list -> Proof.state -> Proof.state
  val including_cmd: (xstring * Position.T) list -> Proof.state -> Proof.state
  val bundle: binding * Attrib.thms ->
    (binding * typ option * mixfix) list -> local_theory -> local_theory
  val bundle_cmd: binding * (Facts.ref * Token.src list) list ->
    (binding * string option * mixfix) list -> local_theory -> local_theory
  val init: binding -> theory -> local_theory
end;

structure Bundle: BUNDLE =
struct

(** context data **)

structure Data = Generic_Data
(
  type T = Attrib.thms Name_Space.table * Attrib.thms option;
  val empty : T = (Name_Space.empty_table Markup.bundleN, NONE);
  fun merge ((tab1, target1), (tab2, target2)) =
    (Name_Space.merge_tables (tab1, tab2), merge_options (target1, target2));
);


(* bundles *)

type name = string

val get_all_generic = #1 o Data.get;
val get_all = get_all_generic o Context.Proof;

val bundle_space = Name_Space.space_of_table o #1 o Data.get;

fun check ctxt = #1 o Name_Space.check (Context.Proof ctxt) (get_all ctxt);

val get = Name_Space.get o get_all_generic o Context.Proof;

fun read ctxt = get ctxt o check ctxt;

fun extern ctxt = Name_Space.extern ctxt (Name_Space.space_of_table (get_all ctxt));


(* context and morphisms *)

val trim_context_bundle =
  map (fn (fact, atts) => (map Thm.trim_context fact, (map o map) Token.trim_context atts));

fun transfer_bundle thy =
  map (fn (fact, atts) => (map (Thm.transfer thy) fact, (map o map) (Token.transfer thy) atts));

fun transform_bundle phi =
  map (fn (fact, atts) => (Morphism.fact phi fact, (map o map) (Token.transform phi) atts));



(* target -- bundle under construction *)

fun the_target thy =
  #2 (Data.get (Context.Theory thy))
  |> \<^if_none>\<open>error "Missing bundle target"\<close>;

val reset_target = (Context.theory_map o Data.map o apsnd o K) NONE;
val set_target = Context.theory_map o Data.map o apsnd o K o SOME o Attrib.trim_context_thms;

fun augment_target thms =
  Local_Theory.background_theory (fn thy => set_target (the_target thy @ thms) thy);


(* print bundles *)

fun pretty_bundle ctxt (markup_name, bundle) =
  let
    val prt_thm = Pretty.cartouche o Thm.pretty_thm ctxt;
    fun prt_thm_attribs atts th =
      Pretty.block (Pretty.breaks (prt_thm th :: Attrib.pretty_attribs ctxt atts));
    fun prt_thms (ths, []) = map prt_thm ths
      | prt_thms (ths, atts) = map (prt_thm_attribs atts) ths;
  in
    Pretty.block ([Pretty.keyword1 "bundle", Pretty.str " ", Pretty.mark_str markup_name] @
      (if null bundle then [] else Pretty.fbreaks (Pretty.str " =" :: maps prt_thms bundle)))
  end;

fun print_bundles verbose ctxt =
  Pretty.writeln_chunks
    (map (pretty_bundle ctxt) (Name_Space.markup_table verbose ctxt (get_all ctxt)));



(** open bundles **)

fun apply_bundle loc bundle ctxt =
  let val notes = if loc then Local_Theory.notes else Attrib.local_notes "" in
    ctxt
    |> Context_Position.set_visible false
    |> notes [(Binding.empty_atts, bundle)] |> snd
    |> Context_Position.restore_visible ctxt
  end;

local

fun gen_unbundle loc prep args ctxt =
  let
    val thy = Proof_Context.theory_of ctxt;
    val bundle = maps (prep ctxt) args |> transfer_bundle thy;
  in apply_bundle loc bundle ctxt end;

fun gen_includes prep = gen_unbundle false prep;

fun gen_include prep bs =
  Proof.assert_forward #> Proof.map_context (gen_includes prep bs) #> Proof.reset_facts;

fun gen_including prep bs =
  Proof.assert_backward #> Proof.map_context (gen_includes prep bs);

in

val unbundle = gen_unbundle true get;
val unbundle_cmd = gen_unbundle true read;

val includes = gen_includes get;
val includes_cmd = gen_includes read;

val include_ = gen_include get;
val include_cmd = gen_include read;

val including = gen_including get;
val including_cmd = gen_including read;

end;



(** define bundle **)

fun define_bundle (b, bundle) context =
  let
    val (name, bundles') = get_all_generic context
      |> Name_Space.define context true (b, trim_context_bundle bundle);
    val context' = (Data.map o apfst o K) bundles' context;
  in (name, context') end;


(* command *)

local

fun gen_bundle prep_fact prep_att add_fixes (binding, raw_bundle) raw_fixes lthy =
  let
    val (_, ctxt') = add_fixes raw_fixes lthy;
    val bundle0 = raw_bundle
      |> map (fn (fact, atts) => (prep_fact ctxt' fact, map (prep_att ctxt') atts));
    val bundle =
      Attrib.partial_evaluation ctxt' [(Binding.empty_atts, bundle0)]
      |> maps #2
      |> transform_bundle (Proof_Context.export_morphism ctxt' lthy)
      |> trim_context_bundle;
  in
    lthy |> Local_Theory.declaration {syntax = false, pervasive = true, pos = Binding.pos_of binding}
      (fn phi => fn context =>
        let val psi = Morphism.set_trim_context'' context phi
        in #2 (define_bundle (Morphism.binding psi binding, transform_bundle psi bundle) context) end)
  end;

in

val bundle = gen_bundle (K I) (K I) Proof_Context.add_fixes;
val bundle_cmd = gen_bundle Proof_Context.get_fact Attrib.check_src Proof_Context.add_fixes_cmd;

end;


(* target *)

local

fun bad_operation _ = error "Not possible in bundle target";

fun conclude invisible binding =
  Local_Theory.background_theory_result (fn thy =>
    thy
    |> invisible ? Context_Position.set_visible_global false
    |> Context.Theory
    |> define_bundle (binding, the_target thy)
    ||> (Context.the_theory
      #> invisible ? Context_Position.restore_visible_global thy
      #> reset_target));

fun pretty binding lthy =
  let
    val bundle = the_target (Proof_Context.theory_of lthy);
    val (name, lthy') = lthy
      |> Local_Theory.raw_theory (Context_Position.set_visible_global false)
      |> conclude true binding;
    val thy_ctxt' = Proof_Context.init_global (Proof_Context.theory_of lthy');
    val markup_name =
      Name_Space.markup_extern thy_ctxt' (Name_Space.space_of_table (get_all thy_ctxt')) name;
  in [pretty_bundle lthy' (markup_name, bundle)] end;

fun bundle_notes kind facts lthy =
  let
    val bundle = facts
      |> maps (fn ((_, more_atts), thms) => map (fn (ths, atts) => (ths, atts @ more_atts)) thms);
  in
    lthy
    |> augment_target (transform_bundle (Local_Theory.standard_morphism_theory lthy) bundle)
    |> Generic_Target.standard_notes (op <>) kind facts
    |> Attrib.local_notes kind facts
  end;

fun bundle_declaration pos decl lthy =
  lthy
  |> (augment_target o Attrib.internal_declaration pos)
    (Morphism.transform (Local_Theory.standard_morphism_theory lthy) decl)
  |> Generic_Target.standard_declaration (K true) decl;

in

fun init binding thy =
  thy
  |> Local_Theory.init
     {background_naming = Sign.naming_of thy,
      setup = set_target [] #> Proof_Context.init_global,
      conclude = conclude false binding #> #2}
     {define = bad_operation,
      notes = bundle_notes,
      abbrev = bad_operation,
      declaration = fn {pos, ...} => bundle_declaration pos,
      theory_registration = bad_operation,
      locale_dependency = bad_operation,
      pretty = pretty binding};

end;

end;
