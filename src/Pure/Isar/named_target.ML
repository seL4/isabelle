(*  Title:      Pure/Isar/named_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Targets for theory, locale, class -- at the bottom the nested structure.
*)

signature NAMED_TARGET =
sig
  val is_theory: local_theory -> bool
  val locale_of: local_theory -> string option
  val class_of: local_theory -> string option
  val init: string -> theory -> local_theory
  val theory_init: theory -> local_theory
  val context_cmd: xstring * Position.T -> theory -> local_theory
end;

structure Named_Target: NAMED_TARGET =
struct

(* context data *)

datatype target =
  Target of {target: string, is_locale: bool, is_class: bool};

fun make_target target is_locale is_class =
  Target {target = target, is_locale = is_locale, is_class = is_class};

fun named_target _ "" = make_target "" false false
  | named_target thy target =
      if Locale.defined thy target
      then make_target target true (Class.is_class thy target)
      else error ("No such locale: " ^ quote target);

structure Data = Proof_Data
(
  type T = target option;
  fun init _ = NONE;
);

fun peek lthy =
  if Local_Theory.level lthy = 1
  then Option.map (fn Target ta => ta) (Data.get lthy)
  else NONE;

fun is_theory lthy =
  case peek lthy of
    SOME {target = "", ...} => true
  | _ => false;

fun locale_of lthy =
  case peek lthy of
    SOME {target = locale, is_locale = true, ...} => SOME locale
  | _ => NONE;

fun class_of lthy =
  case peek lthy of
    SOME {target = class, is_class = true, ...} => SOME class
  | _ => NONE;


(* define *)

fun locale_foundation locale (((b, U), mx), (b_def, rhs)) params =
  Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => Generic_Target.locale_const locale Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def));

fun class_foundation class (((b, U), mx), (b_def, rhs)) params =
  Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => Class.const class ((b, mx), lhs) params
    #> pair (lhs, def));

fun foundation (ta as Target {target, is_locale, is_class, ...}) =
  if is_class then class_foundation target
  else if is_locale then locale_foundation target
  else Generic_Target.theory_foundation;


(* notes *)

fun notes (Target {target, is_locale, ...}) =
  if is_locale then Generic_Target.locale_notes target
  else Generic_Target.theory_notes;


(* abbrev *)

fun locale_abbrev locale prmode (b, mx) global_rhs params =
  Generic_Target.background_abbrev (b, global_rhs) (snd params)
  #-> (fn (lhs, _) => Generic_Target.locale_const locale prmode ((b, mx), lhs));

fun class_abbrev class prmode (b, mx) global_rhs params =
  Generic_Target.background_abbrev (b, global_rhs) (snd params)
  #-> (fn (lhs, rhs) => Class.abbrev class prmode ((b, mx), lhs) rhs params);

fun abbrev (ta as Target {target, is_locale, is_class, ...}) =
  if is_class then class_abbrev target
  else if is_locale then locale_abbrev target
  else Generic_Target.theory_abbrev;


(* declaration *)

fun declaration (Target {target, is_locale, ...}) {syntax, pervasive} decl =
  if is_locale then
    pervasive ? Generic_Target.background_declaration decl
    #> Generic_Target.locale_declaration target syntax decl
    #> Generic_Target.standard_declaration (fn (_, other) => other <> 0) decl
  else Generic_Target.theory_declaration decl;


(* subscription *)

fun subscription (Target {target, is_locale, ...}) =
  if is_locale then Generic_Target.locale_dependency target
  else Generic_Target.theory_registration;


(* pretty *)

fun pretty (Target {target, is_locale, is_class, ...}) ctxt =
  let
    val target_name =
      [Pretty.keyword1 (if is_class then "class" else "locale"), Pretty.brk 1,
        Locale.pretty_name ctxt target];
    val fixes =
      map (fn (x, T) => (Binding.name x, SOME T, NoSyn))
        (#1 (Proof_Context.inferred_fixes ctxt));
    val assumes =
      map (fn A => (Attrib.empty_binding, [(Thm.term_of A, [])]))
        (Assumption.all_assms_of ctxt);
    val elems =
      (if null fixes then [] else [Element.Fixes fixes]) @
      (if null assumes then [] else [Element.Assumes assumes]);
    val body_elems =
      if not is_locale then []
      else if null elems then [Pretty.block target_name]
      else [Pretty.block (Pretty.fbreaks (Pretty.block (target_name @ [Pretty.str " ="]) ::
        map (Pretty.chunks o Element.pretty_ctxt ctxt) elems))];
  in
    Pretty.block [Pretty.keyword1 "theory", Pretty.brk 1,
      Pretty.str (Context.theory_name (Proof_Context.theory_of ctxt))] :: body_elems
  end;


(* init *)

fun init_context (Target {target, is_locale, is_class, ...}) =
  if not is_locale then Proof_Context.init_global
  else if not is_class then Locale.init target
  else Class.init target;

fun init target thy =
  let
    val ta = named_target thy target;
    val naming = Sign.naming_of thy
      |> Name_Space.mandatory_path (Long_Name.base_name target);
  in
    thy
    |> Sign.change_begin
    |> init_context ta
    |> Data.put (SOME ta)
    |> Local_Theory.init naming
       {define = Generic_Target.define (foundation ta),
        notes = Generic_Target.notes (notes ta),
        abbrev = Generic_Target.abbrev (abbrev ta),
        declaration = declaration ta,
        subscription = subscription ta,
        pretty = pretty ta,
        exit = Local_Theory.target_of #> Sign.change_end_local}
  end;

val theory_init = init "";

fun context_cmd ("-", _) thy = theory_init thy
  | context_cmd target thy = init (Locale.check thy target) thy;

end;
