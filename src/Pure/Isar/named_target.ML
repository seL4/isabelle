(*  Title:      Pure/Isar/named_target.ML
    Author:     Makarius
    Author:     Florian Haftmann, TU Muenchen

Targets for theory, locale, class -- at the bottom the nested structure.
*)

signature NAMED_TARGET =
sig
  val is_theory: local_theory -> bool
  val locale_of: local_theory -> string option
  val bottom_locale_of: local_theory -> string option
  val class_of: local_theory -> string option
  val init: string -> theory -> local_theory
  val init': {setup: local_theory -> local_theory, conclude: local_theory -> local_theory} ->
    string -> theory -> local_theory
  val theory_init: theory -> local_theory
  val theory_map: (local_theory -> local_theory) -> theory -> theory
  val begin: xstring * Position.T -> theory -> local_theory
  val exit: local_theory -> theory
  val switch: (xstring * Position.T) option -> Context.generic ->
    (local_theory -> Context.generic) * local_theory
end;

structure Named_Target: NAMED_TARGET =
struct

(* context data *)

datatype target = Theory | Locale of string | Class of string;

fun ident_of_target Theory = ""
  | ident_of_target (Locale locale) = locale
  | ident_of_target (Class class) = class;

fun target_is_theory (SOME Theory) = true
  | target_is_theory _ = false;

fun locale_of_target (SOME (Locale locale)) = SOME locale
  | locale_of_target (SOME (Class locale)) = SOME locale
  | locale_of_target _ = NONE;

fun class_of_target (SOME (Class class)) = SOME class
  | class_of_target _ = NONE;

structure Data = Proof_Data
(
  type T = target option;
  fun init _ = NONE;
);

val get_bottom_target = Data.get;

fun get_target lthy =
  if Local_Theory.level lthy = 1
  then get_bottom_target lthy
  else NONE;

fun ident_of lthy =
  case get_target lthy of
    NONE => error "Not in a named target"
  | SOME target => ident_of_target target;

val is_theory = target_is_theory o get_target;

val locale_of = locale_of_target o get_target;

val bottom_locale_of = locale_of_target o get_bottom_target;

val class_of = class_of_target o get_target;


(* operations *)

fun locale_foundation locale (((b, U), mx), (b_def, rhs)) params =
  Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => Generic_Target.locale_const locale Syntax.mode_default ((b, mx), lhs)
    #> pair (lhs, def));

fun class_foundation class (((b, U), mx), (b_def, rhs)) params =
  Generic_Target.background_foundation (((b, U), NoSyn), (b_def, rhs)) params
  #-> (fn (lhs, def) => Class.const class ((b, mx), lhs) params
    #> pair (lhs, def));

fun foundation Theory = Generic_Target.theory_target_foundation
  | foundation (Locale locale) = locale_foundation locale
  | foundation (Class class) = class_foundation class;

fun notes Theory = Generic_Target.theory_target_notes
  | notes (Locale locale) = Generic_Target.locale_target_notes locale
  | notes (Class class) = Generic_Target.locale_target_notes class;

fun abbrev Theory = Generic_Target.theory_abbrev
  | abbrev (Locale locale) = Generic_Target.locale_abbrev locale
  | abbrev (Class class) = Class.abbrev class;

fun declaration Theory _ decl = Generic_Target.theory_declaration decl
  | declaration (Locale locale) flags decl = Generic_Target.locale_declaration locale flags decl
  | declaration (Class class) flags decl = Generic_Target.locale_declaration class flags decl;

fun theory_registration Theory = Generic_Target.theory_registration
  | theory_registration _ = (fn _ => error "Not possible in theory target");

fun locale_dependency Theory = (fn _ => error "Not possible in theory target")
  | locale_dependency (Locale locale) = Generic_Target.locale_dependency locale
  | locale_dependency (Class class) = Generic_Target.locale_dependency class;

fun pretty Theory ctxt =
      [Pretty.block [Pretty.keyword1 "theory", Pretty.brk 1,
        Pretty.str (Context.theory_name (Proof_Context.theory_of ctxt))]]
  | pretty (Locale locale) ctxt = Locale.pretty_locale (Proof_Context.theory_of ctxt) false locale
  | pretty (Class class) ctxt =
      Class.pretty_specification (Proof_Context.theory_of ctxt) class;


(* init *)

fun make_target _ "" = Theory
  | make_target thy ident =
      if Locale.defined thy ident
      then (if Class.is_class thy ident then Class else Locale) ident
      else error ("No such locale: " ^ quote ident);

fun init_context Theory = Proof_Context.init_global
  | init_context (Locale locale) = Locale.init locale
  | init_context (Class class) = Class.init class;

fun init' {setup, conclude} ident thy =
  let
    val target = make_target thy ident;
    val background_naming =
      Sign.naming_of thy |> Name_Space.mandatory_path (Long_Name.base_name ident);
  in
    thy
    |> Sign.change_begin
    |> init_context target
    |> setup
    |> Local_Theory.init background_naming
       {define = Generic_Target.define (foundation target),
        notes = Generic_Target.notes (notes target),
        abbrev = abbrev target,
        declaration = declaration target,
        theory_registration = theory_registration target,
        locale_dependency = locale_dependency target,
        pretty = pretty target,
        exit = conclude #> Local_Theory.target_of #> Sign.change_end_local}
  end;

fun init ident thy =
  init' {setup = Data.put (SOME (make_target thy ident)), conclude = I} ident thy;

val theory_init = init "";

fun theory_map f = theory_init #> f #> Local_Theory.exit_global;


(* toplevel interaction *)

fun begin ("-", _) thy = theory_init thy
  | begin target thy = init (Locale.check thy target) thy;

val exit = Local_Theory.assert_bottom #> Local_Theory.exit_global;

fun switch NONE (Context.Theory thy) =
      (Context.Theory o exit, theory_init thy)
  | switch (SOME name) (Context.Theory thy) =
      (Context.Theory o exit, begin name thy)
  | switch NONE (Context.Proof lthy) =
      (Context.Proof o Local_Theory.reset, lthy)
  | switch (SOME name) (Context.Proof lthy) =
      (Context.Proof o init (ident_of lthy) o exit,
        (begin name o exit o Local_Theory.assert_nonbrittle) lthy);

end;
