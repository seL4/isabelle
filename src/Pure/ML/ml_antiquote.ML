(*  Title:      Pure/ML/ml_antiquote.ML
    Author:     Makarius

Common ML antiquotations.
*)

signature ML_ANTIQUOTE =
sig
  val macro: string -> Proof.context context_parser -> unit
  val variant: string -> Proof.context -> string * Proof.context
  val inline: string -> string context_parser -> unit
  val declaration: string -> string -> string context_parser -> unit
  val value: string -> string context_parser -> unit
end;

structure ML_Antiquote: ML_ANTIQUOTE =
struct

(** generic tools **)

(* ML names *)

structure NamesData = Proof_Data
(
  type T = Name.context;
  fun init _ = ML_Syntax.reserved;
);

fun variant a ctxt =
  let
    val names = NamesData.get ctxt;
    val ([b], names') = Name.variants [a] names;
    val ctxt' = NamesData.put names' ctxt;
  in (b, ctxt') end;


(* specific antiquotations *)

fun macro name scan = ML_Context.add_antiq name
  (fn _ => scan :|-- (fn ctxt => Scan.depend (fn _ => Scan.succeed
    (Context.Proof ctxt, fn background => (K ("", ""), background)))));

fun inline name scan = ML_Context.add_antiq name
  (fn _ => scan >> (fn s => fn background => (K ("", s), background)));

fun declaration kind name scan = ML_Context.add_antiq name
  (fn _ => scan >> (fn s => fn background =>
    let
      val (a, background') = variant name background;
      val env = kind ^ " " ^ a ^ " = " ^ s ^ ";\n";
      val body = "Isabelle." ^ a;
    in (K (env, body), background') end));

val value = declaration "val";



(** misc antiquotations **)

structure P = OuterParse;

val _ = value "binding"
  (Scan.lift (P.position Args.name) >> (fn name => ML_Syntax.atomic (ML_Syntax.make_binding name)));

val _ = value "theory"
  (Scan.lift Args.name >> (fn name => "ThyInfo.get_theory " ^ ML_Syntax.print_string name)
  || Scan.succeed "ML_Context.the_global_context ()");

val _ = value "theory_ref"
  (Scan.lift Args.name >> (fn name =>
    "Theory.check_thy (ThyInfo.theory " ^ ML_Syntax.print_string name ^ ")")
  || Scan.succeed "Theory.check_thy (ML_Context.the_global_context ())");

val _ = value "context" (Scan.succeed "ML_Context.the_local_context ()");

val _ = inline "typ" (Args.typ >> (ML_Syntax.atomic o ML_Syntax.print_typ));
val _ = inline "term" (Args.term >> (ML_Syntax.atomic o ML_Syntax.print_term));
val _ = inline "prop" (Args.prop >> (ML_Syntax.atomic o ML_Syntax.print_term));

val _ = macro "let" (Args.context --
  Scan.lift (P.and_list1 (P.and_list1 Args.name_source -- (Args.$$$ "=" |-- Args.name_source)))
    >> (fn (ctxt, args) => #2 (ProofContext.match_bind true args ctxt)));

val _ = macro "note" (Args.context :|-- (fn ctxt =>
  P.and_list1' (Scan.lift (Args.opt_thm_name I "=") -- Attrib.thms >> (fn ((a, srcs), ths) =>
    ((a, map (Attrib.attribute (ProofContext.theory_of ctxt)) srcs), [(ths, [])])))
  >> (fn args => #2 (ProofContext.note_thmss "" args ctxt))));

val _ = value "ctyp" (Args.typ >> (fn T =>
  "Thm.ctyp_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_typ T)));

val _ = value "cterm" (Args.term >> (fn t =>
  "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t)));

val _ = value "cprop" (Args.prop >> (fn t =>
  "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t)));

val _ = value "cpat"
  (Args.context -- Scan.lift Args.name_source >> uncurry ProofContext.read_term_pattern >> (fn t =>
    "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t)));


(* type classes *)

fun class syn = Args.theory -- Scan.lift Args.name_source >> (fn (thy, s) =>
  Sign.read_class thy s
  |> syn ? Long_Name.base_name   (* FIXME authentic syntax *)
  |> ML_Syntax.print_string);

val _ = inline "class" (class false);
val _ = inline "class_syntax" (class true);

val _ = inline "sort" (Args.context -- Scan.lift Args.name_source >> (fn (ctxt, s) =>
  ML_Syntax.atomic (ML_Syntax.print_sort (Syntax.read_sort ctxt s))));


(* type constructors *)

fun type_const kind check = Args.context -- Scan.lift Args.name_source >> (fn (ctxt, c) =>
  let
    val d = #1 (Term.dest_Type (ProofContext.read_type_name ctxt false c));
    val decl = Sign.the_type_decl (ProofContext.theory_of ctxt) d;
    val s =
      (case try check (d, decl) of
        SOME s => s
      | NONE => error ("Not a " ^ kind ^ ": " ^ quote d));
  in ML_Syntax.print_string s end);

val _ = inline "type_name" (type_const "logical type" (fn (d, Type.LogicalType _) => d));
val _ = inline "type_abbrev" (type_const "type abbreviation" (fn (d, Type.Abbreviation _) => d));
val _ = inline "nonterminal" (type_const "nonterminal" (fn (d, Type.Nonterminal) => d));
val _ = inline "type_syntax" (type_const "type" (fn (d, _) => Long_Name.base_name d));  (* FIXME authentic syntax *)


(* constants *)

fun const syn = Args.context -- Scan.lift Args.name_source >> (fn (ctxt, c) =>
  #1 (Term.dest_Const (ProofContext.read_const_proper ctxt c))
  |> syn ? Syntax.mark_const
  |> ML_Syntax.print_string);

val _ = inline "const_name" (const false);
val _ = inline "const_syntax" (const true);

val _ = inline "const"
  (Args.context -- Scan.lift Args.name_source -- Scan.optional
      (Scan.lift (Args.$$$ "(") |-- OuterParse.enum1' "," Args.typ --| Scan.lift (Args.$$$ ")")) []
    >> (fn ((ctxt, raw_c), Ts) =>
      let
        val Const (c, _) = ProofContext.read_const_proper ctxt raw_c;
        val const = Const (c, Consts.instance (ProofContext.consts_of ctxt) (c, Ts));
      in ML_Syntax.atomic (ML_Syntax.print_term const) end));

val _ = inline "syntax_const"
  (Args.context -- Scan.lift Args.name >> (fn (ctxt, c) =>
    if Syntax.is_const (ProofContext.syn_of ctxt) c then ML_Syntax.print_string c
    else error ("Unknown syntax const: " ^ quote c)));

end;

