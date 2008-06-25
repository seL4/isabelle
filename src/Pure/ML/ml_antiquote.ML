(*  Title:      Pure/ML/ml_antiquote.ML
    ID:         $Id$
    Author:     Makarius

Common ML antiquotations.
*)

signature ML_ANTIQUOTE =
sig
  val variant: string -> Proof.context -> string * Proof.context
  val inline: string ->
    (Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val declaration: string -> string ->
    (Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val value: string ->
    (Context.generic * Args.T list -> string * (Context.generic * Args.T list)) -> unit
  val the_thms: Proof.context -> int -> thm list
  val the_thm: Proof.context -> int -> thm
end;

structure ML_Antiquote: ML_ANTIQUOTE =
struct

(** generic tools **)

(* ML names *)

structure NamesData = ProofDataFun
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

fun inline name scan = ML_Context.add_antiq name
  (scan >> (fn s => fn {struct_name, background} => ((K ("", s)), background)));

fun declaration kind name scan = ML_Context.add_antiq name
  (scan >> (fn s => fn {struct_name, background} =>
    let
      val (a, background') = variant name background;
      val env = kind ^ " " ^ a ^ " = " ^ s ^ ";\n";
      val body = struct_name ^ "." ^ a;
    in (K (env, body), background') end));

val value = declaration "val";



(** concrete antiquotations **)

fun context x = (Scan.state >> Context.proof_of) x;


(* misc *)

val _ = value "theory"
  (Scan.lift Args.name >> (fn name => "ThyInfo.get_theory " ^ ML_Syntax.print_string name)
  || Scan.succeed "ML_Context.the_global_context ()");

val _ = value "theory_ref"
  (Scan.lift Args.name >> (fn name =>
    "Theory.check_thy (ThyInfo.theory " ^ ML_Syntax.print_string name ^ ")")
  || Scan.succeed "Theory.check_thy (ML_Context.the_global_context ())");

val _ = value "context" (Scan.succeed "ML_Context.the_local_context ()");

val _ = inline "sort" (context -- Scan.lift Args.name >> (fn (ctxt, s) =>
  ML_Syntax.atomic (ML_Syntax.print_sort (Syntax.read_sort ctxt s))));

val _ = inline "typ" (Args.typ >> (ML_Syntax.atomic o ML_Syntax.print_typ));
val _ = inline "term" (Args.term >> (ML_Syntax.atomic o ML_Syntax.print_term));
val _ = inline "prop" (Args.prop >> (ML_Syntax.atomic o ML_Syntax.print_term));

val _ = value "ctyp" (Args.typ >> (fn T =>
  "Thm.ctyp_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_typ T)));

val _ = value "cterm" (Args.term >> (fn t =>
  "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t)));

val _ = value "cprop" (Args.prop >> (fn t =>
  "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t)));

val _ = value "cpat"
  (context -- Scan.lift Args.name >> uncurry ProofContext.read_term_pattern >> (fn t =>
    "Thm.cterm_of (ML_Context.the_global_context ()) " ^ ML_Syntax.atomic (ML_Syntax.print_term t)));


fun type_ syn = (context -- Scan.lift Args.name >> (fn (ctxt, c) =>
    #1 (Term.dest_Type (ProofContext.read_tyname ctxt c))
    |> syn ? Sign.base_name
    |> ML_Syntax.print_string));

val _ = inline "type_name" (type_ false);
val _ = inline "type_syntax" (type_ true);


fun const syn = context -- Scan.lift Args.name >> (fn (ctxt, c) =>
  #1 (Term.dest_Const (ProofContext.read_const_proper ctxt c))
  |> syn ? ProofContext.const_syntax_name ctxt
  |> ML_Syntax.print_string);

val _ = inline "const_name" (const false);
val _ = inline "const_syntax" (const true);

val _ = inline "const"
  (context -- Scan.lift Args.name --
    Scan.optional (Scan.lift (Args.$$$ "(") |-- Args.enum1 "," Args.typ --| Scan.lift (Args.$$$ ")")) []
    >> (fn ((ctxt, c), Ts) =>
      let val (c, _) = Term.dest_Const (ProofContext.read_const_proper ctxt c)
      in ML_Syntax.atomic (ML_Syntax.print_term (ProofContext.mk_const ctxt (c, Ts))) end));


(* abstract fact values *)

structure AuxFacts = ProofDataFun
(
  type T = thm list Inttab.table;
  fun init _ = Inttab.empty;
);

fun the_thms ctxt name = the (Inttab.lookup (AuxFacts.get ctxt) name);
fun the_thm ctxt name = the_single (the_thms ctxt name);

fun put_thms ths ctxt =
  let val i = serial ()
  in (i, AuxFacts.map (Inttab.update (i, ths)) ctxt) end;


fun thm_antiq kind scan = ML_Context.add_antiq kind
  (scan >> (fn ths => fn {struct_name, background} =>
    let
      val ((a, i), background') = background |> variant kind ||>> put_thms ths;
      val env = "val " ^ a ^ " = ML_Antiquote.the_" ^ kind ^
        " (ML_Context.the_local_context ()) " ^ string_of_int i ^ ";\n";
      val body = struct_name ^ "." ^ a;
    in (K (env, body), background') end));

val _ = thm_antiq "thm" (Attrib.thm >> single);
val _ = thm_antiq "thms" Attrib.thms;

end;

