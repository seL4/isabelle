(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen
    License:    GPL (GNU GENERAL PUBLIC LICENSE)

Interface to thm database (see also Pure/pure_thy.ML).
*)

signature BASIC_THM_DATABASE =
sig
  val store_thm: string * thm -> thm
  val store_thms: string * thm list -> thm list
end;

signature THM_DATABASE =
sig
  include BASIC_THM_DATABASE
  val qed_thms: thm list ref
  val ml_store_thm: string * thm -> unit
  val ml_store_thms: string * thm list -> unit
  val is_ml_identifier: string -> bool
  val ml_reserved: string list
  val thms_containing: theory -> string list -> (string * thm) list
  val print_thms_containing: theory -> term list -> unit
end;

structure ThmDatabase: THM_DATABASE =
struct

(** store theorems **)

(* store in theory and generate HTML *)

fun store_thm (name, thm) =
  let val thm' = hd (PureThy.smart_store_thms (name, [thm]))
  in Present.theorem name thm'; thm' end;

fun store_thms (name, thms) =
  let val thms' = PureThy.smart_store_thms (name, thms)
  in Present.theorems name thms'; thms' end;


(* store on ML toplevel *)

val qed_thms: thm list ref = ref [];

val ml_reserved =
 ["abstype", "and", "andalso", "as", "case", "do", "datatype", "else",
  "end", "exception", "fn", "fun", "handle", "if", "in", "infix",
  "infixr", "let", "local", "nonfix", "of", "op", "open", "orelse",
  "raise", "rec", "then", "type", "val", "with", "withtype", "while",
  "eqtype", "functor", "include", "sharing", "sig", "signature",
  "struct", "structure", "where"];

fun is_ml_identifier name =
  Syntax.is_identifier name andalso not (name mem ml_reserved);

fun warn_ml name =
  if is_ml_identifier name then false
  else if name = "" then true
  else (warning ("Cannot bind theorem(s) " ^ quote name ^ " as ML value"); true);

val use_text_verbose = use_text Context.ml_output true;

fun ml_store_thm (name, thm) =
  let val thm' = store_thm (name, thm) in
    if warn_ml name then ()
    else (qed_thms := [thm']; use_text_verbose ("val " ^ name ^ " = hd (! ThmDatabase.qed_thms);"))
  end;

fun ml_store_thms (name, thms) =
  let val thms' = store_thms (name, thms) in
    if warn_ml name then ()
    else (qed_thms := thms'; use_text_verbose ("val " ^ name ^ " = ! ThmDatabase.qed_thms;"))
  end;



(** retrieve theorems **)

fun thms_containing thy consts = PureThy.thms_containing thy consts
  handle THEORY (msg, _) => error msg | THM (msg, _, _) => error msg;

fun print_thms_containing thy ts =
  let
    val prt_const =
      Pretty.quote o Pretty.str o Sign.cond_extern (Theory.sign_of thy) Sign.constK;
    fun prt_thm (a, th) = Pretty.block [Pretty.str (a ^ ":"),
      Pretty.brk 1, Display.pretty_thm_no_quote (#1 (Drule.freeze_thaw th))];

    val cs = foldr Term.add_term_consts (ts, []);
    val header =
      if Library.null cs then []
      else [Pretty.block (Pretty.breaks (Pretty.str "theorems containing constants:" ::
          map prt_const cs)), Pretty.str ""];
  in
    if Library.null cs andalso not (Library.null ts) then
      warning "thms_containing: no constants in specification"
    else (header @ map prt_thm (thms_containing thy cs)) |> Pretty.chunks |> Pretty.writeln
  end;


end;

structure BasicThmDatabase: BASIC_THM_DATABASE = ThmDatabase;
open BasicThmDatabase;
