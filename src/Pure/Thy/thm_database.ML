(*  Title:      Pure/Thy/thm_database.ML
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

ML toplevel interface to the theorem database.
*)

signature BASIC_THM_DATABASE =
sig
  val store_thm: string * thm -> thm
  val store_thms: string * thm list -> thm list
  val legacy_bindings: theory -> string
  val use_legacy_bindings: theory -> unit
end;

signature THM_DATABASE =
sig
  include BASIC_THM_DATABASE
  val qed_thms: thm list ref
  val ml_store_thm: string * thm -> unit
  val ml_store_thms: string * thm list -> unit
  val ml_reserved: string list
  val is_ml_identifier: string -> bool
end;

structure ThmDatabase: THM_DATABASE =
struct

(** store theorems **)

(* store in theory and perform presentation *)

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
  not (name mem_string ml_reserved) andalso Syntax.is_ascii_identifier name;

fun warn_ml name =
  if is_ml_identifier name then false
  else if name = "" then true
  else (warning ("Cannot bind theorem(s) " ^ quote name ^ " as ML value"); true);

val use_text_verbose = use_text Context.ml_output true;

fun ml_store_thm (name, thm) =
  let val thm' = store_thm (name, thm) in
    if warn_ml name then ()
    else (qed_thms := [thm'];
      use_text_verbose ("val " ^ name ^ " = hd (! ThmDatabase.qed_thms);"))
  end;

fun ml_store_thms (name, thms) =
  let val thms' = store_thms (name, thms) in
    if warn_ml name then ()
    else (qed_thms := thms'; use_text_verbose ("val " ^ name ^ " = ! ThmDatabase.qed_thms;"))
  end;


(* legacy bindings *)

fun legacy_bindings thy =
  let
    val thy_name = Context.theory_name thy;
    val (space, thms) = PureThy.theorems_of thy;

    fun prune name =
      let
        val xname = NameSpace.extern space name;
        fun result prfx bname =
          if (prfx = "" orelse is_ml_identifier prfx) andalso is_ml_identifier bname andalso
              NameSpace.intern space xname = name then
            SOME (prfx, (bname, xname, length (the (Symtab.lookup thms name)) = 1))
          else NONE;
        val names = NameSpace.unpack name;
      in
        (case #2 (splitAt (length names - 2, names)) of
          [bname] => result "" bname
        | [prfx, bname] => result (if prfx = thy_name then "" else prfx) bname
        | _ => NONE)
      end;

    fun mk_struct "" = I
      | mk_struct prfx = enclose ("structure " ^ prfx ^ " =\nstruct\n") "\nend\n";

    fun mk_thm (bname, xname, singleton) =
      "val " ^ bname ^ " = thm" ^ (if singleton then "" else "s") ^ " " ^ quote xname;
  in
    Symtab.keys thms |> List.mapPartial prune
    |> Symtab.make_multi |> Symtab.dest |> sort_wrt #1
    |> map (fn (prfx, entries) =>
      entries |> sort_wrt #1 |> map mk_thm |> cat_lines |> mk_struct prfx)
    |> cat_lines
  end;

fun use_legacy_bindings thy = Context.use_mltext (legacy_bindings thy) true (SOME thy);

end;

structure BasicThmDatabase: BASIC_THM_DATABASE = ThmDatabase;
open BasicThmDatabase;
