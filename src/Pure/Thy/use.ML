(*  Title:      Pure/Thy/use.ML
    ID:         $Id$
    Author:     David von Oheimb and Markus Wenzel, TU Muenchen

Redefine 'use' command in order to support path variable expansion,
automatic suffix generation, and symbolic input filtering (if
required).
*)

signature USE =
sig
  val use: string -> unit
  val exit_use: string -> unit
  val time_use: string -> unit
  val cd: string -> unit
end;

structure Use: USE =
struct

(* generate suffix *)

fun append_suffix name =
  let
    fun try [] = error ("File not found: " ^ quote name)
      | try (sfx :: sfxs) =
          if File.exists (name ^ sfx) then name ^ sfx
          else try sfxs;
  in try ["", ".ML", ".sml"] end;


(* input filtering *)

val use_orig = use;

val use_filter =
  if not needs_filtered_use then use_orig
  else
    fn name =>
      let
        val txt = File.read name;
        val txt_out = implode (SymbolFont.write_charnames' (explode txt));
      in
        if txt = txt_out then use_orig name
        else
          let
            val tmp_name = "/tmp/" ^ Path.base_name name;  (* FIXME unique prefix (!?) *)
            val _ = File.write tmp_name txt_out;
            val rm = OS.FileSys.remove;
          in
            use_orig tmp_name handle exn => (rm tmp_name; raise exn);
            rm tmp_name
          end
      end;


(* use commands *)

val use = use_filter o append_suffix o Path.expand getenv;

(*use the file, but exit with error code if errors found*)
fun exit_use name = use name handle _ => exit 1;

(*timed "use" function, printing filenames*)
fun time_use name = timeit (fn () =>
  (writeln ("\n**** Starting " ^ name ^ " ****"); use name;
   writeln ("\n**** Finished " ^ name ^ " ****")));


(* redefine cd *)

val cd = cd o Path.expand getenv;


end;
