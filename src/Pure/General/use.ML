(*  Title:      Pure/General/use.ML
    ID:         $Id$
    Author:     David von Oheimb and Markus Wenzel, TU Muenchen

Redefine 'use' command in order to support path variable expansion,
automatic suffix generation, and symbolic input filtering (if required
by the underlying ML system).
*)

signature BASIC_USE =
sig
  val use: string -> unit
  val exit_use: string -> unit
  val time_use: string -> unit
  val cd: string -> unit
end;

signature USE =
sig
  include BASIC_USE
  val use_path: Path.T -> unit
end;

structure Use: USE =
struct

(* generate suffix *)   (* FIXME elim (cf. Thy/thy_load) (!?) *)

fun append_suffix path =
  let
    fun try [] = error ("File not found: " ^ quote (Path.pack path))
      | try (sfx :: sfxs) =
          let val xpath = Path.ext sfx path
          in if File.exists xpath then xpath else try sfxs end;
  in try ["", "ML", "sml"] end;


(* input filtering *)

val use_path =
  if not needs_filtered_use then File.use
  else
    fn path =>
      let
        val txt = File.read path;
        val txt_out = Symbol.input txt;
      in
        if txt = txt_out then File.use path
        else
          let val tmp_path = File.tmp_path path in
            File.write tmp_path txt_out;
            File.use tmp_path handle exn => (File.rm tmp_path; raise exn);
            File.rm tmp_path
          end
      end;


(* use commands *)

val use = use_path o append_suffix o Path.unpack;

(*use the file, but exit with error code if errors found*)
fun exit_use name = use name handle _ => exit 1;

(*timed "use" function, printing filenames*)
fun time_use name = timeit (fn () =>
  (writeln ("\n**** Starting " ^ name ^ " ****"); use name;
   writeln ("\n**** Finished " ^ name ^ " ****")));


(* cd *)

val cd = File.cd o Path.unpack;


end;

structure BasicUse: BASIC_USE = Use;    (*opened later*)
