(*  Title:      Pure/Thy/symbol_input.ML
    ID:         $Id$
    Author:     David von Oheimb and Markus Wenzel, TU Muenchen

Defines 'use' command with symbol input filtering.
*)

signature SYMBOL_INPUT =
sig
  val use: string -> unit
end;

structure SymbolInput: SYMBOL_INPUT =
struct

fun fix_name name =
  if file_exists name then name
  else if file_exists (name ^ ".ML") then name ^ ".ML"
  else if file_exists (name ^ ".sml") then name ^ ".sml"
  else error ("File not found: " ^ quote name);


val use =
  if not needs_filtered_use then use
  else
    fn raw_name =>
      let
        val name = fix_name raw_name;

        val infile = TextIO.openIn name;
        val txt = TextIO.inputAll infile;
        val _ = TextIO.closeIn infile;

        val txt_out = implode (SymbolFont.write_charnames' (explode txt));
      in
        if txt = txt_out then use name
        else
          let
            val tmp_name = "/tmp/" ^ base_name name;  (* FIXME unique prefix (!?) *)
            val outfile = TextIO.openOut tmp_name;
            val _ = TextIO.output (outfile, txt_out);
            val _ = TextIO.closeOut outfile;

            val rm = OS.FileSys.remove;
          in
            use tmp_name handle exn => (rm tmp_name; raise exn);
            rm tmp_name
          end
      end;

end;
