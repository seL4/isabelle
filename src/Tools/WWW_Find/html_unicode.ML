(*  Title:      html_unicode.ML
    Author:     Timothy Bourke, NICTA
                Based on Pure/Thy/html.ML
                by Markus Wenzel and Stefan Berghofer, TU Muenchen

HTML presentation elements that use unicode code points.
*)

signature HTML_UNICODE =
sig
  val print_mode: ('a -> 'b) -> 'a -> 'b
end;

structure HTML_Unicode: HTML_UNICODE =
struct

(** HTML print modes **)

(* mode *)

val htmlunicodeN = "HTMLUnicode";
fun print_mode f x = PrintMode.with_modes [htmlunicodeN, Symbol.xsymbolsN] f x;

(* symbol output *)

local
  val sym_width_lookup = Symtab.make
   [("\<spacespace>", 2),
    ("\<Longleftarrow>", 2),
    ("\<longleftarrow>", 2),
    ("\<Longrightarrow>", 2),
    ("\<longrightarrow>", 2),
    ("\<longleftrightarrow>", 2),
    ("\<^bsub>", 0),
    ("\<^esub>", 0),
    ("\<^bsup>", 0),
    ("\<^esup>", 0)];

  fun sym_width s =
    (case Symtab.lookup sym_width_lookup s of
       NONE => 1
     | SOME w => w);

  fun output_sym s =
    if Symbol.is_raw s then (1, Symbol.decode_raw s)
    else
      (case UnicodeSymbols.symbol_to_unicode s of
         SOME x => (sym_width s, "&#" ^ Int.toString x ^ ";") (* numeric entities *)
         (* SOME x => (sym_width s, UnicodeSymbols.utf8 [x])     (* utf-8 *) *)
       | NONE => (size s, XML.text s));

  fun output_sub s = apsnd (enclose "<sub>" "</sub>") (output_sym s);
  fun output_sup s = apsnd (enclose "<sup>" "</sup>") (output_sym s);
  fun output_loc s = apsnd (enclose "<span class=\"loc\">" "</span>") (output_sym s);

  fun output_syms ("\<^sub>" :: s :: ss) = output_sub s :: output_syms ss
    | output_syms ("\<^isub>" :: s :: ss) = output_sub s :: output_syms ss
    | output_syms ("\<^sup>" :: s :: ss) = output_sup s :: output_syms ss
    | output_syms ("\<^isup>" :: s :: ss) = output_sup s :: output_syms ss
    | output_syms ("\<^loc>" :: s :: ss) = output_loc s :: output_syms ss
    | output_syms (s :: ss) = output_sym s :: output_syms ss
    | output_syms [] = [];

  fun output_width str =
    if not (exists_string (fn s => s = "\\" orelse s = "<" orelse s = ">" orelse s = "&") str)
    then Output.default_output str
    else
      let val (syms, width) = fold_map (fn (w, s) => fn width => (s, w + width))
        (output_syms (Symbol.explode str)) 0
      in (implode syms, width) end;
in

val output = #1 o output_width;

val _ = Output.add_mode htmlunicodeN output_width Symbol.encode_raw;

end;

(* common markup *)

fun span s = ("<span class=" ^ quote (XML.text s) ^ ">", "</span>");

val _ = Markup.add_mode htmlunicodeN (fn (name, _) => span name);

end;
