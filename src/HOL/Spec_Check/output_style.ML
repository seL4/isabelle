(*  Title:      HOL/Spec_Check/output_style.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Output styles for presenting Spec_Check's results.
*)

signature OUTPUT_STYLE =
sig
  val setup: theory -> theory
end

structure Output_Style: OUTPUT_STYLE =
struct

(* perl style *)

local

open StringCvt

fun new ctxt tag =
  let
    val target = Config.get ctxt Spec_Check.gen_target
    val namew = Config.get ctxt Spec_Check.column_width
    val sort_examples = Config.get ctxt Spec_Check.sort_examples
    val show_stats = Config.get ctxt Spec_Check.show_stats
    val limit = Config.get ctxt Spec_Check.examples

    val resultw = 8
    val countw = 20
    val allw = namew + resultw + countw + 2

    val maybe_sort = if sort_examples then sort (int_ord o pairself size) else I

    fun result ({count=0,...}, _) _ = "dubious"
      | result (_ : Property.stats, badobjs) false = if null badobjs then "ok" else "FAILED"
      | result ({count,tags,...}, badobjs) true =
          if not (null badobjs) then "FAILED"
          else if AList.defined (op =) tags "__GEN" andalso count < target then "dubious"
          else "ok"

    fun ratio (0, _) = "(0/0 passed)"
      | ratio (count, 0) = "(" ^ string_of_int count ^ " passed)"
      | ratio (count, n) = "(" ^ string_of_int (count - n) ^ "/" ^ string_of_int count ^  " passed)"

    fun update (stats, badobjs) donep =
      "\r" ^ padRight #"." namew tag ^ "." ^ padRight #" " resultw (result (stats, badobjs) donep)
      ^ padRight #" " countw (ratio (#count stats, length badobjs))

    fun status (_, result, (stats, badobjs)) =
      if Property.failure result then writeln (update (stats, badobjs) false) else ()

    fun prtag count (tag, n) first =
      if String.isPrefix "__" tag then ("", first)
      else
         let
           val ratio = round ((real n / real count) * 100.0)
         in
           (((if first then "" else padRight #" " allw "\n") ^
             padLeft #" " 3 (string_of_int ratio) ^ "% " ^ tag),
           false)
         end

    fun prtags ({count, tags, ...} : Property.stats) =
      if show_stats then cat_lines (fst (fold_map (prtag count) tags true)) else ""

    fun err badobjs =
      let
        fun iter [] _ = ()
          | iter (e :: es) k =
              (writeln (padLeft #" " namew (if k > 0 then "" else "counter-examples")
                ^ padRight #" " resultw (if k > 0 then "" else ":") ^ e);
              iter es (k + 1))
      in
        iter (maybe_sort (take limit (map_filter I badobjs))) 0
      end

    fun finish (stats, badobjs) =
      if null badobjs then writeln (update (stats, badobjs) true ^ prtags stats)
      else (writeln (update (stats, badobjs) true); err badobjs)
  in
    {status = status, finish = finish}
  end

in
  val perl_style = Spec_Check.register_style ("Perl", new)
end


(* CM style: meshes with CM output; highlighted in sml-mode *)

local

fun pad wd = StringCvt.padLeft #"0" wd o Int.toString

fun new ctxt tag =
  let
    val gen_target = Config.get ctxt Spec_Check.gen_target
    val _ = writeln ("[testing " ^ tag ^ "... ")
    fun finish ({count, ...}, badobjs) =
      (case (count, badobjs) of
        (0, []) => writeln ("no valid cases generated]")
      | (n, []) => writeln (
            if n >= gen_target then "ok]"
            else "ok on " ^ string_of_int n ^ "; " ^ string_of_int gen_target ^ " required]")
      | (_, es) =>
          let
            val wd = size (string_of_int (length es))
            fun each (NONE, _) = ()
              | each (SOME e, i) = writeln (tag ^ ":" ^ pad wd i ^ ".0 Error: " ^ e)
          in
            (writeln "FAILED]"; map each (es ~~ (1 upto (length es))); ())
          end)
  in
    {status = K (), finish = finish}
  end

in
  val cm_style = Spec_Check.register_style ("CM", new)
end


(* setup *)

val setup = perl_style #> cm_style

end
