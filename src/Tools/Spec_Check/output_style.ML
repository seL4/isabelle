(*  Title:      Tools/Spec_Check/output_style.ML
    Author:     Lukas Bulwahn and Nicolai Schaffroth, TU Muenchen
    Author:     Christopher League

Output styles for presenting Spec_Check's results.
*)

structure Output_Style : sig end =
struct

(* perl style *)

val perl_style =
  Spec_Check.register_style "Perl"
    (fn ctxt => fn tag =>
      let
        val target = Config.get ctxt Spec_Check.gen_target
        val namew = Config.get ctxt Spec_Check.column_width
        val sort_examples = Config.get ctxt Spec_Check.sort_examples
        val show_stats = Config.get ctxt Spec_Check.show_stats
        val limit = Config.get ctxt Spec_Check.examples

        val resultw = 8
        val countw = 20
        val allw = namew + resultw + countw + 2

        val maybe_sort = if sort_examples then sort (int_ord o apply2 size) else I

        fun result ({count = 0, ...}, _) _ = "dubious"
          | result (_ : Property.stats, badobjs) false = if null badobjs then "ok" else "FAILED"
          | result ({count, tags}, badobjs) true =
              if not (null badobjs) then "FAILED"
              else if AList.defined (op =) tags "__GEN" andalso count < target then "dubious"
              else "ok"

        fun ratio (0, _) = "(0/0 passed)"
          | ratio (count, 0) = "(" ^ string_of_int count ^ " passed)"
          | ratio (count, n) =
              "(" ^ string_of_int (count - n) ^ "/" ^ string_of_int count ^  " passed)"

        fun update (stats, badobjs) donep =
          "\r" ^ StringCvt.padRight #"." namew tag ^ "." ^
          StringCvt.padRight #" " resultw (result (stats, badobjs) donep) ^
          StringCvt.padRight #" " countw (ratio (#count stats, length badobjs))

        fun status (_, result, (stats, badobjs)) =
          if Property.failure result then warning (update (stats, badobjs) false) else ()

        fun prtag count (tag, n) first =
          if String.isPrefix "__" tag then ("", first)
          else
             let
               val ratio = round ((real n / real count) * 100.0)
             in
               (((if first then "" else StringCvt.padRight #" " allw "\n") ^
                 StringCvt.padLeft #" " 3 (string_of_int ratio) ^ "% " ^ tag),
               false)
             end

        fun prtags ({count, tags} : Property.stats) =
          if show_stats then cat_lines (fst (fold_map (prtag count) tags true)) else ""

        fun err badobjs =
          let
            fun iter [] _ = ()
              | iter (e :: es) k =
                  (warning (StringCvt.padLeft #" " namew (if k > 0 then "" else "counter-examples") ^
                    StringCvt.padRight #" " resultw (if k > 0 then "" else ":") ^ e);
                  iter es (k + 1))
          in
            iter (maybe_sort (take limit (map_filter I badobjs))) 0
          end

        fun finish (stats, badobjs) =
          if null badobjs then writeln (update (stats, badobjs) true ^ prtags stats)
          else (warning (update (stats, badobjs) true); err badobjs)
      in
        {status = status, finish = finish}
      end)

val _ = Theory.setup perl_style;


(* CM style: meshes with CM output; highlighted in sml-mode *)

val cm_style =
  Spec_Check.register_style "CM"
    (fn ctxt => fn tag =>
      let
        fun pad wd = StringCvt.padLeft #"0" wd o Int.toString
        val gen_target = Config.get ctxt Spec_Check.gen_target
        val _ = writeln ("[testing " ^ tag ^ "... ")
        fun finish ({count, ...} : Property.stats, badobjs) =
          (case (count, badobjs) of
            (0, []) => warning ("no valid cases generated]")
          | (n, []) => writeln (
                if n >= gen_target then "ok]"
                else "ok on " ^ string_of_int n ^ "; " ^ string_of_int gen_target ^ " required]")
          | (_, es) =>
              let
                val wd = size (string_of_int (length es))
                fun each (NONE, _) = ()
                  | each (SOME e, i) = warning (tag ^ ":" ^ pad wd i ^ ".0 Error: " ^ e)
              in
                (warning "FAILED]"; map each (es ~~ (1 upto (length es))); ())
              end)
      in
        {status = K (), finish = finish}
      end)

val _ = Theory.setup cm_style;

end
