(*  Title:      Pure/System/scala_compiler.ML
    Author:     Makarius

Scala compiler operations.
*)

signature SCALA_COMPILER =
sig
  val toplevel: string -> unit
  val static_check: string -> unit
end;

structure Scala_Compiler: SCALA_COMPILER =
struct

(* check declaration *)

fun toplevel source =
  let val errors =
    \<^scala>\<open>scala_toplevel\<close> source
    |> YXML.parse_body
    |> let open XML.Decode in list string end
  in if null errors then () else error (cat_lines errors) end;

fun static_check source =
  toplevel ("package test\nclass __Dummy__ { __dummy__ => " ^ source ^ " }");


(* antiquotations *)

local

fun make_list bg en = space_implode "," #> enclose bg en;

fun print_args [] = ""
  | print_args xs = make_list "(" ")" xs;

fun print_types [] = ""
  | print_types Ts = make_list "[" "]" Ts;

fun print_class (c, Ts) = c ^ print_types Ts;

val types =
  Scan.optional (Parse.$$$ "[" |-- Parse.list1 Parse.name --| Parse.$$$ "]") [];

val in_class =
  Parse.$$$ "(" |-- Parse.!!! (Parse.$$$ "in" |-- Parse.name -- types  --| Parse.$$$ ")");

val arguments =
  (Parse.nat >> (fn n => replicate n "_") ||
    Parse.list (Parse.underscore || Parse.name >> (fn T => "_ : " ^ T))) >> print_args
  || Scan.succeed " _";

val method_arguments = Scan.optional (Parse.$$$ "(" |-- arguments --| Parse.$$$ ")") " _";

fun scala_name name =
  let val latex = Latex.string (Latex.output_ascii_breakable "." name)
  in Latex.enclose_block "\\isatt{" "}" [latex] end;

in

val _ =
  Theory.setup
    (Thy_Output.antiquotation_verbatim_embedded \<^binding>\<open>scala\<close>
      (Scan.lift Parse.embedded) (fn _ => tap static_check) #>

    Thy_Output.antiquotation_raw_embedded \<^binding>\<open>scala_type\<close>
      (Scan.lift (Parse.embedded -- (types >> print_types)))
      (fn _ => fn (t, type_args) =>
        (static_check ("type _Test_" ^ type_args ^ " = " ^ t ^ type_args);
          scala_name (t ^ type_args))) #>

    Thy_Output.antiquotation_raw_embedded \<^binding>\<open>scala_object\<close>
      (Scan.lift Parse.embedded)
      (fn _ => fn object => (static_check ("val _test_ = " ^ object); scala_name object)) #>

    Thy_Output.antiquotation_raw_embedded \<^binding>\<open>scala_method\<close>
      (Scan.lift (Scan.option in_class -- Parse.embedded -- types -- method_arguments))
      (fn _ => fn (((class, method), method_types), method_args) =>
        let
          val class_types = (case class of SOME (_, Ts) => Ts | NONE => []);
          val def = "def _test_" ^ print_types (merge (op =) (method_types, class_types));
          val def_context =
            (case class of
              NONE => def ^ " = "
            | SOME c => def ^ "(_this_ : " ^ print_class c ^ ") = _this_.");
          val source = def_context ^ method ^ method_args;
          val _ = static_check source;
        in scala_name (case class of NONE => method | SOME c => print_class c ^ "." ^ method) end));

end;

end;
