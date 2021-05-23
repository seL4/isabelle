(*  Title:      Pure/System/scala_compiler.ML
    Author:     Makarius

Scala compiler operations.
*)

signature SCALA_COMPILER =
sig
  val toplevel: bool -> string -> unit
  val static_check: string * Position.T -> unit
end;

structure Scala_Compiler: SCALA_COMPILER =
struct

(* check declaration *)

fun toplevel interpret source =
  let val errors =
    (interpret, source)
    |> let open XML.Encode in pair bool string end
    |> YXML.string_of_body
    |> \<^scala>\<open>scala_toplevel\<close>
    |> YXML.parse_body
    |> let open XML.Decode in list string end
  in if null errors then () else error (cat_lines errors) end;

fun static_check (source, pos) =
  toplevel false ("package test\nclass __Dummy__ { __dummy__ => " ^ source ^ " }")
    handle ERROR msg => error (msg ^ Position.here pos);


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

val class =
  Scan.option
    (Parse.$$$ "(" |-- Parse.!!! (Parse.$$$ "in" |-- Parse.name -- types  --| Parse.$$$ ")"));

val arguments =
  (Parse.nat >> (fn n => replicate n "_") ||
    Parse.list (Parse.underscore || Parse.name >> (fn T => "_ : " ^ T))) >> print_args;

val args = Scan.optional (Parse.$$$ "(" |-- arguments --| Parse.$$$ ")") " _";

fun scala_name name =
  let val latex = Latex.string (Latex.output_ascii_breakable "." name)
  in Latex.enclose_block "\\isatt{" "}" [latex] end;

in

val _ =
  Theory.setup
    (Document_Output.antiquotation_verbatim_embedded \<^binding>\<open>scala\<close>
      (Scan.lift Args.embedded_position)
      (fn _ => fn (s, pos) => (static_check (s, pos); s)) #>

    Document_Output.antiquotation_raw_embedded \<^binding>\<open>scala_type\<close>
      (Scan.lift (Args.embedded_position -- (types >> print_types)))
      (fn _ => fn ((t, pos), type_args) =>
        (static_check ("type _Test_" ^ type_args ^ " = " ^ t ^ type_args, pos);
          scala_name (t ^ type_args))) #>

    Document_Output.antiquotation_raw_embedded \<^binding>\<open>scala_object\<close>
      (Scan.lift Args.embedded_position)
      (fn _ => fn (x, pos) => (static_check ("val _test_ = " ^ x, pos); scala_name x)) #>

    Document_Output.antiquotation_raw_embedded \<^binding>\<open>scala_method\<close>
      (Scan.lift (class -- Args.embedded_position -- types -- args))
      (fn _ => fn (((class_context, (method, pos)), method_types), method_args) =>
        let
          val class_types = (case class_context of SOME (_, Ts) => Ts | NONE => []);
          val def = "def _test_" ^ print_types (merge (op =) (method_types, class_types));
          val def_context =
            (case class_context of
              NONE => def ^ " = "
            | SOME c => def ^ "(_this_ : " ^ print_class c ^ ") = _this_.");
          val source = def_context ^ method ^ method_args;
          val _ = static_check (source, pos);
          val text = (case class_context of NONE => method | SOME c => print_class c ^ "." ^ method);
        in scala_name text end));

end;

end;
