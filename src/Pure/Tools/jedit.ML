(*  Title:      Pure/Tools/jedit.ML
    Author:     Makarius

jEdit support.
*)

signature JEDIT =
sig
  val check_action: string * Position.T -> string
end;

structure JEdit: JEDIT =
struct

(* jEdit actions *)

local

fun parse_named a (XML.Elem ((b, props), _)) =
      (case Properties.get props "NAME" of
        SOME name => if a = b then [name] else []
      | NONE => [])
  | parse_named _ _ = [];

val isabelle_jedit_actions =
  Lazy.lazy (fn () =>
    (case XML.parse (File.read \<^file>\<open>~~/src/Tools/jEdit/src/actions.xml\<close>) of
      XML.Elem (("ACTIONS", _), body) => maps (parse_named "ACTION") body
    | _ => []));

val isabelle_jedit_dockables =
  Lazy.lazy (fn () =>
    (case XML.parse (File.read \<^file>\<open>~~/src/Tools/jEdit/src/dockables.xml\<close>) of
      XML.Elem (("DOCKABLES", _), body) => maps (parse_named "DOCKABLE") body
    | _ => []));

val jedit_actions =
  Lazy.lazy (fn () =>
    (case Isabelle_System.bash_output
      "unzip -p \"$JEDIT_HOME/dist/jedit.jar\" org/gjt/sp/jedit/actions.xml" of
      (txt, 0) =>
        (case XML.parse txt of
          XML.Elem (("ACTIONS", _), body) => maps (parse_named "ACTION") body
        | _ => [])
    | (_, rc) => error ("Cannot unzip jedit.jar\nreturn code = " ^ string_of_int rc)));

val all_actions =
  Lazy.lazy (fn () =>
    Lazy.force isabelle_jedit_actions @
    Lazy.force isabelle_jedit_dockables @
    Lazy.force jedit_actions);

in

fun check_action (name, pos) =
  if member (op =) (Lazy.force all_actions) name then name
  else
    let
      val completion =
        Completion.make (name, pos)
          (fn completed =>
            Lazy.force all_actions
            |> filter completed
            |> sort_strings
            |> map (fn a => (a, ("action", a))));
      val report = Markup.markup_report (Completion.reported_text completion);
    in error ("Bad jEdit action " ^ quote name ^ Position.here pos ^ report) end

end;

end;
