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
    (case XML.parse (File.read @{path "~~/src/Tools/jEdit/src/actions.xml"}) of
      XML.Elem (("ACTIONS", _), body) => maps (parse_named "ACTION") body
    | _ => []));

val isabelle_jedit_dockables =
  Lazy.lazy (fn () =>
    (case XML.parse (File.read @{path "~~/src/Tools/jEdit/src/dockables.xml"}) of
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

fun is_action a =
  member (op =) (Lazy.force isabelle_jedit_actions) a orelse
  member (op =) (Lazy.force isabelle_jedit_dockables) a orelse
  member (op =) (Lazy.force jedit_actions) a;

in

fun check_action (a, pos) =
  if is_action a then a
  else error ("Bad jEdit action " ^ quote a ^ Position.here pos);

end;

end;
