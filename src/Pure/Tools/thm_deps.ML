(*  Title:      Pure/Tools/thm_deps.ML
    Author:     Stefan Berghofer, TU Muenchen

Visualize dependencies of theorems.
*)

signature THM_DEPS =
sig
  val thm_deps: theory -> thm list -> unit
  val unused_thms: theory list * theory list -> (string * thm) list
end;

structure Thm_Deps: THM_DEPS =
struct

(* thm_deps *)

fun thm_deps thy thms =
  let
    fun add_dep ("", _, _) = I
      | add_dep (name, _, PBody {thms = thms', ...}) =
          let
            val prefix = #1 (split_last (Long_Name.explode name));
            val session =
              (case prefix of
                a :: _ =>
                  (case try (Context.get_theory thy) a of
                    SOME thy =>
                      (case Present.session_name thy of
                        "" => []
                      | session => [session])
                  | NONE => [])
               | _ => ["global"]);
            val directory = space_implode "/" (session @ prefix);
            val parents = filter_out (fn s => s = "") (map (#1 o #2) thms');
          in
            cons ((name, Graph_Display.session_node
              {name = Long_Name.base_name name, directory = directory,
                unfold = false, path = ""}), parents)
          end;
    val gr = Proofterm.fold_body_thms add_dep (Thm.proof_bodies_of thms) [];
  in Graph_Display.display_graph (sort_wrt I (map (fst o fst) gr), Graph.make gr) end;

val _ =
  Outer_Syntax.command @{command_spec "thm_deps"} "visualize theorem dependencies"
    (Parse.xthms1 >> (fn args =>
      Toplevel.unknown_theory o Toplevel.keep (fn state =>
        thm_deps (Toplevel.theory_of state) (Attrib.eval_thms (Toplevel.context_of state) args))));


(* unused_thms *)

fun unused_thms (base_thys, thys) =
  let
    fun add_fact space (name, ths) =
      if exists (fn thy => Global_Theory.defined_fact thy name) base_thys then I
      else
        let val {concealed, group, ...} = Name_Space.the_entry space name in
          fold_rev (fn th =>
            (case Thm.derivation_name th of
              "" => I
            | a => cons (a, (th, concealed, group)))) ths
        end;
    fun add_facts facts = Facts.fold_static (add_fact (Facts.space_of facts)) facts;

    val new_thms =
      fold (add_facts o Global_Theory.facts_of) thys []
      |> sort_distinct (string_ord o apply2 #1);

    val used =
      Proofterm.fold_body_thms
        (fn (a, _, _) => a <> "" ? Symtab.update (a, ()))
        (map Proofterm.strip_thm (Thm.proof_bodies_of (map (#1 o #2) new_thms)))
        Symtab.empty;

    fun is_unused a = not (Symtab.defined used a);

    (*groups containing at least one used theorem*)
    val used_groups = fold (fn (a, (_, _, group)) =>
      if is_unused a then I
      else
        (case group of
          NONE => I
        | SOME grp => Inttab.update (grp, ()))) new_thms Inttab.empty;

    val (thms', _) = fold (fn (a, (th, concealed, group)) => fn q as (thms, seen_groups) =>
      if not concealed andalso
        (* FIXME replace by robust treatment of thm groups *)
        member (op =) [Thm.theoremK, Thm.lemmaK, Thm.corollaryK] (Thm.legacy_get_kind th) andalso
        is_unused a
      then
        (case group of
           NONE => ((a, th) :: thms, seen_groups)
         | SOME grp =>
             if Inttab.defined used_groups grp orelse
               Inttab.defined seen_groups grp then q
             else ((a, th) :: thms, Inttab.update (grp, ()) seen_groups))
      else q) new_thms ([], Inttab.empty);
  in rev thms' end;

val _ =
  Outer_Syntax.command @{command_spec "unused_thms"} "find unused theorems"
    (Scan.option ((Scan.repeat1 (Scan.unless Parse.minus Parse.name) --| Parse.minus) --
       Scan.option (Scan.repeat1 (Scan.unless Parse.minus Parse.name))) >> (fn opt_range =>
        Toplevel.keep (fn state =>
          let
            val thy = Toplevel.theory_of state;
            val ctxt = Toplevel.context_of state;
            fun pretty_thm (a, th) = Proof_Context.pretty_fact ctxt (a, [th]);
            val get_theory = Context.get_theory thy;
          in
            unused_thms
              (case opt_range of
                NONE => (Theory.parents_of thy, [thy])
              | SOME (xs, NONE) => (map get_theory xs, [thy])
              | SOME (xs, SOME ys) => (map get_theory xs, map get_theory ys))
            |> map pretty_thm |> Pretty.writeln_chunks
          end)));

end;

