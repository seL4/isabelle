(*  Title:      Pure/Thy/thm_deps.ML
    Author:     Stefan Berghofer, TU Muenchen

Visualize dependencies of theorems.
*)

signature THM_DEPS =
sig
  val thm_deps: thm list -> unit
  val unused_thms: theory list * theory list -> (string * thm) list
end;

structure ThmDeps: THM_DEPS =
struct

(* thm_deps *)

fun thm_deps thms =
  let
    fun add_dep ("", _, _) = I
      | add_dep (name, _, PBody {thms = thms', ...}) =
          let
            val prefix = #1 (Library.split_last (Long_Name.explode name));
            val session =
              (case prefix of
                a :: _ =>
                  (case ThyInfo.lookup_theory a of
                    SOME thy =>
                      (case Present.session_name thy of
                        "" => []
                      | session => [session])
                  | NONE => [])
               | _ => ["global"]);
            val parents = filter_out (fn s => s = "") (map (#1 o #2) thms');
            val entry =
              {name = Long_Name.base_name name,
               ID = name,
               dir = space_implode "/" (session @ prefix),
               unfold = false,
               path = "",
               parents = parents};
          in cons entry end;
    val deps = Proofterm.fold_body_thms (add_dep o #2) (map Thm.proof_body_of thms) [];
  in Present.display_graph (sort_wrt #ID deps) end;


(* unused_thms *)

fun unused_thms (base_thys, thys) =
  let
    fun add_fact (name, ths) =
      if exists (fn thy => PureThy.defined_fact thy name) base_thys then I
      else fold_rev (fn th => (case Thm.get_name th of "" => I | a => cons (a, th))) ths;
    val thms =
      fold (Facts.fold_static add_fact o PureThy.facts_of) thys []
      |> sort_distinct (string_ord o pairself #1);

    val tab = Proofterm.fold_body_thms
      (fn (_, (name, prop, _)) => name <> "" ? Symtab.insert_list (op =) (name, prop))
      (map (Proofterm.strip_thm o Thm.proof_body_of o snd) thms) Symtab.empty;
    fun is_unused (name, th) =
      not (member (op aconv) (Symtab.lookup_list tab name) (Thm.prop_of th));

    (* groups containing at least one used theorem *)
    val grps = fold (fn p as (_, thm) => if is_unused p then I else
      case Thm.get_group thm of
        NONE => I | SOME grp => Symtab.update (grp, ())) thms Symtab.empty;
    val (thms', _) = fold (fn p as (s, thm) => fn q as (thms, grps') =>
      if member (op =) [Thm.theoremK, Thm.generatedK, Thm.lemmaK, Thm.corollaryK, Thm.axiomK] (Thm.get_kind thm)
        andalso is_unused p
      then
        (case Thm.get_group thm of
           NONE => (p :: thms, grps')
         | SOME grp =>
             (* do not output theorem if another theorem in group has been used *)
             if Symtab.defined grps grp then q
             (* output at most one unused theorem per group *)
             else if Symtab.defined grps' grp then q
             else (p :: thms, Symtab.update (grp, ()) grps'))
      else q) thms ([], Symtab.empty)
  in rev thms' end;

end;

