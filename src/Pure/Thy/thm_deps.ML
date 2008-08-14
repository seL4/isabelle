(*  Title:      Pure/Thy/thm_deps.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Visualize dependencies of theorems.
*)

signature THM_DEPS =
sig
  val enable: unit -> unit
  val disable: unit -> unit
  val thm_deps: thm list -> unit
  val unused_thms: theory list * theory list -> (string * thm) list
end;

structure ThmDeps: THM_DEPS =
struct

(* thm_deps *)

fun enable () = CRITICAL (fn () => if ! proofs = 0 then proofs := 1 else ());
fun disable () = proofs := 0;

local

open Proofterm;

fun dest_thm_axm (PThm (name, prf, _, _)) = (name, prf)
  | dest_thm_axm (PAxm (name, _, _)) = (name ^ " (Ax)", MinProof ([], [], []))
  | dest_thm_axm _ = ("", MinProof ([], [], []));

fun make_deps_graph (AbsP (_, _, prf)) = make_deps_graph prf
  | make_deps_graph (Abst (_, _, prf)) = make_deps_graph prf
  | make_deps_graph (prf1 %% prf2) = make_deps_graph prf1 #> make_deps_graph prf2
  | make_deps_graph (prf % _) = make_deps_graph prf
  | make_deps_graph (MinProof (thms, axms, _)) =
      fold (make_deps_graph o Proofterm.proof_of_min_thm) thms #>
      fold (make_deps_graph o Proofterm.proof_of_min_axm) axms
  | make_deps_graph prf = (fn p as (gra, parents) =>
      let val (name, prf') = dest_thm_axm prf
      in
        if name <> "" then
          if not (Symtab.defined gra name) then
            let
              val (gra', parents') = make_deps_graph prf' (gra, []);
              val prefx = #1 (Library.split_last (NameSpace.explode name));
              val session =
                (case prefx of
                  (x :: _) =>
                    (case ThyInfo.lookup_theory x of
                      SOME thy =>
                        let val name = Present.session_name thy
                        in if name = "" then [] else [name] end
                    | NONE => [])
                 | _ => ["global"]);
            in
              if member (op =) parents' name then (gra', parents union parents')
              else (Symtab.update (name,
                {name = Sign.base_name name, ID = name,
                 dir = space_implode "/" (session @ prefx),
                 unfold = false, path = "", parents = parents'}) gra',
               insert (op =) name parents)
            end
          else (gra, insert (op =) name parents)
        else
          make_deps_graph prf' (gra, parents)
      end);

in

fun thm_deps thms =
  Present.display_graph
    (map snd (sort_wrt fst (Symtab.dest (fst
      (fold make_deps_graph (map Thm.proof_of thms) (Symtab.empty, []))))));

end;


(* unused_thms *)

fun unused_thms (base_thys, thys) =
  let
    fun add_fact (name, ths) =
      if exists (fn thy => PureThy.defined_fact thy name) base_thys then I
      else fold_rev (fn th => (case Thm.get_name th of "" => I | a => cons (a, th))) ths;
    val thms =
      fold (Facts.fold_static add_fact o PureThy.facts_of) thys []
      |> sort_distinct (string_ord o pairself #1);
    val tab = fold Proofterm.thms_of_proof
      (map (Proofterm.strip_thm o Thm.proof_of o snd) thms) Symtab.empty;
    fun is_unused (name, th) = case Symtab.lookup tab name of
        NONE => true
      | SOME ps => not (member (op aconv) (map fst ps) (Thm.prop_of th));
    (* groups containing at least one used theorem *)
    val grps = fold (fn p as (_, thm) => if is_unused p then I else
      case Thm.get_group thm of
        NONE => I | SOME grp => Symtab.update (grp, ())) thms Symtab.empty;
    val (thms', _) = fold (fn p as (s, thm) => fn q as (thms, grps') =>
      if member (op =) [Thm.theoremK, Thm.lemmaK, Thm.corollaryK, Thm.axiomK] (Thm.get_kind thm)
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

