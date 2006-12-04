(*  Title:      Pure/Thy/thm_deps.ML
    ID:         $Id$
    Author:     Stefan Berghofer, TU Muenchen

Visualize dependencies of theorems.
*)

signature BASIC_THM_DEPS =
sig
  val thm_deps : thm list -> unit
end;

signature THM_DEPS =
sig
  include BASIC_THM_DEPS
  val enable : unit -> unit
  val disable : unit -> unit
end;

structure ThmDeps : THM_DEPS =
struct

open Proofterm;

fun enable () = if ! proofs = 0 then proofs := 1 else ();
fun disable () = proofs := 0;

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
              val prefx = #1 (Library.split_last (NameSpace.unpack name));
              val session =
                (case prefx of
                  (x :: _) =>
                    (case ThyInfo.lookup_theory x of
                      SOME thy =>
                        let val name = #name (Present.get_info thy)
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

fun thm_deps thms =
  Present.display_graph
    (map snd (Symtab.dest (fst
      (fold make_deps_graph (map Thm.proof_of thms) (Symtab.empty, [])))));

end;

structure BasicThmDeps : BASIC_THM_DEPS = ThmDeps;
open BasicThmDeps;
