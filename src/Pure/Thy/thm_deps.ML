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

fun dest_thm_axm (PThm (nt, prf, _, _)) = (nt, prf)
  | dest_thm_axm (PAxm (n, _, _)) = ((n ^ " (Ax)", []), MinProof [])
  | dest_thm_axm _ = (("", []), MinProof []);

fun make_deps_graph (p, AbsP (_, _, prf)) = make_deps_graph (p, prf)
  | make_deps_graph (p, Abst (_, _, prf)) = make_deps_graph (p, prf)
  | make_deps_graph (p, prf1 % prf2) =
      make_deps_graph (make_deps_graph (p, prf1), prf2)
  | make_deps_graph (p, prf %% _) = make_deps_graph (p, prf)
  | make_deps_graph (p, MinProof prfs) = foldl make_deps_graph (p, prfs)
  | make_deps_graph (p as (gra, parents), prf) =
      let val ((name, tags), prf') = dest_thm_axm prf
      in
        if name <> "" andalso not (Drule.has_internal tags) then
          if is_none (Symtab.lookup (gra, name)) then
            let
              val (gra', parents') = make_deps_graph ((gra, []), prf');
              val prefx = #1 (Library.split_last (NameSpace.unpack name));
              val session =
                (case prefx of
                  (x :: _) =>
                    (case ThyInfo.lookup_theory x of
                      Some thy =>
                        let val name = #name (Present.get_info thy)
                        in if name = "" then [] else [name] end 
                    | None => [])
                 | _ => ["global"]);
            in
              (Symtab.update ((name,
                {name = Sign.base_name name, ID = name,
                 dir = space_implode "/" (session @ prefx),
                 unfold = false, path = "", parents = parents'}), gra'),
               name ins parents)
            end
          else (gra, name ins parents)
        else
          make_deps_graph ((gra, parents), prf')
      end;

fun thm_deps thms =
  let
    val _ = writeln "Generating graph ...";
    val gra = map snd (Symtab.dest (fst (foldl make_deps_graph ((Symtab.empty, []),
      map (#2 o #der o Thm.rep_thm) thms))));
    val path = File.tmp_path (Path.unpack "theorems.graph");
    val _ = Present.write_graph gra path;
    val _ = system ("$ISATOOL browser -d " ^ Path.pack (Path.expand path) ^ " &");
  in () end;

end;

structure BasicThmDeps : BASIC_THM_DEPS = ThmDeps;
open BasicThmDeps;
