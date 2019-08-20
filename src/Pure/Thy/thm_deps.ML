(*  Title:      Pure/Thy/thm_deps.ML
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Makarius

Dependencies of theorems wrt. internal derivation.
*)

signature THM_DEPS =
sig
  val all_oracles: thm list -> Proofterm.oracle list
  val has_skip_proof: thm list -> bool
  val pretty_thm_oracles: Proof.context -> thm list -> Pretty.T
  val thm_deps: theory -> thm -> (Proofterm.thm_id * Thm_Name.T) list
  val thm_deps_cmd: theory -> thm list -> unit
  val unused_thms_cmd: theory list * theory list -> (string * thm) list
end;

structure Thm_Deps: THM_DEPS =
struct

(* oracles *)

fun all_oracles thms =
  let
    fun collect (PBody {oracles, thms, ...}) =
      (if null oracles then I else apfst (cons oracles)) #>
      (tap Proofterm.join_thms thms |> fold (fn (i, thm_node) => fn (res, seen) =>
        if Inttab.defined seen i then (res, seen)
        else
          let val body = Future.join (Proofterm.thm_node_body thm_node)
          in collect body (res, Inttab.update (i, ()) seen) end));
    val bodies = map Thm.proof_body_of thms;
  in fold collect bodies ([], Inttab.empty) |> #1 |> Proofterm.unions_oracles end;

fun has_skip_proof thms =
  all_oracles thms |> exists (fn (name, _) => name = \<^oracle_name>\<open>skip_proof\<close>);

fun pretty_thm_oracles ctxt thms =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun prt_oracle (name, NONE) = [Thm.pretty_oracle ctxt name]
      | prt_oracle (name, SOME prop) =
          [Thm.pretty_oracle ctxt name, Pretty.str ":", Pretty.brk 1,
            Syntax.pretty_term_global thy prop];
  in Pretty.big_list "oracles:" (map (Pretty.item o prt_oracle) (all_oracles thms)) end;


(* thm_deps *)

fun thm_deps thy =
  let
    val lookup = Global_Theory.lookup_thm_id thy;
    fun deps (i, thm_node) res =
      if Inttab.defined res i then res
      else
        let val thm_id = Proofterm.thm_id (i, thm_node) in
          (case lookup thm_id of
            SOME thm_name => Inttab.update (i, (thm_id, thm_name)) res
          | NONE => fold deps (Proofterm.thm_node_thms thm_node) res)
        end;
  in fn thm => fold deps (Thm.thm_deps thm) Inttab.empty |> Inttab.dest |> map #2 end;


(* thm_deps_cmd *)

fun thm_deps_cmd thy thms =
  let
    fun make_node name directory =
      Graph_Display.session_node
       {name = Long_Name.base_name name, directory = directory, unfold = false, path = ""};
    fun add_dep {name = "", ...} = I
      | add_dep {name = name, body = PBody {thms = thms', ...}, ...} =
          let
            val prefix = #1 (split_last (Long_Name.explode name));
            val session =
              (case prefix of
                a :: _ =>
                  (case try (Context.get_theory {long = false} thy) a of
                    SOME thy =>
                      (case Present.theory_qualifier thy of
                        "" => []
                      | session => [session])
                  | NONE => [])
              | _ => ["global"]);
            val node = make_node name (space_implode "/" (session @ prefix));
            val deps = filter_out (fn s => s = "") (map (Proofterm.thm_node_name o #2) thms');
          in Symtab.update (name, (node, deps)) end;
    val entries0 = Proofterm.fold_body_thms add_dep (Thm.proof_bodies_of thms) Symtab.empty;
    val entries1 =
      Symtab.fold (fn (_, (_, deps)) => deps |> fold (fn d => fn tab =>
        if Symtab.defined tab d then tab
        else Symtab.update (d, (make_node d "", [])) tab)) entries0 entries0;
  in
    Symtab.fold (fn (name, (node, deps)) => cons ((name, node), deps)) entries1 []
    |> Graph_Display.display_graph_old
  end;


(* unused_thms_cmd *)

fun unused_thms_cmd (base_thys, thys) =
  let
    fun add_fact transfer space (name, ths) =
      if exists (fn thy => Global_Theory.defined_fact thy name) base_thys then I
      else
        let val {concealed, group, ...} = Name_Space.the_entry space name in
          fold_rev (fn th =>
            (case Thm.derivation_name th of
              "" => I
            | a => cons (a, (transfer th, concealed, group)))) ths
        end;
    fun add_facts thy =
      let
        val transfer = Global_Theory.transfer_theories thy;
        val facts = Global_Theory.facts_of thy;
      in Facts.fold_static (add_fact transfer (Facts.space_of facts)) facts end;

    val new_thms =
      fold add_facts thys []
      |> sort_distinct (string_ord o apply2 #1);

    val used =
      Proofterm.fold_body_thms
        (fn {name = a, ...} => a <> "" ? Symtab.update (a, ()))
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
        Thm.legacy_get_kind th = Thm.theoremK andalso is_unused a
      then
        (case group of
           NONE => ((a, th) :: thms, seen_groups)
         | SOME grp =>
             if Inttab.defined used_groups grp orelse
               Inttab.defined seen_groups grp then q
             else ((a, th) :: thms, Inttab.update (grp, ()) seen_groups))
      else q) new_thms ([], Inttab.empty);
  in rev thms' end;

end;
