(*  Title:      Pure/thm_deps.ML
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Makarius

Dependencies of theorems wrt. internal derivation.
*)

signature THM_DEPS =
sig
  val all_oracles: thm list -> Proofterm.oracle list
  val has_skip_proof: thm list -> bool
  val pretty_thm_oracles: Proof.context -> thm list -> Pretty.T
  val thm_deps: theory -> thm list -> (Proofterm.thm_id * Thm_Name.T) list
  val pretty_thm_deps: theory -> thm list -> Pretty.T
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
  all_oracles thms |> exists (fn ((name, _), _) => name = \<^oracle_name>\<open>skip_proof\<close>);

fun pretty_thm_oracles ctxt thms =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun prt_ora (name, pos) = Thm.pretty_oracle ctxt name :: Pretty.here pos;
    fun prt_oracle (ora, NONE) = prt_ora ora
      | prt_oracle (ora, SOME prop) =
          prt_ora ora @ [Pretty.str ":", Pretty.brk 1, Syntax.pretty_term_global thy prop];
    val oracles =
      (case try all_oracles thms of
        SOME oracles => oracles
      | NONE => error "Malformed proofs")
  in Pretty.big_list "oracles:" (map (Pretty.item o prt_oracle) oracles) end;


(* thm_deps *)

fun thm_deps thy =
  let
    val lookup = Global_Theory.lookup_thm_id thy;
    fun deps (i, thm_node) res =
      if Inttab.defined res i then res
      else
        let val thm_id = Proofterm.thm_id (i, thm_node) in
          (case lookup thm_id of
            SOME thm_name =>
              Inttab.update (i, SOME (thm_id, thm_name)) res
          | NONE =>
              Inttab.update (i, NONE) res
              |> fold deps (Proofterm.thm_node_thms thm_node))
        end;
  in
    fn thms =>
      (fold (fold deps o Thm.thm_deps o Thm.transfer thy) thms Inttab.empty, [])
      |-> Inttab.fold_rev (fn (_, SOME entry) => cons entry | _ => I)
  end;

fun pretty_thm_deps thy thms =
  let
    val ctxt = Proof_Context.init_global thy;
    val deps =
      (case try (thm_deps thy) thms of
        SOME deps => deps
      | NONE => error "Malformed proofs");
    val items =
      map #2 deps
      |> map (fn (name, i) => (Proof_Context.markup_extern_fact ctxt name, i))
      |> sort_by (#2 o #1)
      |> map (fn ((marks, xname), i) =>
          Pretty.item [Pretty.marks_str (marks, Thm_Name.print (xname, i))]);
  in Pretty.big_list ("dependencies: " ^ string_of_int (length items)) items end;


(* unused_thms_cmd *)

fun unused_thms_cmd (base_thys, thys) =
  let
    fun add_fact transfer space (name, ths) =
      if exists (fn thy => Global_Theory.defined_fact thy name) base_thys then I
      else
        let val {concealed, group, ...} = Name_Space.the_entry space name in
          fold_rev (transfer #> (fn th =>
            (case Thm.derivation_name th of
              "" => I
            | a => cons (a, (th, concealed, group))))) ths
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
        (map Proofterm.strip_thm_body (Thm.proof_bodies_of (map (#1 o #2) new_thms)))
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
