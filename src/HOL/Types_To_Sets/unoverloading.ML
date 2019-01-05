(*  Title:      HOL/Types_To_Sets/unoverloading.ML
    Author:     Ondřej Kunčar, TU München

The Unoverloading Rule (extension of the logic).
*)

signature UNOVERLOADING =
sig
  val unoverload: cterm -> thm -> thm
  val unoverload_attr: cterm -> attribute
end;

structure Unoverloading : UNOVERLOADING =
struct

(*
Unoverloading Rule (UO)

      \<turnstile> \<phi>[c::\<sigma> / x::\<sigma>]
---------------------------- [no type or constant or type class in \<phi>
        \<turnstile> \<And>x::\<sigma>. \<phi>           depends on c::\<sigma>; c::\<sigma> is undefined]
*)

(* The following functions match_args, reduction and entries_of were
   cloned from defs.ML and theory.ML because the functions are not public.
   Notice that these functions already belong to the critical code.
*)

(* >= *)
fun match_args (Ts, Us) =
  if Type.could_matches (Ts, Us) then
    Option.map Envir.subst_type
      (SOME (Type.raw_matches (Ts, Us) Vartab.empty) handle Type.TYPE_MATCH => NONE)
  else NONE;

fun reduction defs (deps : Defs.entry list) : Defs.entry list option =
  let
    fun reduct Us (Ts, rhs) =
      (case match_args (Ts, Us) of
        NONE => NONE
      | SOME subst => SOME (map (apsnd (map subst)) rhs));
    fun reducts (d, Us) = get_first (reduct Us) (Defs.get_deps defs d);

    val reds = map (`reducts) deps;
    val deps' =
      if forall (is_none o #1) reds then NONE
      else SOME (fold_rev
        (fn (NONE, dp) => insert (op =) dp | (SOME dps, _) => fold (insert (op =)) dps) reds []);
  in deps' end;

fun const_and_typ_entries_of thy tm =
 let
   val consts =
     fold_aterms (fn Const const => insert (op =) (Theory.const_dep thy const) | _ => I) tm [];
   val types =
     (fold_types o fold_subtypes) (fn Type t => insert (op =) (Theory.type_dep t) | _ => I) tm [];
 in
   consts @ types
 end;


(* The actual implementation *)

(** BEGINNING OF THE CRITICAL CODE **)

fun fold_atyps_classes f =
  fold_atyps (fn T as TFree (_, S) => fold (pair T #> f) S
    | T as TVar (_, S) => fold (pair T #> f) S
    (* just to avoid a warning about incomplete patterns *)
    | _ => raise TERM ("fold_atyps_classes", []));

fun class_entries_of thy tm =
  let
    val var_classes = (fold_types o fold_atyps_classes) (insert op=) tm [];
  in
    map (Logic.mk_of_class #> Term.head_of #> Term.dest_Const #> Theory.const_dep thy) var_classes
  end;

fun unoverload_impl cconst thm =
  let
    fun err msg = raise THM ("unoverloading: " ^ msg, 0, [thm]);

    val _ = null (Thm.hyps_of thm) orelse err "the theorem has meta hypotheses";
    val _ = null (Thm.tpairs_of thm) orelse err "the theorem contains unresolved flex-flex pairs";

    val prop = Thm.prop_of thm;
    val prop_tfrees = rev (Term.add_tfree_names prop []);
    val _ = null prop_tfrees orelse err ("the theorem contains free type variables "
      ^ commas_quote prop_tfrees);

    val const = Thm.term_of cconst;
    val _ = Term.is_Const const orelse err "the parameter is is not a constant";
    val const_tfrees = rev (Term.add_tfree_names const []);
    val _ = null const_tfrees orelse err ("the constant contains free type variables "
      ^ commas_quote const_tfrees);

    val thy = Thm.theory_of_thm thm;
    val defs = Theory.defs_of thy;

    val const_entry = Theory.const_dep thy (Term.dest_Const const);

    val Uss = Defs.specifications_of defs (fst const_entry);
    val _ = forall (fn spec => is_none (match_args (#lhs spec, snd const_entry))) Uss
      orelse err "the constant instance has already a specification";

    val context = Defs.global_context thy;
    val prt_entry = Pretty.string_of o Defs.pretty_entry context;

    fun dep_err (c, Ts) (d, Us) =
      err (prt_entry (c, Ts) ^ " depends on " ^ prt_entry (d, Us));
    fun deps_of entry = perhaps_loop (reduction defs) [entry] |> these;
    fun not_depends_on_const prop_entry = forall (not_equal const_entry) (deps_of prop_entry)
      orelse dep_err prop_entry const_entry;
    val prop_entries = const_and_typ_entries_of thy prop @ class_entries_of thy prop;
    val _ = forall not_depends_on_const prop_entries;
  in
    Thm.global_cterm_of thy (Logic.all const prop) |> Thm.weaken_sorts (Thm.shyps_of thm)
  end;

(** END OF THE CRITICAL CODE **)

val (_, unoverload_oracle) = Context.>>> (Context.map_theory_result
  (Thm.add_oracle (\<^binding>\<open>unoverload\<close>,
  fn (const, thm) => unoverload_impl const  thm)));

fun unoverload const thm = unoverload_oracle (const, thm);

fun unoverload_attr const =
  Thm.rule_attribute [] (fn _ => fn thm => (unoverload const thm));

val const = Args.context -- Args.term  >>
  (fn (ctxt, tm) =>
    if not (Term.is_Const tm)
    then error ("The term is not a constant: " ^ Syntax.string_of_term ctxt tm)
    else tm |> Logic.varify_types_global |> Thm.cterm_of ctxt);

val _ = Context.>> (Context.map_theory (Attrib.setup \<^binding>\<open>unoverload\<close>
  (const >> unoverload_attr) "unoverload an uninterpreted constant"));

end;
