(*  Title:      HOL/Tools/Metis/metis_instantiations.ML
    Author:     Lukas Bartl, Universitaet Augsburg

Inference of Variable Instantiations for Metis.
*)

signature METIS_INSTANTIATIONS =
sig
  type inst

  type infer_params = {
    infer_ctxt : Proof.context,
    type_enc : string,
    lam_trans : string,
    th_name : thm -> string option,
    new_skolem : bool,
    using_th_cls_pairs : (thm * thm list) list,
    arg_th_cls_pairs : (thm * thm list) list,
    lifted : (string * term) list,
    sym_tab : int Symtab.table,
    axioms : (Metis_Thm.thm * thm) list,
    mth : Metis_Thm.thm
  }

  val instantiate : bool Config.T
  val instantiate_undefined : bool Config.T
  val metis_call : string -> string -> string
  val table_of_thm_inst : thm * inst -> cterm Vars.table
  val pretty_name_inst : Proof.context -> string * inst -> Pretty.T
  val string_of_name_inst : Proof.context -> string * inst -> string
  val infer_thm_insts : Proof.context -> infer_params ->
    ((thm * inst) list * (thm * inst) list) option
  val instantiate_call : Proof.context -> infer_params -> thm list -> thm -> unit
end;

structure Metis_Instantiations : METIS_INSTANTIATIONS =
struct

open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Generate
open Metis_Reconstruct

(* Type of variable instantiations of a theorem.  This is a list of (certified)
 * terms suitably ordered for an of-instantiation of the theorem. *)
type inst = cterm list

(* Params needed for inference of variable instantiations *)
type infer_params = {
  infer_ctxt : Proof.context,
  type_enc : string,
  lam_trans : string,
  th_name : thm -> string option,
  new_skolem : bool,
  using_th_cls_pairs : (thm * thm list) list,
  arg_th_cls_pairs : (thm * thm list) list,
  lifted : (string * term) list,
  sym_tab : int Symtab.table,
  axioms : (Metis_Thm.thm * thm) list,
  mth : Metis_Thm.thm
}

(* Config option to enable suggestion of of-instantiations (e.g. "assms(1)[of x]") *)
val instantiate = Attrib.setup_config_bool @{binding "metis_instantiate"} (K false)
(* Config option to allow instantiation of variables with "undefined" *)
val instantiate_undefined = Attrib.setup_config_bool @{binding "metis_instantiate_undefined"} (K true)

fun metis_call type_enc lam_trans =
  let
    val type_enc =
      case AList.find (fn (enc, encs) => enc = hd encs) type_enc_aliases type_enc of
        [alias] => alias
      | _ => type_enc
    val opts =
      [] |> lam_trans <> default_metis_lam_trans ? cons lam_trans
         |> type_enc <> partial_typesN ? cons type_enc
  in
    metisN ^ (if null opts then "" else " (" ^ commas opts ^ ")")
  end

(* Variables of a theorem ordered the same way as in of-instantiations
 * (cf. Rule_Insts.of_rule) *)
fun of_vars_of_thm th = Vars.build (Vars.add_vars (Thm.full_prop_of th)) |> Vars.list_set

(* "_" terms are used for variables without instantiation *)
val is_dummy_cterm = Term.is_dummy_pattern o Thm.term_of
val thm_insts_trivial = forall (forall is_dummy_cterm o snd)

fun table_of_thm_inst (th, cts) =
  of_vars_of_thm th ~~ cts
  |> filter_out (is_dummy_cterm o snd)
  |> Vars.make

fun open_attrib name =
  case try (unsuffix "]") name of
    NONE => name ^ "["
  | SOME name' => name' ^ ", "

fun pretty_inst_cterm ctxt ct =
  let
    val pretty = Syntax.pretty_term ctxt (Thm.term_of ct)
    val is_dummy = ATP_Util.content_of_pretty pretty = "_"
  in
    (* Do not quote single "_" *)
    pretty |> not is_dummy ? ATP_Util.pretty_maybe_quote ctxt
  end

(* Pretty of-instantiation *)
fun pretty_name_inst ctxt (name, inst) =
  case drop_suffix is_dummy_cterm inst of
    [] => Pretty.str name
  | cts =>
    map (pretty_inst_cterm ctxt) cts
    |> Pretty.breaks o cons (Pretty.str "of")
    |> Pretty.enclose (open_attrib name) "]"

val string_of_name_inst = Pretty.string_of oo pretty_name_inst

(* Infer Metis axioms with corresponding subtitutions *)
fun infer_metis_axiom_substs mth =
  let
    fun add_metis_axiom_substs msubst mth =
      case Metis_Thm.inference mth of
        (Metis_Thm.Axiom, []) => cons (msubst, mth)
      | (Metis_Thm.Metis_Subst, _) =>
        (case Metis_Proof.thmToInference mth of
          Metis_Proof.Metis_Subst (msubst', par) =>
            add_metis_axiom_substs (Metis_Subst.compose msubst' msubst) par
        | _ => raise Fail "expected Metis_Subst")
      | (_, pars) => fold (add_metis_axiom_substs msubst) pars
  in
    add_metis_axiom_substs Metis_Subst.empty mth []
  end

(* Variables are renamed during clausification by importing and exporting
 * theorems.  Do the same here to find the right variable. *)
fun import_export_thm ctxt th =
  let
    (* cf. Meson_Clausify.nnf_axiom *)
    val (import_th, import_ctxt) =
      Drule.zero_var_indexes th
      |> (fn th' => Variable.import true [th'] ctxt)
      |>> the_single o snd
    (* cf. Meson_Clausify.cnf_axiom *)
    val export_th = import_th
      |> singleton (Variable.export import_ctxt ctxt)
  in
    (* cf. Meson.finish_cnf *)
    Drule.zero_var_indexes export_th
  end

(* Find the theorem corresponding to a Metis axiom if it has a name.
 * "Theorems" are Isabelle theorems given to the metis tactic.
 * "Axioms" are clauses given to the Metis prover. *)
fun metis_axiom_to_thm ctxt {th_name, axioms, ...} th_cls_pairs (msubst, maxiom) =
  let
    val axiom = lookth axioms maxiom
  in
    List.find (have_common_thm ctxt [axiom] o snd) th_cls_pairs
    |> Option.mapPartial (fn (th, _) => th_name th |> Option.map (pair th))
    |> Option.map (pair (msubst, maxiom, axiom))
  end

(* Build a table : term Vartab.table list Thmtab.table that maps a theorem to a
 * list of variable substitutions (theorems can be instantiated multiple times)
 * from Metis substitutions *)
fun metis_substs_to_table ctxt {infer_ctxt, type_enc, lifted, new_skolem, sym_tab, ...}
    th_of_vars th_msubsts =
  let
    val _ = trace_msg ctxt (K "AXIOM SUBSTITUTIONS")
    val type_enc = type_enc_of_string Strict type_enc
    val thy = Proof_Context.theory_of ctxt

    (* Replace Skolem terms with "_" because they are unknown to the user
     * (cf. Metis_Generate.reveal_old_skolem_terms) *)
    val dummy_old_skolem_terms = map_aterms
      (fn t as Const (s, T) =>
          if String.isPrefix old_skolem_const_prefix s
          then Term.dummy_pattern T
          else t
        | t => t)

    (* Infer types and replace "_" terms/types with schematic variables *)
    val infer_types_pattern =
      singleton (Type_Infer_Context.infer_types_finished
        (Proof_Context.set_mode Proof_Context.mode_pattern infer_ctxt))

    (* "undefined" if allowed and not using new_skolem, "_" otherwise. *)
    val undefined_pattern =
      (* new_skolem uses schematic variables which should not be instantiated with "undefined" *)
      if not new_skolem andalso Config.get ctxt instantiate_undefined then
        Const o (pair @{const_name "undefined"})
      else
        Term.dummy_pattern

    (* Instantiate schematic and free variables *)
    val inst_vars_frees = map_aterms
      (fn t as Free (x, T) =>
        (* an undeclared/internal free variable is unknown/inaccessible to the user,
         * so we replace it with "_" *)
        let
          val x' = Variable.revert_fixed ctxt x
        in
          if not (Variable.is_declared ctxt x') orelse Name.is_internal x' then
            Term.dummy_pattern T
          else
            t
        end
      | Var (_, T) =>
        (* a schematic variable can be replaced with any term,
         * so we replace it with "undefined" *)
        undefined_pattern T
      | t => t)

    (* Remove arguments of "_" unknown functions because the functions could
     * change (e.g. instantiations can change Skolem functions).
     * Type inference also introduces arguments (cf. Term.replace_dummy_patterns). *)
    fun eliminate_dummy_args (t $ u) =
        let
          val t' = eliminate_dummy_args t
        in
          if Term.is_dummy_pattern t' then
            Term.dummy_pattern (Term.fastype_of t' |> Term.range_type)
          else
            t' $ eliminate_dummy_args u
        end
      | eliminate_dummy_args (Abs (s, T, t)) = Abs (s, T, eliminate_dummy_args t)
      | eliminate_dummy_args t = t

    (* Polish Isabelle term, s.t. it can be displayed
     * (cf. Metis_Reconstruct.polish_hol_terms and ATP_Proof_Reconstruct.termify_line) *)
    val polish_term =
      reveal_lam_lifted lifted (* reveal lifted lambdas *)
      #> dummy_old_skolem_terms (* eliminate Skolem terms *)
      #> infer_types_pattern (* type inference *)
      #> eliminate_lam_wrappers (* eliminate Metis.lambda wrappers *)
      #> uncombine_term thy (* eliminate Meson.COMB* terms *)
      #> Envir.beta_eta_contract (* simplify lambda terms *)
      #> simplify_bool (* simplify boolean terms *)
      #> Term.show_dummy_patterns (* reveal "_" that have been replaced by type inference *)
      #> inst_vars_frees (* eliminate schematic and free variables *)
      #> eliminate_dummy_args (* eliminate arguments of "_" (unknown functions) *)

    (* Translate a Metis substitution to Isabelle *)
    fun add_subst_to_table ((msubst, maxiom, axiom), (th, name)) th_substs_table =
      let
        val _ = trace_msg ctxt (fn () => "Metis axiom: " ^ Metis_Thm.toString maxiom)
        val _ = trace_msg ctxt (fn () => "Metis substitution: " ^ Metis_Subst.toString msubst)
        val _ = trace_msg ctxt (fn () => "Isabelle axiom: " ^ Thm.string_of_thm infer_ctxt axiom)
        val _ = trace_msg ctxt (fn () => "Isabelle theorem: " ^
          Thm.string_of_thm ctxt th ^ " (" ^ name ^ ")")

        (* Only indexnames of variables without types
         * because types can change during clausification *)
        val vars =
          inter (op =) (map fst (of_vars_of_thm axiom))
            (map fst (Thmtab.lookup th_of_vars th |> the))

        (* Translate Metis variable and term to Isabelle *)
        fun translate_var_term (mvar, mt) =
          Metis_Name.toString mvar
          (* cf. remove_typeinst in Metis_Reconstruct.inst_inference *)
          |> unprefix_and_unascii schematic_var_prefix
          (* cf. find_var in Metis_Reconstruct.inst_inference *)
          |> Option.mapPartial (fn name => List.find (fn (a, _) => a = name) vars)
          (* cf. subst_translation in Metis_Reconstruct.inst_inference *)
          |> Option.map (fn var => (var, hol_term_of_metis infer_ctxt type_enc sym_tab mt))

        (* Build the substitution table and instantiate the remaining schematic variables *)
        fun build_subst_table substs =
          let
            (* Variable of the axiom that didn't get instantiated by Metis,
             * the type is later set via type unification *)
            val undefined_term = undefined_pattern (TVar ((Name.aT, 0), []))
          in
            Vartab.build (vars |> fold (fn var => Vartab.default
              (var, AList.lookup (op =) substs var |> the_default undefined_term)))
          end

        val raw_substs =
          Metis_Subst.toList msubst
          |> map_filter translate_var_term
        val _ = if null raw_substs then () else
          trace_msg ctxt (fn () => cat_lines ("Raw Isabelle substitution:" ::
            (raw_substs |> map (fn (var, t) =>
              Term.string_of_vname var ^ " |-> " ^
              Syntax.string_of_term infer_ctxt t))))

        val subst = raw_substs
          |> map (apsnd polish_term)
          |> build_subst_table
        val _ = trace_msg ctxt (fn () =>
          if Vartab.is_empty subst then
            "No Isabelle substitution"
          else
            cat_lines ("Final Isabelle substitution:" ::
              (Vartab.dest subst |> map (fn (var ,t) =>
                Term.string_of_vname var ^ " |-> " ^
                Syntax.string_of_term ctxt t))))

        (* Try to merge the substitution with another substitution of the theorem *)
        fun insert_subst [] = [subst]
          | insert_subst (subst' :: substs') =
            Vartab.merge Term.aconv_untyped (subst', subst) :: substs'
            handle Vartab.DUP _ => subst' :: insert_subst substs'
      in
        Thmtab.lookup th_substs_table th
        |> insert_subst o these
        |> (fn substs => Thmtab.update (th, substs) th_substs_table)
      end
  in
    fold add_subst_to_table th_msubsts Thmtab.empty
  end

(* Build variable instantiations : thm * inst list from the table *)
fun table_to_thm_insts ctxt th_of_vars th_substs_table =
  let
    val thy = Proof_Context.theory_of ctxt

    (* Unify types of a variable with the term for instantiation
     * (cf. Drule.infer_instantiate_types, Metis_Reconstruct.cterm_incr_types) *)
    fun unify (tyenv, maxidx) T t =
      let
        val t' = Term.map_types (Logic.incr_tvar (maxidx + 1)) t
        val U = Term.fastype_of t'
        val maxidx' = Term.maxidx_term t' maxidx
      in
        (t', Sign.typ_unify thy (T, U) (tyenv, maxidx'))
      end

    (* Instantiate type variables with a type unifier and import remaining ones
     * (cf. Drule.infer_instantiate_types) *)
    fun inst_unifier (ts, tyenv) =
      let
        val instT =
          TVars.build (tyenv |> Vartab.fold (fn (xi, (S, T)) =>
            TVars.add ((xi, S), Envir.norm_type tyenv T)))
        val ts' = map (Term_Subst.instantiate (instT, Vars.empty)) ts
      in
        Variable.importT_terms ts' ctxt |> fst
      end

    (* Build variable instantiations from a substitution table and instantiate
     * the remaining schematic variables with "_" *)
    fun add_subst th subst =
      let
        val of_vars = Thmtab.lookup th_of_vars th |> the

        fun unify_or_dummy (var, T) unify_params =
          Vartab.lookup subst var
          |> Option.map (unify unify_params T)
          |> the_default (Term.dummy_pattern T, unify_params)
      in
        fold_map unify_or_dummy of_vars (Vartab.empty, Thm.maxidx_of th)
        |> inst_unifier o apsnd fst
        |> map (Thm.cterm_of ctxt)
        |> cons o pair th
      end
  in
    Thmtab.fold_rev (fn (th, substs) => fold (add_subst th) substs) th_substs_table []
  end

fun really_infer_thm_insts ctxt
    (infer_params as {th_name, using_th_cls_pairs, arg_th_cls_pairs, mth, ...}) =
  let
    (* Compute the theorem variables ordered as in of-instantiations.
     * import_export_thm is used to get the same variables as in axioms. *)
    val using_th_of_vars =
      Thmtab.build (using_th_cls_pairs |> fold (fn (th, _) => Thmtab.default
        (th, of_vars_of_thm (import_export_thm ctxt th))))

    val using_th_insts =
      infer_metis_axiom_substs mth
      |> map_filter (metis_axiom_to_thm ctxt infer_params using_th_cls_pairs)
      |> metis_substs_to_table ctxt infer_params using_th_of_vars
      |> table_to_thm_insts ctxt using_th_of_vars

    val _ = trace_msg ctxt (fn () => cat_lines ("using THEOREM INSTANTIATIONS" ::
      (if thm_insts_trivial using_th_insts then
         ["No instantiation available"]
       else
         using_th_insts |> maps (fn th_inst as (th, _) =>
           let
             val table = table_of_thm_inst th_inst
           in
             if Vars.is_empty table then
               []
             else
               "Theorem " ^ Thm.string_of_thm ctxt th ^ " (" ^ the (th_name th) ^ "):" ::
               (Vars.dest table |> map (fn (var, ct) =>
                 Syntax.string_of_term ctxt (Var var) ^ " |-> " ^
                 Syntax.string_of_term ctxt (Thm.term_of ct)))
           end))))

    val arg_th_of_vars =
      Thmtab.build (arg_th_cls_pairs |> fold (fn (th, _) => Thmtab.default
        (th, of_vars_of_thm (import_export_thm ctxt th))))

    val arg_th_insts =
      infer_metis_axiom_substs mth
      |> map_filter (metis_axiom_to_thm ctxt infer_params arg_th_cls_pairs)
      |> metis_substs_to_table ctxt infer_params arg_th_of_vars
      |> table_to_thm_insts ctxt arg_th_of_vars

    val _ = trace_msg ctxt (fn () => cat_lines ("ARGUMENT THEOREM INSTANTIATIONS" ::
      (if thm_insts_trivial arg_th_insts then
         ["No instantiation available"]
       else
         arg_th_insts |> maps (fn th_inst as (th, _) =>
           let
             val table = table_of_thm_inst th_inst
           in
             if Vars.is_empty table then
               []
             else
               "Theorem " ^ Thm.string_of_thm ctxt th ^ " (" ^ the (th_name th) ^ "):" ::
               (Vars.dest table |> map (fn (var, ct) =>
                 Syntax.string_of_term ctxt (Var var) ^ " |-> " ^
                 Syntax.string_of_term ctxt (Thm.term_of ct)))
           end))))
  in
    (using_th_insts, arg_th_insts)
  end

(* Infer variable instantiations *)
fun infer_thm_insts ctxt infer_params =
  \<^try>\<open>SOME (really_infer_thm_insts ctxt infer_params)
    catch exn => (trace_msg ctxt (fn () => Runtime.exn_message exn); NONE)\<close>

(* Write suggested command with instantiations *)
fun write_command ctxt {type_enc, lam_trans, th_name, ...} schem_usings st
    (using_th_insts, arg_th_insts) =
  if null using_th_insts andalso null arg_th_insts then
    ()
  else
    let
      val _ = trace_msg ctxt (K "INSTANTIATIONS")
      val apply_str = if Thm.nprems_of st = 0 then "by" else "apply"

      val (using_schem_insts, arg_insts) =
        List.partition (fn (th, _) => member Thm.eq_thm schem_usings th) arg_th_insts
        |>> append using_th_insts

      val using_prs =
        if null using_schem_insts then
          [Pretty.str ""]
        else
          Pretty.breaks (Pretty.str "using" ::
            map (pretty_name_inst ctxt o apfst (the o th_name)) using_schem_insts
            @ [Pretty.brk 0])
      val metis_pr = Pretty.str (metis_call type_enc lam_trans)
      val tactic_pr =
        if null arg_insts then
          [metis_pr]
          |> Pretty.enclose (apply_str ^ " ") ""
        else
          arg_insts
          |> map (pretty_name_inst ctxt o apfst (the o th_name))
          |> cons metis_pr
          |> Pretty.breaks
          |> Pretty.enclose (apply_str ^ " (") ")"

      val command_str =
        Pretty.symbolic_string_of (Pretty.paragraph (using_prs @ [tactic_pr]))
    in
      writeln ("Found variable instantiations, try this:" ^
        (* Add optional markup break (command may need multiple lines) *)
        Markup.markup (Markup.break {width = 1, indent = 2}) " " ^
        Active.sendback_markup_command command_str)
    end

(* Infer variable instantiations and instantiations *)
fun instantiate_call ctxt infer_params schem_usings st =
  (case infer_thm_insts ctxt infer_params of
    NONE => ()
  | SOME (using_th_insts, arg_th_insts) =>
    (if thm_insts_trivial using_th_insts then [] else using_th_insts,
     if thm_insts_trivial arg_th_insts then [] else arg_th_insts)
    |> write_command ctxt infer_params schem_usings st)

end;
