(*  Title:      Pure/more_thm.ML
    Author:     Makarius

Further operations on type ctyp/cterm/thm, outside the inference kernel.
*)

infix aconvc;

signature BASIC_THM =
sig
  include BASIC_THM
  val show_consts: bool Config.T
  val show_hyps: bool Config.T
  val show_tags: bool Config.T
  val aconvc: cterm * cterm -> bool
  type attribute = Context.generic * thm -> Context.generic option * thm option
end;

signature THM =
sig
  include THM
  val eq_ctyp: ctyp * ctyp -> bool
  val aconvc: cterm * cterm -> bool
  val add_tvars: thm -> ctyp TVars.table -> ctyp TVars.table
  val add_vars: thm -> cterm Vars.table -> cterm Vars.table
  val dest_ctyp0: ctyp -> ctyp
  val dest_ctyp1: ctyp -> ctyp
  val dest_funT: ctyp -> ctyp * ctyp
  val strip_type: ctyp -> ctyp list * ctyp
  val instantiate_ctyp: ctyp TVars.table -> ctyp -> ctyp
  val all_name: Proof.context -> string * cterm -> cterm -> cterm
  val all: Proof.context -> cterm -> cterm -> cterm
  val mk_binop: cterm -> cterm -> cterm -> cterm
  val dest_binop: cterm -> cterm * cterm
  val dest_implies: cterm -> cterm * cterm
  val dest_equals: cterm -> cterm * cterm
  val dest_equals_lhs: cterm -> cterm
  val dest_equals_rhs: cterm -> cterm
  val lhs_of: thm -> cterm
  val rhs_of: thm -> cterm
  val is_reflexive: thm -> bool
  val eq_thm: thm * thm -> bool
  val eq_thm_prop: thm * thm -> bool
  val eq_thm_strict: thm * thm -> bool
  val equiv_thm: theory -> thm * thm -> bool
  val class_triv: theory -> class -> thm
  val of_sort: ctyp * sort -> thm list
  val is_dummy: thm -> bool
  val add_thm: thm -> thm list -> thm list
  val del_thm: thm -> thm list -> thm list
  val merge_thms: thm list * thm list -> thm list
  val item_net: thm Item_Net.T
  val item_net_intro: thm Item_Net.T
  val item_net_elim: thm Item_Net.T
  val declare_hyps: cterm -> Proof.context -> Proof.context
  val assume_hyps: cterm -> Proof.context -> thm * Proof.context
  val unchecked_hyps: Proof.context -> Proof.context
  val restore_hyps: Proof.context -> Proof.context -> Proof.context
  val undeclared_hyps: Context.generic -> thm -> term list
  val check_hyps: Context.generic -> thm -> thm
  val declare_term_sorts: term -> Proof.context -> Proof.context
  val extra_shyps': Proof.context -> thm -> sort list
  val check_shyps: Proof.context -> thm -> thm
  val weaken_sorts': Proof.context -> cterm -> cterm
  val elim_implies: thm -> thm -> thm
  val assume_prems: int -> thm -> thm
  val forall_intr_name: string * cterm -> thm -> thm
  val forall_elim_var: int -> thm -> thm
  val forall_elim_vars: int -> thm -> thm
  val instantiate_frees: ctyp TFrees.table * cterm Frees.table -> thm -> thm
  val instantiate': ctyp option list -> cterm option list -> thm -> thm
  val forall_intr_frees: thm -> thm
  val forall_intr_vars: thm -> thm
  val unvarify_global: theory -> thm -> thm
  val unvarify_axiom: theory -> string -> thm
  val rename_params_rule: string list * int -> thm -> thm
  val rename_boundvars: term -> term -> thm -> thm
  val add_axiom: Proof.context -> binding * term -> theory -> (string * thm) * theory
  val add_axiom_global: binding * term -> theory -> (string * thm) * theory
  val add_def: Defs.context -> bool -> bool -> binding * term -> theory -> (string * thm) * theory
  val add_def_global: bool -> bool -> binding * term -> theory -> (string * thm) * theory
  type attribute = Context.generic * thm -> Context.generic option * thm option
  type binding = binding * attribute list
  val tag_rule: string * string -> thm -> thm
  val untag_rule: string -> thm -> thm
  val is_free_dummy: thm -> bool
  val tag_free_dummy: thm -> thm
  val def_name: string -> string
  val def_name_optional: string -> string -> string
  val def_binding: Binding.binding -> Binding.binding
  val def_binding_optional: Binding.binding -> Binding.binding -> Binding.binding
  val make_def_binding: bool -> Binding.binding -> Binding.binding
  val the_name_hint: thm -> Thm_Name.T  (*exception THM*)
  val has_name_hint: thm -> bool
  val get_name_hint: thm -> Thm_Name.T
  val put_name_hint: Thm_Name.T -> thm -> thm
  val theoremK: string
  val legacy_get_kind: thm -> string
  val kind_rule: string -> thm -> thm
  val rule_attribute: thm list -> (Context.generic -> thm -> thm) -> attribute
  val declaration_attribute: (thm -> Context.generic -> Context.generic) -> attribute
  val mixed_attribute: (Context.generic * thm -> Context.generic * thm) -> attribute
  val apply_attribute: attribute -> thm -> Context.generic -> thm * Context.generic
  val attribute_declaration: attribute -> thm -> Context.generic -> Context.generic
  val theory_attributes: attribute list -> thm -> theory -> thm * theory
  val proof_attributes: attribute list -> thm -> Proof.context -> thm * Proof.context
  val no_attributes: 'a -> 'a * 'b list
  val simple_fact: 'a -> ('a * 'b list) list
  val tag: string * string -> attribute
  val untag: string -> attribute
  val kind: string -> attribute
  val register_proofs: thm list lazy -> theory -> theory
  val consolidate_theory: theory -> unit
  val expose_theory: theory -> unit
  val show_consts: bool Config.T
  val show_hyps: bool Config.T
  val show_tags: bool Config.T
  val pretty_thm_raw: Proof.context -> {quote: bool, show_hyps: bool} -> thm -> Pretty.T
  val pretty_thm: Proof.context -> thm -> Pretty.T
  val pretty_thm_item: Proof.context -> thm -> Pretty.T
  val pretty_thm_global: theory -> thm -> Pretty.T
  val string_of_thm: Proof.context -> thm -> string
  val string_of_thm_global: theory -> thm -> string
end;

structure Thm: THM =
struct

(** basic operations **)

(* collecting ctyps and cterms *)

val eq_ctyp = op = o apply2 Thm.typ_of;
val op aconvc = op aconv o apply2 Thm.term_of;

val add_tvars =
  Thm.fold_atomic_ctyps {hyps = false}
    (fn tab => fn T => Term.is_TVar T andalso not (TVars.defined tab (Term.dest_TVar T)))
    (fn cT => TVars.add (Term.dest_TVar (Thm.typ_of cT), cT));

val add_vars =
  Thm.fold_atomic_cterms {hyps = false}
    (fn tab => fn t => Term.is_Var t andalso not (Vars.defined tab (Term.dest_Var t)))
    (fn ct => Vars.add (Term.dest_Var (Thm.term_of ct), ct));


(* ctyp operations *)

val dest_ctyp0 = Thm.dest_ctypN 0;
val dest_ctyp1 = Thm.dest_ctypN 1;

fun dest_funT cT =
  (case Thm.typ_of cT of
    Type ("fun", _) => let val [A, B] = Thm.dest_ctyp cT in (A, B) end
  | T => raise TYPE ("dest_funT", [T], []));

(* ctyp version of strip_type: maps  [T1,...,Tn]--->T  to   ([T1,T2,...,Tn], T) *)
fun strip_type cT =
  (case Thm.typ_of cT of
    Type ("fun", _) =>
      let
        val (cT1, cT2) = dest_funT cT;
        val (cTs, cT') = strip_type cT2
      in (cT1 :: cTs, cT') end
  | _ => ([], cT));

fun instantiate_ctyp instT cT =
  Thm.instantiate_cterm (instT, Vars.empty) (Thm.var (("x", 0), cT))
  |> Thm.ctyp_of_cterm;


(* cterm operations *)

fun all_name ctxt (x, t) A =
  let
    val T = Thm.typ_of_cterm t;
    val all_const = Thm.cterm_of ctxt (Const ("Pure.all", (T --> propT) --> propT));
  in Thm.apply all_const (Thm.lambda_name (x, t) A) end;

fun all ctxt t A = all_name ctxt ("", t) A;

fun mk_binop c a b = Thm.apply (Thm.apply c a) b;
fun dest_binop ct = (Thm.dest_arg1 ct, Thm.dest_arg ct);

fun dest_implies ct =
  (case Thm.term_of ct of
    Const ("Pure.imp", _) $ _ $ _ => dest_binop ct
  | _ => raise TERM ("dest_implies", [Thm.term_of ct]));

fun dest_equals ct =
  (case Thm.term_of ct of
    Const ("Pure.eq", _) $ _ $ _ => dest_binop ct
  | _ => raise TERM ("dest_equals", [Thm.term_of ct]));

fun dest_equals_lhs ct =
  (case Thm.term_of ct of
    Const ("Pure.eq", _) $ _ $ _ => Thm.dest_arg1 ct
  | _ => raise TERM ("dest_equals_lhs", [Thm.term_of ct]));

fun dest_equals_rhs ct =
  (case Thm.term_of ct of
    Const ("Pure.eq", _) $ _ $ _ => Thm.dest_arg ct
  | _ => raise TERM ("dest_equals_rhs", [Thm.term_of ct]));

val lhs_of = dest_equals_lhs o Thm.cprop_of;
val rhs_of = dest_equals_rhs o Thm.cprop_of;


(* equality *)

fun is_reflexive th = op aconv (Logic.dest_equals (Thm.prop_of th))
  handle TERM _ => false;

val eq_thm = is_equal o Thm.thm_ord;

val eq_thm_prop = op aconv o apply2 Thm.full_prop_of;

fun eq_thm_strict ths =
  eq_thm ths andalso
  Context.eq_thy_id (apply2 Thm.theory_id ths) andalso
  op = (apply2 Thm.maxidx_of ths) andalso
  op = (apply2 Thm.get_tags ths);


(* pattern equivalence *)

fun equiv_thm thy ths =
  Pattern.equiv thy (apply2 (Thm.full_prop_of o Thm.transfer thy) ths);


(* type classes and sorts *)

fun class_triv thy c =
  Thm.of_class (Thm.global_ctyp_of thy (TVar ((Name.aT, 0), [c])), c);

fun of_sort (T, S) = map (fn c => Thm.of_class (T, c)) S;


(* misc operations *)

fun is_dummy thm =
  (case try Logic.dest_term (Thm.concl_of thm) of
    NONE => false
  | SOME t => Term.is_dummy_pattern (Term.head_of t));


(* collections of theorems in canonical order *)

val add_thm = update eq_thm_prop;
val del_thm = remove eq_thm_prop;
val merge_thms = merge eq_thm_prop;

val item_net = Item_Net.init eq_thm_prop (single o Thm.full_prop_of);
val item_net_intro = Item_Net.init eq_thm_prop (single o Thm.concl_of);
val item_net_elim = Item_Net.init eq_thm_prop (single o Thm.major_prem_of);



(** declared hyps and sort hyps **)

structure Hyps = Proof_Data
(
  type T = {checked_hyps: bool, hyps: Termset.T, shyps: sort Ord_List.T};
  fun init _ : T = {checked_hyps = true, hyps = Termset.empty, shyps = []};
);

fun map_hyps f = Hyps.map (fn {checked_hyps, hyps, shyps} =>
  let val (checked_hyps', hyps', shyps') = f (checked_hyps, hyps, shyps)
  in {checked_hyps = checked_hyps', hyps = hyps', shyps = shyps'} end);


(* hyps *)

fun declare_hyps raw_ct ctxt = ctxt |> map_hyps (fn (checked_hyps, hyps, shyps) =>
  let
    val ct = Thm.transfer_cterm' ctxt raw_ct;
    val hyps' = Termset.insert (Thm.term_of ct) hyps;
  in (checked_hyps, hyps', shyps) end);

fun assume_hyps ct ctxt = (Thm.assume ct, declare_hyps ct ctxt);

val unchecked_hyps = map_hyps (fn (_, hyps, shyps) => (false, hyps, shyps));

fun restore_hyps ctxt =
  map_hyps (fn (_, hyps, shyps) => (#checked_hyps (Hyps.get ctxt), hyps, shyps));

fun undeclared_hyps context th =
  Thm.hyps_of th
  |> filter_out
    (case context of
      Context.Theory _ => K false
    | Context.Proof ctxt =>
        (case Hyps.get ctxt of
          {checked_hyps = false, ...} => K true
        | {hyps, ...} => Termset.member hyps));

fun check_hyps context th =
  (case undeclared_hyps context th of
    [] => th
  | undeclared =>
      error (Pretty.string_of (Pretty.big_list "Undeclared hyps:"
        (map (Pretty.item o single o Syntax.pretty_term (Syntax.init_pretty context)) undeclared))));


(* shyps *)

fun declare_term_sorts t =
  map_hyps (fn (checked_hyps, hyps, shyps) =>
    (checked_hyps, hyps, Sorts.insert_term t shyps));

fun extra_shyps' ctxt th =
  Sorts.subtract (#shyps (Hyps.get ctxt)) (Thm.extra_shyps th);

fun check_shyps ctxt raw_th =
  let
    val th = Thm.strip_shyps raw_th;
    val extra_shyps = extra_shyps' ctxt th;
  in
    if null extra_shyps then th
    else error (Pretty.string_of (Pretty.block (Pretty.str "Pending sort hypotheses:" ::
      Pretty.brk 1 :: Pretty.commas (map (Syntax.pretty_sort ctxt) extra_shyps))))
  end;

val weaken_sorts' = Thm.weaken_sorts o #shyps o Hyps.get;



(** basic derived rules **)

(*Elimination of implication
  A    A \<Longrightarrow> B
  ------------
        B
*)
fun elim_implies thA thAB = Thm.implies_elim thAB thA;


(* assume_prems: shift at most n premises into hyps, where n < 0 means infinity *)

fun assume_prems n th =
  fold (elim_implies o Thm.assume) (Thm.take_cprems_of n th) th;


(* forall_intr_name *)

fun forall_intr_name (a, x) th =
  let
    val th' = Thm.forall_intr x th;
    val prop' = (case Thm.prop_of th' of all $ Abs (_, T, b) => all $ Abs (a, T, b));
  in Thm.renamed_prop prop' th' end;


(* forall_elim_var(s) *)

local

val used_frees =
  Name.build_context o
    Thm.fold_terms {hyps = true} Term.declare_free_names;

fun used_vars i =
  Name.build_context o
    Thm.fold_terms {hyps = false} (Term.declare_var_names (fn j => i = j));

fun dest_all ct used =
  (case Thm.term_of ct of
    Const ("Pure.all", _) $ Abs (x, _, _) =>
      let
        val (x', used') = Name.variant x used;
        val (v, ct') = Thm.dest_abs_fresh x' (Thm.dest_arg ct);
      in SOME ((x, Thm.ctyp_of_cterm v), (ct', used')) end
  | _ => NONE);

fun dest_all_list ct used =
  (case dest_all ct used of
    NONE => ([], used)
  | SOME (v, (ct', used')) =>
      let val (vs, used'') = dest_all_list ct' used'
      in (v :: vs, used'') end);

fun forall_elim_vars_list vars i th =
  let
    val (vars', _) =
      (vars, used_vars i th) |-> fold_map (fn (x, T) => fn used =>
        let val (x', used') = Name.variant x used
        in (Thm.var ((x', i), T), used') end);
  in fold Thm.forall_elim vars' th end;

in

fun forall_elim_vars i th =
  forall_elim_vars_list (#1 (dest_all_list (Thm.cprop_of th) (used_frees th))) i th;

fun forall_elim_var i th =
  let
    val vars =
      (case dest_all (Thm.cprop_of th) (used_frees th) of
        SOME (v, _) => [v]
      | NONE => raise THM ("forall_elim_var", i, [th]));
  in forall_elim_vars_list vars i th end;

end;


(* instantiate frees *)

fun instantiate_frees (instT, inst) th =
  if TFrees.is_empty instT andalso Frees.is_empty inst then th
  else
    let
      val namesT = Names.build (TFrees.fold (Names.add_set o #1 o #1) instT);
      val names = Names.build (Frees.fold (Names.add_set o #1 o #1) inst);

      val idx =
        (Thm.maxidx_of th
          |> TFrees.fold (Integer.max o Thm.maxidx_of_ctyp o #2) instT
          |> Frees.fold (Integer.max o Thm.maxidx_of_cterm o #2) inst) + 1;
      fun index ((a, A), b) = (((a, idx), A), b);

      val instT' =
        TVars.build (TFrees.fold (TVars.add o index) instT)
        |> not (Names.is_empty namesT) ? Thm.fold_atomic_ctyps {hyps = true}
            (fn tab => fn T => Term.is_TFree T andalso
              let val (a, S) = Term.dest_TFree T in
                Names.defined namesT a andalso
                not (TFrees.defined instT (a, S)) andalso
                not (TVars.defined tab ((a, idx), S))
              end)
            (fn cT =>
              let val (a, S) = Term.dest_TFree (Thm.typ_of cT)
              in TVars.add (((a, idx), S), cT) end) th;

      val inst_typ = Term_Subst.instantiateT_frees (TFrees.map (K Thm.typ_of) instT);
      val inst_ctyp =
        Thm.generalize_cterm (namesT, Names.empty) idx #>
        Thm.instantiate_cterm (instT', Vars.empty);

      val inst' =
        Vars.build (Frees.fold (Vars.add o index) inst)
        |> not (Names.is_empty names) ? Thm.fold_atomic_cterms {hyps = true}
            (fn tab => fn t => Term.is_Free t andalso
              let val (x, T) = Term.dest_Free t in
                Names.defined names x andalso
                  let val U = inst_typ T
                  in not (Frees.defined inst (x, U)) andalso not (Vars.defined tab ((x, idx), U)) end
              end)
            (fn ct =>
              let val (x, T) = Term.dest_Free (Thm.term_of ct)
              in Vars.add (((x, idx), inst_typ T), inst_ctyp ct) end) th;

      val hyps = Thm.chyps_of th;
    in
      th
      |> fold_rev Thm.implies_intr hyps
      |> Thm.generalize (namesT, names) idx
      |> Thm.instantiate (instT', inst')
      |> assume_prems (length hyps)
    end;


(* instantiate by left-to-right occurrence of variables *)

fun instantiate' cTs cts thm =
  let
    fun err msg =
      raise TYPE ("instantiate': " ^ msg,
        map_filter (Option.map Thm.typ_of) cTs,
        map_filter (Option.map Thm.term_of) cts);

    fun zip_vars xs ys =
      zip_options xs ys handle ListPair.UnequalLengths =>
        err "more instantiations than variables in thm";

    val instT = zip_vars (build_rev (Thm.fold_terms {hyps = false} Term.add_tvars thm)) cTs;
    val thm' = Thm.instantiate (TVars.make instT, Vars.empty) thm;
    val inst = zip_vars (build_rev (Thm.fold_terms {hyps = false} Term.add_vars thm')) cts;
  in Thm.instantiate (TVars.empty, Vars.make inst) thm' end;


(* implicit generalization over variables -- canonical order *)

fun forall_intr_vars th =
  let val vars = Cterms.build (Cterms.add_vars th)
  in fold_rev Thm.forall_intr (Cterms.list_set vars) th end;

fun forall_intr_frees th =
  let
    val fixed =
      Frees.build
       (fold Frees.add_frees (Thm.terms_of_tpairs (Thm.tpairs_of th)) #>
        fold Frees.add_frees (Thm.hyps_of th));
    fun guard t = Term.is_Free t andalso not (Frees.defined fixed (Term.dest_Free t));
    val frees = Cterms.build (th |> Thm.fold_atomic_cterms {hyps = false} (K guard) Cterms.add_set);
  in fold_rev Thm.forall_intr (Cterms.list_set frees) th end;


(* unvarify_global: global schematic variables *)

fun unvarify_global thy th =
  let
    val prop = Thm.full_prop_of th;
    val _ = map Logic.unvarify_global (prop :: Thm.hyps_of th)
      handle TERM (msg, _) => raise THM (msg, 0, [th]);

    val cert = Thm.global_cterm_of thy;
    val certT = Thm.global_ctyp_of thy;

    val instT =
      TVars.build (prop |> (Term.fold_types o Term.fold_atyps)
        (fn T => fn instT =>
          (case T of
            TVar (v as ((a, _), S)) =>
              if TVars.defined instT v then instT
              else TVars.add (v, TFree (a, S)) instT
          | _ => instT)));
    val cinstT = TVars.map (K certT) instT;
    val cinst =
      Vars.build (prop |> Term.fold_aterms
        (fn t => fn inst =>
          (case t of
            Var ((x, i), T) =>
              let val T' = Term_Subst.instantiateT instT T
              in Vars.add (((x, i), T'), cert (Free ((x, T')))) inst end
          | _ => inst)));
  in Thm.instantiate (cinstT, cinst) th end;

fun unvarify_axiom thy = unvarify_global thy o Thm.axiom thy;


(* user renaming of parameters in a subgoal *)

(*The names, if distinct, are used for the innermost parameters of subgoal i;
  preceding parameters may be renamed to make all parameters distinct.*)
fun rename_params_rule (names, i) st =
  let
    val (_, Bs, Bi, C) = Thm.dest_state (st, i);
    val params = map #1 (Logic.strip_params Bi);
    val short = length params - length names;
    val names' =
      if short < 0 then error "More names than parameters in subgoal!"
      else Name.variant_list names (take short params) @ names;
    val free_names = Term.fold_aterms (fn Free (x, _) => insert (op =) x | _ => I) Bi [];
    val Bi' = Logic.list_rename_params names' Bi;
  in
    (case duplicates (op =) names of
      a :: _ => (warning ("Can't rename.  Bound variables not distinct: " ^ a); st)
    | [] =>
      (case inter (op =) names free_names of
        a :: _ => (warning ("Can't rename.  Bound/Free variable clash: " ^ a); st)
      | [] => Thm.renamed_prop (Logic.list_implies (Bs @ [Bi'], C)) st))
  end;


(* preservation of bound variable names *)

fun rename_boundvars pat obj th =
  (case Term.rename_abs pat obj (Thm.prop_of th) of
    NONE => th
  | SOME prop' => Thm.renamed_prop prop' th);



(** specification primitives **)

(* rules *)

fun stripped_sorts thy t =
  let
    val tfrees = build_rev (Term.add_tfrees t);
    val tfrees' = map (fn a => (a, [])) (Name.variant_list [] (map #1 tfrees));
    val recover =
      map2 (fn (a', S') => fn (a, S) => (((a', 0), S'), Thm.global_ctyp_of thy (TVar ((a, 0), S))))
        tfrees' tfrees;
    val strip = map (apply2 TFree) (tfrees ~~ tfrees');
    val t' =
      (Term.map_types o Term.map_atyps_same)
        (Same.function_eq (op =) (perhaps (AList.lookup (op =) strip))) t;
  in (strip, recover, t') end;

fun add_axiom ctxt (b, prop) thy =
  let
    val _ = Sign.no_vars ctxt prop;
    val (strip, recover, prop') = stripped_sorts thy prop;
    val constraints = map (fn (TFree (_, S), T) => (T, S)) strip;
    val of_sorts = maps (fn (T as TFree (_, S), _) => of_sort (Thm.ctyp_of ctxt T, S)) strip;

    val thy' = thy
      |> Theory.add_axiom ctxt (b, Logic.list_implies (maps Logic.mk_of_sort constraints, prop'));
    val axm_name = Sign.full_name thy' b;
    val axm' = Thm.axiom thy' axm_name;
    val thm =
      Thm.instantiate (TVars.make recover, Vars.empty) axm'
      |> unvarify_global thy'
      |> fold elim_implies of_sorts;
  in ((axm_name, thm), thy') end;

fun add_axiom_global arg thy = add_axiom (Syntax.init_pretty_global thy) arg thy;

fun add_def (context as (ctxt, _)) unchecked overloaded (b, prop) thy =
  let
    val _ = Sign.no_vars ctxt prop;
    val prems = map (Thm.cterm_of ctxt) (Logic.strip_imp_prems prop);
    val (_, recover, concl') = stripped_sorts thy (Logic.strip_imp_concl prop);

    val thy' = Theory.add_def context unchecked overloaded (b, concl') thy;
    val axm_name = Sign.full_name thy' b;
    val axm' = Thm.axiom thy' axm_name;
    val thm =
      Thm.instantiate (TVars.make recover, Vars.empty) axm'
      |> unvarify_global thy'
      |> fold_rev Thm.implies_intr prems;
  in ((axm_name, thm), thy') end;

fun add_def_global unchecked overloaded arg thy =
  add_def (Defs.global_context thy) unchecked overloaded arg thy;



(** theorem tags **)

(* add / delete tags *)

fun tag_rule tg = Thm.map_tags (insert (op =) tg);
fun untag_rule s = Thm.map_tags (filter_out (fn (s', _) => s = s'));


(* free dummy thm -- for abstract closure *)

val free_dummyN = "free_dummy";
fun is_free_dummy thm = Properties.defined (Thm.get_tags thm) free_dummyN;
val tag_free_dummy = tag_rule (free_dummyN, "");


(* def_name *)

fun def_name c = c ^ "_def";

fun def_name_optional c "" = def_name c
  | def_name_optional _ name = name;

val def_binding = Binding.map_name def_name #> Binding.reset_pos;
fun def_binding_optional b name = if Binding.is_empty name then def_binding b else name;
fun make_def_binding cond b = if cond then def_binding b else Binding.empty;


(* unofficial theorem names *)

fun the_name_hint thm =
  let val thm_name = Thm_Name.parse (Properties.get_string (Thm.get_tags thm) Markup.nameN)
  in
    if Thm_Name.is_empty thm_name
    then raise THM ("Thm.the_name_hint: missing name", 0, [thm])
    else thm_name
  end;

fun has_name_hint thm = can the_name_hint thm;
fun get_name_hint thm = try the_name_hint thm |> the_default ("??.unknown", 0);

fun put_name_hint name = untag_rule Markup.nameN #> tag_rule (Markup.nameN, Thm_Name.print name);


(* theorem kinds *)

val theoremK = "theorem";

fun legacy_get_kind thm = Properties.get_string (Thm.get_tags thm) Markup.kindN;

fun kind_rule k = tag_rule (Markup.kindN, k) o untag_rule Markup.kindN;



(** attributes **)

(*attributes subsume any kind of rules or context modifiers*)
type attribute = Context.generic * thm -> Context.generic option * thm option;

type binding = binding * attribute list;

fun rule_attribute ths f (x, th) =
  (NONE,
    (case find_first is_free_dummy (th :: ths) of
      SOME th' => SOME th'
    | NONE => SOME (f x th)));

fun declaration_attribute f (x, th) =
  (if is_free_dummy th then NONE else SOME (f th x), NONE);

fun mixed_attribute f (x, th) =
  let val (x', th') = f (x, th) in (SOME x', SOME th') end;

fun apply_attribute (att: attribute) th x =
  let val (x', th') = att (x, check_hyps x (Thm.transfer'' x th))
  in (the_default th th', the_default x x') end;

fun attribute_declaration att th x = #2 (apply_attribute att th x);

fun apply_attributes mk dest =
  let
    fun app [] th x = (th, x)
      | app (att :: atts) th x = apply_attribute att th (mk x) ||> dest |-> app atts;
  in app end;

val theory_attributes = apply_attributes Context.Theory Context.the_theory;
val proof_attributes = apply_attributes Context.Proof Context.the_proof;

fun no_attributes x = (x, []);
fun simple_fact x = [(x, [])];

fun tag tg = rule_attribute [] (K (tag_rule tg));
fun untag s = rule_attribute [] (K (untag_rule s));
fun kind k = rule_attribute [] (K (k <> "" ? kind_rule k));



(** forked proofs **)

structure Proofs = Theory_Data
(
  type T = thm list lazy Inttab.table;
  val empty = Inttab.empty;
  val merge = Inttab.merge (K true);
);

fun reset_proofs thy =
  if Inttab.is_empty (Proofs.get thy) then NONE
  else SOME (Proofs.put Inttab.empty thy);

val _ = Theory.setup (Theory.at_begin reset_proofs);

fun register_proofs ths thy =
  let val entry = (serial (), Lazy.map_finished (map Thm.trim_context) ths)
  in (Proofs.map o Inttab.update) entry thy end;

fun force_proofs thy =
  Proofs.get thy |> Inttab.dest |> maps (map (Thm.transfer thy) o Lazy.force o #2);

val consolidate_theory = Thm.consolidate o force_proofs;

fun expose_theory thy =
  if Proofterm.export_enabled ()
  then Thm.expose_proofs thy (force_proofs thy) else ();



(** print theorems **)

(* options *)

val show_consts = Config.declare_option_bool ("show_consts", \<^here>);
val show_hyps = Config.declare_bool ("show_hyps", \<^here>) (K false);
val show_tags = Config.declare_bool ("show_tags", \<^here>) (K false);


(* pretty_thm etc. *)

fun pretty_tag (name, arg) = Pretty.strs [name, quote arg];
val pretty_tags = Pretty.list "[" "]" o map pretty_tag;

fun pretty_thm_raw ctxt {quote, show_hyps = show_hyps'} raw_th =
  let
    val show_tags = Config.get ctxt show_tags;
    val show_hyps = Config.get ctxt show_hyps;

    val th = raw_th
      |> perhaps (try (Thm.transfer' ctxt))
      |> perhaps (try Thm.strip_shyps);

    val hyps = if show_hyps then Thm.hyps_of th else undeclared_hyps (Context.Proof ctxt) th;
    val extra_shyps = extra_shyps' ctxt th;
    val tags = Thm.get_tags th;
    val tpairs = Thm.tpairs_of th;

    val q = if quote then Pretty.quote else I;
    val prt_term = q o Syntax.pretty_term ctxt;


    val hlen = length extra_shyps + length hyps + length tpairs;
    val hsymbs =
      if hlen = 0 then []
      else if show_hyps orelse show_hyps' then
        [Pretty.brk 2, Pretty.list "[" "]"
          (map (q o Pretty.block o Syntax.pretty_flexpair ctxt) tpairs @ map prt_term hyps @
           map (Syntax.pretty_sort ctxt) extra_shyps)]
      else [Pretty.brk 2, Pretty.str ("[" ^ replicate_string hlen "." ^ "]")];
    val tsymbs =
      if null tags orelse not show_tags then []
      else [Pretty.brk 1, pretty_tags tags];
  in Pretty.block (prt_term (Thm.prop_of th) :: (hsymbs @ tsymbs)) end;

fun pretty_thm ctxt = pretty_thm_raw ctxt {quote = false, show_hyps = true};
fun pretty_thm_item ctxt th = Pretty.item [pretty_thm ctxt th];

fun pretty_thm_global thy =
  pretty_thm_raw (Syntax.init_pretty_global thy) {quote = false, show_hyps = false};

val string_of_thm = Pretty.string_of oo pretty_thm;
val string_of_thm_global = Pretty.string_of oo pretty_thm_global;


open Thm;

end;

structure Basic_Thm: BASIC_THM = Thm;
open Basic_Thm;
