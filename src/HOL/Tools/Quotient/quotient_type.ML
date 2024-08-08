(*  Title:      HOL/Tools/Quotient/quotient_type.ML
    Author:     Cezary Kaliszyk and Christian Urban

Definition of a quotient type.
*)

signature QUOTIENT_TYPE =
sig
  val add_quotient_type: {overloaded: bool} ->
    ((string list * binding * mixfix) * (typ * term * bool) *
      ((binding * binding) option * thm option)) * thm -> local_theory ->
      Quotient_Info.quotients * local_theory
  val quotient_type:  {overloaded: bool} ->
    (string list * binding * mixfix) * (typ * term * bool) *
      ((binding * binding) option * thm option) -> Proof.context -> Proof.state
  val quotient_type_cmd:  {overloaded: bool} ->
    (((((string list * binding) * mixfix) * string) * (bool * string)) *
      (binding * binding) option) * (Facts.ref * Token.src list) option ->
      Proof.context -> Proof.state
end;

structure Quotient_Type: QUOTIENT_TYPE =
struct


(*** definition of quotient types ***)

val mem_def1 = @{lemma "y \<in> Collect S \<Longrightarrow> S y" by simp}
val mem_def2 = @{lemma "S y \<Longrightarrow> y \<in> Collect S" by simp}

(* constructs the term {c. EX (x::rty). rel x x \<and> c = Collect (rel x)} *)
fun typedef_term rel rty lthy =
  let
    val [x, c] =
      [("x", rty), ("c", HOLogic.mk_setT rty)]
      |> Variable.variant_frees lthy [rel]
      |> map Free
  in
    HOLogic.Collect_const (HOLogic.mk_setT rty) $ (lambda c (HOLogic.exists_const rty $
        lambda x (HOLogic.mk_conj (rel $ x $ x,
        HOLogic.mk_eq (c, HOLogic.Collect_const rty $ (rel $ x))))))
  end


(* makes the new type definitions and proves non-emptyness *)
fun typedef_make overloaded (vs, qty_name, mx, rel, rty) equiv_thm lthy =
  let
    fun typedef_tac ctxt =
      EVERY1 (map (resolve_tac ctxt o single) [@{thm part_equivp_typedef}, equiv_thm])
  in
    Typedef.add_typedef overloaded (qty_name, map (rpair dummyS) vs, mx)
      (typedef_term rel rty lthy) NONE typedef_tac lthy
  end


(* tactic to prove the quot_type theorem for the new type *)
fun typedef_quot_type_tac ctxt equiv_thm ((_, typedef_info): Typedef.info) =
  let
    val rep_thm = #Rep typedef_info RS mem_def1
    val rep_inv = #Rep_inverse typedef_info
    val abs_inv = #Abs_inverse typedef_info
    val rep_inj = #Rep_inject typedef_info
  in
    (resolve_tac ctxt @{thms quot_type.intro} THEN' RANGE [
      resolve_tac ctxt [equiv_thm],
      resolve_tac ctxt [rep_thm],
      resolve_tac ctxt [rep_inv],
      resolve_tac ctxt [abs_inv] THEN' resolve_tac ctxt [mem_def2] THEN' assume_tac ctxt,
      resolve_tac ctxt [rep_inj]]) 1
  end

(* proves the quot_type theorem for the new type *)
fun typedef_quot_type_thm (rel, abs, rep, equiv_thm, typedef_info) lthy =
  let
    val \<^Type>\<open>fun A _\<close> = fastype_of rel
    val \<^Type>\<open>fun _ B\<close> = fastype_of abs
  in
    Goal.prove lthy [] [] (HOLogic.mk_Trueprop (\<^Const>\<open>quot_type A B for rel abs rep\<close>))
      (fn {context = ctxt, ...} => typedef_quot_type_tac ctxt equiv_thm typedef_info)
  end

open Lifting_Util

infix 0 MRSL

fun define_cr_rel equiv_thm abs_fun lthy =
  let
    fun force_type_of_rel rel forced_ty =
      let
        val thy = Proof_Context.theory_of lthy
        val rel_ty = (domain_type o fastype_of) rel
        val ty_inst = Sign.typ_match thy (rel_ty, forced_ty) Vartab.empty
      in
        Envir.subst_term_types ty_inst rel
      end

    val (rty, qty) = (dest_funT o fastype_of) abs_fun
    val abs_fun_graph = HOLogic.mk_eq(abs_fun $ Bound 1, Bound 0)
    val Abs_body =
      (case (HOLogic.dest_Trueprop o Thm.prop_of) equiv_thm of
        \<^Const_>\<open>equivp _ for _\<close> => abs_fun_graph
      | \<^Const_>\<open>part_equivp _ for rel\<close> =>
          HOLogic.mk_conj (force_type_of_rel rel rty $ Bound 1 $ Bound 1, abs_fun_graph)
      | _ => error "unsupported equivalence theorem")
    val def_term = Abs ("x", rty, Abs ("y", qty, Abs_body));
    val qty_name = Binding.name (Long_Name.base_name (dest_Type_name qty))
    val cr_rel_name = Binding.prefix_name "cr_" qty_name
    val (fixed_def_term, lthy') = yield_singleton (Variable.importT_terms) def_term lthy
    val ((_, (_ , def_thm)), lthy'') =
      Local_Theory.define ((cr_rel_name, NoSyn), ((Thm.def_binding cr_rel_name, []), fixed_def_term)) lthy'
  in
    (def_thm, lthy'')
  end;

fun setup_lifting_package quot3_thm equiv_thm opt_par_thm lthy =
  let
    val (_ $ _ $ abs_fun $ _) = (HOLogic.dest_Trueprop o Thm.prop_of) quot3_thm
    val (T_def, lthy') = define_cr_rel equiv_thm abs_fun lthy
    val (rty, qty) = (dest_funT o fastype_of) abs_fun
    val qty_name = Binding.name (Long_Name.base_name (dest_Type_name qty))
    val quotient_thm_name = Binding.prefix_name "Quotient_" qty_name
    val (reflp_thm, quot_thm) =
      (case (HOLogic.dest_Trueprop o Thm.prop_of) equiv_thm of
        \<^Const_>\<open>equivp _ for _\<close> =>
          (SOME (equiv_thm RS @{thm equivp_reflp2}),
            [quot3_thm, T_def, equiv_thm] MRSL @{thm Quotient3_to_Quotient_equivp})
      | \<^Const_>\<open>part_equivp _ for _\<close> =>
          (NONE, [quot3_thm, T_def] MRSL @{thm Quotient3_to_Quotient})
      | _ => error "unsupported equivalence theorem")
    val config = { notes = true }
  in
    lthy'
      |> Lifting_Setup.setup_by_quotient config quot_thm reflp_thm opt_par_thm
      |> snd
      |> (snd oo Local_Theory.note) ((quotient_thm_name, []), [quot_thm])
  end

fun init_quotient_infr quot_thm equiv_thm opt_par_thm lthy =
  let
    val (_ $ rel $ abs $ rep) = (HOLogic.dest_Trueprop o Thm.prop_of) quot_thm
    val (qtyp, rtyp) = (dest_funT o fastype_of) rep
    val qty_full_name = dest_Type_name qtyp
    fun quotients phi =
      Quotient_Info.transform_quotients phi
        {qtyp = qtyp, rtyp = rtyp, equiv_rel = rel, equiv_thm = equiv_thm,
          quot_thm = quot_thm}
    fun abs_rep phi =
      Quotient_Info.transform_abs_rep phi {abs = abs, rep = rep}
  in
    lthy
    |> Local_Theory.declaration {syntax = false, pervasive = true, pos = \<^here>} (fn phi =>
        Quotient_Info.update_quotients (qty_full_name, quotients phi) #>
        Quotient_Info.update_abs_rep (qty_full_name, abs_rep phi))
    |> setup_lifting_package quot_thm equiv_thm opt_par_thm
  end

(* main function for constructing a quotient type *)
fun add_quotient_type overloaded
    (((vs, qty_name, mx), (rty, rel, partial), (opt_morphs, opt_par_thm)), equiv_thm) lthy =
  let
    val part_equiv =
      if partial
      then equiv_thm
      else equiv_thm RS @{thm equivp_implies_part_equivp}

    (* generates the typedef *)
    val ((_, typedef_info), lthy1) =
      typedef_make overloaded (vs, qty_name, mx, rel, rty) part_equiv lthy

    (* abs and rep functions from the typedef *)
    val Abs_ty = #abs_type (#1 typedef_info)
    val Rep_ty = #rep_type (#1 typedef_info)
    val Abs_name = #Abs_name (#1 typedef_info)
    val Rep_name = #Rep_name (#1 typedef_info)
    val Abs_const = Const (Abs_name, Rep_ty --> Abs_ty)
    val Rep_const = Const (Rep_name, Abs_ty --> Rep_ty)

    (* more useful abs and rep definitions *)
    val abs_trm = \<^Const>\<open>quot_type.abs rty Abs_ty\<close> $ rel $ Abs_const
    val rep_trm = \<^Const>\<open>quot_type.rep Abs_ty rty\<close> $ Rep_const
    val (rep_name, abs_name) =
      (case opt_morphs of
        NONE => (Binding.prefix_name "rep_" qty_name, Binding.prefix_name "abs_" qty_name)
      | SOME morphs => morphs)

    val ((_, (_, abs_def)), lthy2) = lthy1
      |> Local_Theory.define ((abs_name, NoSyn), ((Thm.def_binding abs_name, []), abs_trm))
    val ((_, (_, rep_def)), lthy3) = lthy2
      |> Local_Theory.define ((rep_name, NoSyn), ((Thm.def_binding rep_name, []), rep_trm))

    (* quot_type theorem *)
    val quot_thm = typedef_quot_type_thm (rel, Abs_const, Rep_const, part_equiv, typedef_info) lthy3

    (* quotient theorem *)
    val quotient_thm_name = Binding.prefix_name "Quotient3_" qty_name
    val quotient_thm =
      (quot_thm RS @{thm quot_type.Quotient})
      |> fold_rule lthy3 [abs_def, rep_def]

    (* name equivalence theorem *)
    val equiv_thm_name = Binding.suffix_name "_equivp" qty_name

    (* storing the quotients *)
    val quotients = {qtyp = Abs_ty, rtyp = rty, equiv_rel = rel, equiv_thm = equiv_thm,
      quot_thm = quotient_thm}

    val lthy4 = lthy3
      |> init_quotient_infr quotient_thm equiv_thm opt_par_thm
      |> (snd oo Local_Theory.note)
        ((equiv_thm_name,
          if partial then [] else @{attributes [quot_equiv]}),
          [equiv_thm])
      |> (snd oo Local_Theory.note)
        ((quotient_thm_name, @{attributes [quot_thm]}), [quotient_thm])
  in
    (quotients, lthy4)
  end


(* sanity checks for the quotient type specifications *)
fun sanity_check ((vs, qty_name, _), (rty, rel, _), _) =
  let
    val rty_tfreesT = map fst (Term.add_tfreesT rty [])
    val rel_tfrees = map fst (Term.add_tfrees rel [])
    val rel_frees = map fst (Term.add_frees rel [])
    val rel_vars = Term.add_vars rel []
    val rel_tvars = Term.add_tvars rel []
    val qty_str = Binding.print qty_name ^ ": "

    val illegal_rel_vars =
      if null rel_vars andalso null rel_tvars then []
      else [qty_str ^ "illegal schematic variable(s) in the relation."]

    val dup_vs =
      (case duplicates (op =) vs of
        [] => []
      | dups => [qty_str ^ "duplicate type variable(s) on the lhs: " ^ commas_quote dups])

    val extra_rty_tfrees =
      (case subtract (op =) vs rty_tfreesT of
        [] => []
      | extras => [qty_str ^ "extra type variable(s) on the lhs: " ^ commas_quote extras])

    val extra_rel_tfrees =
      (case subtract (op =) vs rel_tfrees of
        [] => []
      | extras => [qty_str ^ "extra type variable(s) in the relation: " ^ commas_quote extras])

    val illegal_rel_frees =
      (case rel_frees of
        [] => []
      | xs => [qty_str ^ "illegal variable(s) in the relation: " ^ commas_quote xs])

    val errs = illegal_rel_vars @ dup_vs @ extra_rty_tfrees @ extra_rel_tfrees @ illegal_rel_frees
  in
    if null errs then () else error (cat_lines errs)
  end

(* check for existence of map functions *)
fun map_check ctxt (_, (rty, _, _), _) =
  let
    fun map_check_aux rty warns =
      (case rty of
        Type (_, []) => warns
      | Type (s, _) =>
          if Symtab.defined (Functor.entries ctxt) s then warns else s :: warns
      | _ => warns)

    val warns = map_check_aux rty []
  in
    if null warns then ()
    else warning ("No map function defined for " ^ commas warns ^
      ". This will cause problems later on.")
  end


(*** interface and syntax setup ***)

(* the ML-interface takes a list of tuples consisting of:

 - the name of the quotient type
 - its free type variables (first argument)
 - its mixfix annotation
 - the type to be quotient
 - the partial flag (a boolean)
 - the relation according to which the type is quotient
 - optional names of morphisms (rep/abs)
 - flag if code should be generated by Lifting package

 it opens a proof-state in which one has to show that the
 relations are equivalence relations
*)

fun quotient_type overloaded quot lthy =
  let
    (* sanity check *)
    val _ = sanity_check quot
    val _ = map_check lthy quot

    val (rty, rel, partial) = #2 quot
    val const = if partial then \<^Const>\<open>part_equivp rty\<close> else \<^Const>\<open>equivp rty\<close>
    val goal = HOLogic.mk_Trueprop (const $ rel)

    fun after_qed [[thm]] = (snd oo add_quotient_type overloaded) (quot, thm)
  in
    Proof.theorem NONE after_qed [[(goal, [])]] lthy
  end

fun quotient_type_cmd overloaded spec lthy =
  let
    fun parse_spec ((((((vs, qty_name), mx), rty_str), (partial, rel_str)), opt_morphs), opt_par_xthm) lthy =
      let
        val rty = Syntax.read_typ lthy rty_str
        val tmp_lthy1 = Variable.declare_typ rty lthy
        val rel =
          Syntax.parse_term tmp_lthy1 rel_str
          |> Type.constraint (rty --> rty --> \<^typ>\<open>bool\<close>)
          |> Syntax.check_term tmp_lthy1
        val tmp_lthy2 = Variable.declare_term rel tmp_lthy1
        val opt_par_thm = Option.map (singleton (Attrib.eval_thms lthy)) opt_par_xthm
      in
        (((vs, qty_name, mx), (rty, rel, partial), (opt_morphs, opt_par_thm)), tmp_lthy2)
      end

    val (spec', _) = parse_spec spec lthy
  in
    quotient_type overloaded spec' lthy
  end


(* command syntax *)

val _ =
  Outer_Syntax.local_theory_to_proof \<^command_keyword>\<open>quotient_type\<close>
    "quotient type definitions (require equivalence proofs)"
      (* FIXME Parse.type_args_constrained and standard treatment of sort constraints *)
      (Parse_Spec.overloaded -- (Parse.type_args -- Parse.binding --
        Parse.opt_mixfix -- (\<^keyword>\<open>=\<close> |-- Parse.typ) -- (\<^keyword>\<open>/\<close> |--
          Scan.optional (Parse.reserved "partial" -- \<^keyword>\<open>:\<close> >> K true) false -- Parse.term) --
        Scan.option (\<^keyword>\<open>morphisms\<close> |-- Parse.!!! (Parse.binding -- Parse.binding)) --
        Scan.option (\<^keyword>\<open>parametric\<close> |-- Parse.!!! Parse.thm))
      >> (fn (overloaded, spec) => quotient_type_cmd {overloaded = overloaded} spec))

end
