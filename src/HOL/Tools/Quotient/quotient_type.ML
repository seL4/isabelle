(*  Title:      HOL/Tools/Quotient/quotient_type.ML
    Author:     Cezary Kaliszyk and Christian Urban

Definition of a quotient type.
*)

signature QUOTIENT_TYPE =
sig
  val can_generate_code_cert: thm -> bool
  
  val add_quotient_type: ((string list * binding * mixfix) * (typ * term * bool) * 
    ((binding * binding) option)) * thm -> local_theory -> Quotient_Info.quotients * local_theory

  val quotient_type: ((string list * binding * mixfix) * (typ * term * bool) * 
    ((binding * binding) option)) list -> Proof.context -> Proof.state

  val quotient_type_cmd: (((((string list * binding) * mixfix) * string) * (bool * string)) *
    (binding * binding) option) list -> Proof.context -> Proof.state
end;

structure Quotient_Type: QUOTIENT_TYPE =
struct


(*** definition of quotient types ***)

val mem_def1 = @{lemma "y : Collect S ==> S y" by simp}
val mem_def2 = @{lemma "S y ==> y : Collect S" by simp}

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
fun typedef_make (vs, qty_name, mx, rel, rty) equiv_thm lthy =
  let
    val typedef_tac =
      EVERY1 (map rtac [@{thm part_equivp_typedef}, equiv_thm])
  in
    Typedef.add_typedef false NONE (qty_name, map (rpair dummyS) vs, mx)
      (typedef_term rel rty lthy) NONE typedef_tac lthy
  end


(* tactic to prove the quot_type theorem for the new type *)
fun typedef_quot_type_tac equiv_thm ((_, typedef_info): Typedef.info) =
  let
    val rep_thm = #Rep typedef_info RS mem_def1
    val rep_inv = #Rep_inverse typedef_info
    val abs_inv = #Abs_inverse typedef_info
    val rep_inj = #Rep_inject typedef_info
  in
    (rtac @{thm quot_type.intro} THEN' RANGE [
      rtac equiv_thm,
      rtac rep_thm,
      rtac rep_inv,
      rtac abs_inv THEN' rtac mem_def2 THEN' atac,
      rtac rep_inj]) 1
  end

(* proves the quot_type theorem for the new type *)
fun typedef_quot_type_thm (rel, abs, rep, equiv_thm, typedef_info) lthy =
  let
    val quot_type_const = Const (@{const_name "quot_type"},
      fastype_of rel --> fastype_of abs --> fastype_of rep --> @{typ bool})
    val goal = HOLogic.mk_Trueprop (quot_type_const $ rel $ abs $ rep)
  in
    Goal.prove lthy [] [] goal
      (K (typedef_quot_type_tac equiv_thm typedef_info))
  end
   
fun can_generate_code_cert quot_thm  =
   case Quotient_Term.get_rel_from_quot_thm quot_thm of
      Const (@{const_name HOL.eq}, _) => true
      | Const (@{const_name Lifting.invariant}, _) $ _  => true
      | _ => false

fun define_abs_type quot_thm lthy =
  if can_generate_code_cert quot_thm then
    let
      val abs_type_thm = quot_thm RS @{thm Quotient3_abs_rep}
      val add_abstype_attribute = 
          Thm.declaration_attribute (fn thm => Context.mapping (Code.add_abstype thm) I)
        val add_abstype_attrib = Attrib.internal (K add_abstype_attribute);
    in
      lthy
        |> (snd oo Local_Theory.note) ((Binding.empty, [add_abstype_attrib]), [abs_type_thm])
    end
  else
    lthy

infix 0 MRSL

fun ants MRSL thm = fold (fn rl => fn thm => rl RS thm) ants thm

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
    val Abs_body = (case (HOLogic.dest_Trueprop o prop_of) equiv_thm of
      Const (@{const_name equivp}, _) $ _ => abs_fun_graph
      | Const (@{const_name part_equivp}, _) $ rel => 
        HOLogic.mk_conj (force_type_of_rel rel rty $ Bound 1 $ Bound 1, abs_fun_graph)
      | _ => error "unsupported equivalence theorem"
      )
    val def_term = Abs ("x", rty, Abs ("y", qty, Abs_body));
    val qty_name = (fst o dest_Type) qty
    val cr_rel_name = Binding.prefix_name "cr_" (Binding.qualified_name qty_name)  
    val (fixed_def_term, lthy') = yield_singleton (Variable.importT_terms) def_term lthy
    val ((_, (_ , def_thm)), lthy'') =
      Local_Theory.define ((cr_rel_name, NoSyn), ((Thm.def_binding cr_rel_name, []), fixed_def_term)) lthy'
  in
    (def_thm, lthy'')
  end;

fun setup_lifting_package quot3_thm equiv_thm lthy =
  let
    val (_ $ _ $ abs_fun $ _) = (HOLogic.dest_Trueprop o prop_of) quot3_thm
    val (T_def, lthy') = define_cr_rel equiv_thm abs_fun lthy
    val (rty, qty) = (dest_funT o fastype_of) abs_fun
    val qty_name = (fst o dest_Type) qty
    val quotient_thm_name = Binding.prefix_name "Quotient_" (Binding.qualified_name qty_name) 
    val (reflp_thm, quot_thm) = (case (HOLogic.dest_Trueprop o prop_of) equiv_thm of
      Const (@{const_name equivp}, _) $ _ =>
        (SOME (equiv_thm RS @{thm equivp_reflp2}),
         [quot3_thm, T_def, equiv_thm] MRSL @{thm Quotient3_to_Quotient_equivp})
      | Const (@{const_name part_equivp}, _) $ _ =>
        (NONE,
        [quot3_thm, T_def] MRSL @{thm Quotient3_to_Quotient})
      | _ => error "unsupported equivalence theorem"
      )
  in
    lthy'
      |> Lifting_Setup.setup_by_quotient false quot_thm reflp_thm
      |> (snd oo Local_Theory.note) ((quotient_thm_name, []), [quot_thm])
  end

fun init_quotient_infr quot_thm equiv_thm lthy =
  let
    val (_ $ rel $ abs $ rep) = (HOLogic.dest_Trueprop o prop_of) quot_thm
    val (qtyp, rtyp) = (dest_funT o fastype_of) rep
    val qty_full_name = (fst o dest_Type) qtyp
    val quotients = {qtyp = qtyp, rtyp = rtyp, equiv_rel = rel, equiv_thm = equiv_thm, 
      quot_thm = quot_thm }
    fun quot_info phi = Quotient_Info.transform_quotients phi quotients
    val abs_rep = {abs = abs, rep = rep}
    fun abs_rep_info phi = Quotient_Info.transform_abs_rep phi abs_rep
  in
    lthy
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Quotient_Info.update_quotients qty_full_name (quot_info phi)
          #> Quotient_Info.update_abs_rep qty_full_name (abs_rep_info phi))
      |> define_abs_type quot_thm
      |> setup_lifting_package quot_thm equiv_thm
  end

(* main function for constructing a quotient type *)
fun add_quotient_type (((vs, qty_name, mx), (rty, rel, partial), opt_morphs), equiv_thm) lthy =
  let
    val part_equiv =
      if partial
      then equiv_thm
      else equiv_thm RS @{thm equivp_implies_part_equivp}

    (* generates the typedef *)
    val ((_, typedef_info), lthy1) =
      typedef_make (vs, qty_name, mx, rel, rty) part_equiv lthy

    (* abs and rep functions from the typedef *)
    val Abs_ty = #abs_type (#1 typedef_info)
    val Rep_ty = #rep_type (#1 typedef_info)
    val Abs_name = #Abs_name (#1 typedef_info)
    val Rep_name = #Rep_name (#1 typedef_info)
    val Abs_const = Const (Abs_name, Rep_ty --> Abs_ty)
    val Rep_const = Const (Rep_name, Abs_ty --> Rep_ty)

    (* more useful abs and rep definitions *)
    val abs_const = Const (@{const_name quot_type.abs},
      (rty --> rty --> @{typ bool}) --> (Rep_ty --> Abs_ty) --> rty --> Abs_ty)
    val rep_const = Const (@{const_name quot_type.rep}, (Abs_ty --> Rep_ty) --> Abs_ty --> rty)
    val abs_trm = abs_const $ rel $ Abs_const
    val rep_trm = rep_const $ Rep_const
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
      |> fold_rule [abs_def, rep_def]

    (* name equivalence theorem *)
    val equiv_thm_name = Binding.suffix_name "_equivp" qty_name

    (* storing the quotients *)
    val quotients = {qtyp = Abs_ty, rtyp = rty, equiv_rel = rel, equiv_thm = equiv_thm, 
      quot_thm = quotient_thm}

    val lthy4 = lthy3
      |> init_quotient_infr quotient_thm equiv_thm
      |> (snd oo Local_Theory.note)
        ((equiv_thm_name,
          if partial then [] else [Attrib.internal (K Quotient_Info.equiv_rules_add)]),
          [equiv_thm])
      |> (snd oo Local_Theory.note)
        ((quotient_thm_name, [Attrib.internal (K Quotient_Info.quotient_rules_add)]),
          [quotient_thm])
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
          if Symtab.defined (Enriched_Type.entries ctxt) s then warns else s :: warns
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

 it opens a proof-state in which one has to show that the
 relations are equivalence relations
*)

fun quotient_type quot_list lthy =
  let
    (* sanity check *)
    val _ = List.app sanity_check quot_list
    val _ = List.app (map_check lthy) quot_list

    fun mk_goal (rty, rel, partial) =
      let
        val equivp_ty = ([rty, rty] ---> @{typ bool}) --> @{typ bool}
        val const =
          if partial then @{const_name part_equivp} else @{const_name equivp}
      in
        HOLogic.mk_Trueprop (Const (const, equivp_ty) $ rel)
      end

    val goals = map (mk_goal o #2) quot_list

    fun after_qed [thms] = fold (snd oo add_quotient_type) (quot_list ~~ thms)
  in
    Proof.theorem NONE after_qed [map (rpair []) goals] lthy
  end

fun quotient_type_cmd specs lthy =
  let
    fun parse_spec (((((vs, qty_name), mx), rty_str), (partial, rel_str)), opt_morphs) lthy =
      let
        val rty = Syntax.read_typ lthy rty_str
        val tmp_lthy1 = Variable.declare_typ rty lthy
        val rel =
          Syntax.parse_term tmp_lthy1 rel_str
          |> Type.constraint (rty --> rty --> @{typ bool})
          |> Syntax.check_term tmp_lthy1
        val tmp_lthy2 = Variable.declare_term rel tmp_lthy1
      in
        (((vs, qty_name, mx), (rty, rel, partial), opt_morphs), tmp_lthy2)
      end

    val (spec', _) = fold_map parse_spec specs lthy
  in
    quotient_type spec' lthy
  end

val partial = Scan.optional (Parse.reserved "partial" -- @{keyword ":"} >> K true) false

val quotspec_parser =
  Parse.and_list1
    ((Parse.type_args -- Parse.binding) --
      (* FIXME Parse.type_args_constrained and standard treatment of sort constraints *)
      Parse.opt_mixfix -- (@{keyword "="} |-- Parse.typ) --
        (@{keyword "/"} |-- (partial -- Parse.term))  --
        Scan.option (@{keyword "morphisms"} |-- Parse.!!! (Parse.binding -- Parse.binding)))

val _ =
  Outer_Syntax.local_theory_to_proof @{command_spec "quotient_type"}
    "quotient type definitions (require equivalence proofs)"
      (quotspec_parser >> quotient_type_cmd)


end;
