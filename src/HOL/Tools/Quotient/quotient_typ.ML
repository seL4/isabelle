(*  Title:      HOL/Tools/Quotient/quotient_typ.ML
    Author:     Cezary Kaliszyk and Christian Urban

Definition of a quotient type.
*)

signature QUOTIENT_TYPE =
sig
  val add_quotient_type: ((string list * binding * mixfix) * (typ * term * bool)) * thm
    -> local_theory -> Quotient_Info.quotients * local_theory

  val quotient_type: ((string list * binding * mixfix) * (typ * term * bool)) list
    -> Proof.context -> Proof.state

  val quotient_type_cmd: ((((string list * binding) * mixfix) * string) * (bool * string)) list
    -> Proof.context -> Proof.state
end;

structure Quotient_Type: QUOTIENT_TYPE =
struct


(*** definition of quotient types ***)

val mem_def1 = @{lemma "y : Collect S ==> S y" by simp}
val mem_def2 = @{lemma "S y ==> y : Collect S" by simp}

(* constructs the term lambda (c::rty => bool). EX (x::rty). c = rel x *)
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
  (* FIXME: purely local typedef causes at the moment
     problems with type variables

    Typedef.add_typedef false NONE (qty_name, vs, mx)
      (typedef_term rel rty lthy) NONE typedef_tac lthy
  *)
  (* FIXME should really use local typedef here *)
    Local_Theory.background_theory_result
     (Typedef.add_typedef_global false NONE
       (qty_name, map (rpair dummyS) vs, mx)
         (typedef_term rel rty lthy)
           NONE typedef_tac) lthy
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

(* main function for constructing a quotient type *)
fun add_quotient_type (((vs, qty_name, mx), (rty, rel, partial)), equiv_thm) lthy =
  let
    val part_equiv =
      if partial
      then equiv_thm
      else equiv_thm RS @{thm equivp_implies_part_equivp}

    (* generates the typedef *)
    val ((qty_full_name, typedef_info), lthy1) =
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
    val abs_name = Binding.prefix_name "abs_" qty_name
    val rep_name = Binding.prefix_name "rep_" qty_name

    val ((abs_t, (_, abs_def)), lthy2) = lthy1
      |> Local_Theory.define ((abs_name, NoSyn), (Attrib.empty_binding, abs_trm))
    val ((rep_t, (_, rep_def)), lthy3) = lthy2
      |> Local_Theory.define ((rep_name, NoSyn), (Attrib.empty_binding, rep_trm))

    (* quot_type theorem *)
    val quot_thm = typedef_quot_type_thm (rel, Abs_const, Rep_const, part_equiv, typedef_info) lthy3

    (* quotient theorem *)
    val quotient_thm_name = Binding.prefix_name "Quotient_" qty_name
    val quotient_thm =
      (quot_thm RS @{thm quot_type.Quotient})
      |> fold_rule [abs_def, rep_def]

    (* name equivalence theorem *)
    val equiv_thm_name = Binding.suffix_name "_equivp" qty_name

    (* storing the quotients *)
    val quotients = {qtyp = Abs_ty, rtyp = rty, equiv_rel = rel, equiv_thm = equiv_thm}

    fun qinfo phi = Quotient_Info.transform_quotients phi quotients
    fun abs_rep phi = Quotient_Info.transform_abs_rep phi {abs = abs_t, rep = rep_t}

    val lthy4 = lthy3
      |> Local_Theory.declaration {syntax = false, pervasive = true}
        (fn phi => Quotient_Info.update_quotients qty_full_name (qinfo phi)
           #> Quotient_Info.update_abs_rep qty_full_name (abs_rep phi))
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
fun sanity_check ((vs, qty_name, _), (rty, rel, _)) =
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
fun map_check thy (_, (rty, _, _)) =
  let
    fun map_check_aux rty warns =
      (case rty of
        Type (_, []) => warns
      | Type (s, _) =>
          if is_some (Quotient_Info.lookup_quotmaps_global thy s) then warns else s :: warns
      | _ => warns)

    val warns = map_check_aux rty []
  in
    if null warns then ()
    else warning ("No map function defined for " ^ commas warns ^
      ". This will cause problems later on.")
  end



(*** interface and syntax setup ***)


(* the ML-interface takes a list of 5-tuples consisting of:

 - the name of the quotient type
 - its free type variables (first argument)
 - its mixfix annotation
 - the type to be quotient
 - the partial flag (a boolean)
 - the relation according to which the type is quotient

 it opens a proof-state in which one has to show that the
 relations are equivalence relations
*)

fun quotient_type quot_list lthy =
  let
    (* sanity check *)
    val _ = List.app sanity_check quot_list
    val _ = List.app (map_check (Proof_Context.theory_of lthy)) quot_list

    fun mk_goal (rty, rel, partial) =
      let
        val equivp_ty = ([rty, rty] ---> @{typ bool}) --> @{typ bool}
        val const =
          if partial then @{const_name part_equivp} else @{const_name equivp}
      in
        HOLogic.mk_Trueprop (Const (const, equivp_ty) $ rel)
      end

    val goals = map (mk_goal o snd) quot_list

    fun after_qed [thms] = fold (snd oo add_quotient_type) (quot_list ~~ thms)
  in
    Proof.theorem NONE after_qed [map (rpair []) goals] lthy
  end

fun quotient_type_cmd specs lthy =
  let
    fun parse_spec ((((vs, qty_name), mx), rty_str), (partial, rel_str)) lthy =
      let
        val rty = Syntax.read_typ lthy rty_str
        val lthy1 = Variable.declare_typ rty lthy
        val rel =
          Syntax.parse_term lthy1 rel_str
          |> Type.constraint (rty --> rty --> @{typ bool})
          |> Syntax.check_term lthy1
        val lthy2 = Variable.declare_term rel lthy1
      in
        (((vs, qty_name, mx), (rty, rel, partial)), lthy2)
      end

    val (spec', lthy') = fold_map parse_spec specs lthy
  in
    quotient_type spec' lthy'
  end

val partial = Scan.optional (Parse.reserved "partial" -- Parse.$$$ ":" >> K true) false

val quotspec_parser =
  Parse.and_list1
    ((Parse.type_args -- Parse.binding) --
      Parse.opt_mixfix -- (Parse.$$$ "=" |-- Parse.typ) --
        (Parse.$$$ "/" |-- (partial -- Parse.term)))

val _ = Keyword.keyword "/"

val _ =
  Outer_Syntax.local_theory_to_proof "quotient_type"
    "quotient type definitions (require equivalence proofs)"
       Keyword.thy_goal (quotspec_parser >> quotient_type_cmd)

end;
