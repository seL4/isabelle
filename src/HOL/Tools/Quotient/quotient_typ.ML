(*  Title:      HOL/Tools/Quotient/quotient_typ.thy
    Author:     Cezary Kaliszyk and Christian Urban

Definition of a quotient type.

*)

signature QUOTIENT_TYPE =
sig
  val add_quotient_type: ((string list * binding * mixfix) * (typ * term)) * thm
    -> Proof.context -> (thm * thm) * local_theory

  val quotient_type: ((string list * binding * mixfix) * (typ * term)) list
    -> Proof.context -> Proof.state

  val quotient_type_cmd: ((((string list * binding) * mixfix) * string) * string) list
    -> Proof.context -> Proof.state
end;

structure Quotient_Type: QUOTIENT_TYPE =
struct

open Quotient_Info;

(* wrappers for define, note, Attrib.internal and theorem_i *)
fun define (name, mx, rhs) lthy =
let
  val ((rhs, (_ , thm)), lthy') =
     Local_Theory.define ((name, mx), (Attrib.empty_binding, rhs)) lthy
in
  ((rhs, thm), lthy')
end

fun note (name, thm, attrs) lthy =
let
  val ((_,[thm']), lthy') = Local_Theory.note ((name, attrs), [thm]) lthy
in
  (thm', lthy')
end

fun intern_attr at = Attrib.internal (K at)

fun theorem after_qed goals ctxt =
let
  val goals' = map (rpair []) goals
  fun after_qed' thms = after_qed (the_single thms)
in
  Proof.theorem NONE after_qed' [goals'] ctxt
end



(*** definition of quotient types ***)

val mem_def1 = @{lemma "y : S ==> S y" by (simp add: mem_def)}
val mem_def2 = @{lemma "S y ==> y : S" by (simp add: mem_def)}

(* constructs the term lambda (c::rty => bool). EX (x::rty). c = rel x *)
fun typedef_term rel rty lthy =
let
  val [x, c] =
    [("x", rty), ("c", HOLogic.mk_setT rty)]
    |> Variable.variant_frees lthy [rel]
    |> map Free
in
  lambda c (HOLogic.exists_const rty $
     lambda x (HOLogic.mk_eq (c, (rel $ x))))
end


(* makes the new type definitions and proves non-emptyness *)
fun typedef_make (vs, qty_name, mx, rel, rty) lthy =
let
  val typedef_tac =
    EVERY1 (map rtac [@{thm exI}, mem_def2, @{thm exI}, @{thm refl}])
in
(* FIXME: purely local typedef causes at the moment 
   problems with type variables
  
  Typedef.add_typedef false NONE (qty_name, vs, mx) 
    (typedef_term rel rty lthy) NONE typedef_tac lthy
*)
   Local_Theory.theory_result
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
  val abs_inv = mem_def2 RS #Abs_inverse typedef_info
  val rep_inj = #Rep_inject typedef_info
in
  (rtac @{thm quot_type.intro} THEN' RANGE [
    rtac equiv_thm,
    rtac rep_thm,
    rtac rep_inv,
    EVERY' (map rtac [abs_inv, @{thm exI}, @{thm refl}]),
    rtac rep_inj]) 1
end


(* proves the quot_type theorem for the new type *)
fun typedef_quot_type_thm (rel, abs, rep, equiv_thm, typedef_info) lthy =
let
  val quot_type_const = Const (@{const_name "quot_type"}, dummyT)
  val goal =
    HOLogic.mk_Trueprop (quot_type_const $ rel $ abs $ rep)
    |> Syntax.check_term lthy
in
  Goal.prove lthy [] [] goal
    (K (typedef_quot_type_tac equiv_thm typedef_info))
end

(* proves the quotient theorem for the new type *)
fun typedef_quotient_thm (rel, abs, rep, abs_def, rep_def, quot_type_thm) lthy =
let
  val quotient_const = Const (@{const_name "Quotient"}, dummyT)
  val goal =
    HOLogic.mk_Trueprop (quotient_const $ rel $ abs $ rep)
    |> Syntax.check_term lthy

  val typedef_quotient_thm_tac =
    EVERY1 [
      K (rewrite_goals_tac [abs_def, rep_def]),
      rtac @{thm quot_type.Quotient},
      rtac quot_type_thm]
in
  Goal.prove lthy [] [] goal
    (K typedef_quotient_thm_tac)
end


(* main function for constructing a quotient type *)
fun add_quotient_type (((vs, qty_name, mx), (rty, rel)), equiv_thm) lthy =
let
  (* generates the typedef *)
  val ((qty_full_name, typedef_info), lthy1) = typedef_make (vs, qty_name, mx, rel, rty) lthy

  (* abs and rep functions from the typedef *)
  val Abs_ty = #abs_type (#1 typedef_info)
  val Rep_ty = #rep_type (#1 typedef_info)
  val Abs_name = #Abs_name (#1 typedef_info)
  val Rep_name = #Rep_name (#1 typedef_info)
  val Abs_const = Const (Abs_name, Rep_ty --> Abs_ty)
  val Rep_const = Const (Rep_name, Abs_ty --> Rep_ty)

  (* more useful abs and rep definitions *)
  val abs_const = Const (@{const_name "quot_type.abs"}, dummyT )
  val rep_const = Const (@{const_name "quot_type.rep"}, dummyT )
  val abs_trm = Syntax.check_term lthy1 (abs_const $ rel $ Abs_const)
  val rep_trm = Syntax.check_term lthy1 (rep_const $ Rep_const)
  val abs_name = Binding.prefix_name "abs_" qty_name
  val rep_name = Binding.prefix_name "rep_" qty_name

  val ((abs, abs_def), lthy2) = define (abs_name, NoSyn, abs_trm) lthy1
  val ((rep, rep_def), lthy3) = define (rep_name, NoSyn, rep_trm) lthy2

  (* quot_type theorem *)
  val quot_thm = typedef_quot_type_thm (rel, Abs_const, Rep_const, equiv_thm, typedef_info) lthy3

  (* quotient theorem *)
  val quotient_thm = typedef_quotient_thm (rel, abs, rep, abs_def, rep_def, quot_thm) lthy3
  val quotient_thm_name = Binding.prefix_name "Quotient_" qty_name

  (* name equivalence theorem *)
  val equiv_thm_name = Binding.suffix_name "_equivp" qty_name

  (* storing the quot-info *)
  fun qinfo phi = transform_quotdata phi
    {qtyp = Abs_ty, rtyp = rty, equiv_rel = rel, equiv_thm = equiv_thm}
  val lthy4 = Local_Theory.declaration true
    (fn phi => quotdata_update_gen qty_full_name (qinfo phi)) lthy3
in
  lthy4
  |> note (quotient_thm_name, quotient_thm, [intern_attr quotient_rules_add])
  ||>> note (equiv_thm_name, equiv_thm, [intern_attr equiv_rules_add])
end


(* sanity checks for the quotient type specifications *)
fun sanity_check ((vs, qty_name, _), (rty, rel)) =
let
  val rty_tfreesT = map fst (Term.add_tfreesT rty [])
  val rel_tfrees = map fst (Term.add_tfrees rel [])
  val rel_frees = map fst (Term.add_frees rel [])
  val rel_vars = Term.add_vars rel []
  val rel_tvars = Term.add_tvars rel []
  val qty_str = Binding.str_of qty_name ^ ": "

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
fun map_check ctxt (_, (rty, _)) =
let
  val thy = ProofContext.theory_of ctxt

  fun map_check_aux rty warns =
    case rty of
      Type (_, []) => warns
    | Type (s, _) => if maps_defined thy s then warns else s::warns
    | _ => warns

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
 - the relation according to which the type is quotient

 it opens a proof-state in which one has to show that the
 relations are equivalence relations
*)

fun quotient_type quot_list lthy =
let
  (* sanity check *)
  val _ = List.app sanity_check quot_list
  val _ = List.app (map_check lthy) quot_list

  fun mk_goal (rty, rel) =
  let
    val equivp_ty = ([rty, rty] ---> @{typ bool}) --> @{typ bool}
  in
    HOLogic.mk_Trueprop (Const (@{const_name equivp}, equivp_ty) $ rel)
  end

  val goals = map (mk_goal o snd) quot_list

  fun after_qed thms lthy =
    fold_map add_quotient_type (quot_list ~~ thms) lthy |> snd
in
  theorem after_qed goals lthy
end

fun quotient_type_cmd specs lthy =
let
  fun parse_spec ((((vs, qty_name), mx), rty_str), rel_str) lthy =
  let
    val rty = Syntax.read_typ lthy rty_str
    val lthy1 = Variable.declare_typ rty lthy
    val rel = 
      Syntax.parse_term lthy1 rel_str
      |> Syntax.type_constraint (rty --> rty --> @{typ bool}) 
      |> Syntax.check_term lthy1 
    val lthy2 = Variable.declare_term rel lthy1 
  in
    (((vs, qty_name, mx), (rty, rel)), lthy2)
  end

  val (spec', lthy') = fold_map parse_spec specs lthy
in
  quotient_type spec' lthy'
end

val quotspec_parser =
    Parse.and_list1
     ((Parse.type_args -- Parse.binding) --
        Parse.opt_mixfix -- (Parse.$$$ "=" |-- Parse.typ) --
         (Parse.$$$ "/" |-- Parse.term))

val _ = Keyword.keyword "/"

val _ =
    Outer_Syntax.local_theory_to_proof "quotient_type"
      "quotient type definitions (require equivalence proofs)"
         Keyword.thy_goal (quotspec_parser >> quotient_type_cmd)

end; (* structure *)
