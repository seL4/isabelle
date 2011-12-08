(*  Title:      HOL/HOLCF/Tools/fixrec.ML
    Author:     Amber Telfer and Brian Huffman

Recursive function definition package for HOLCF.
*)

signature FIXREC =
sig
  val add_fixrec: (binding * typ option * mixfix) list
    -> (bool * (Attrib.binding * term)) list -> local_theory -> local_theory
  val add_fixrec_cmd: (binding * string option * mixfix) list
    -> (bool * (Attrib.binding * string)) list -> local_theory -> local_theory
  val add_matchers: (string * string) list -> theory -> theory
  val fixrec_simp_tac: Proof.context -> int -> tactic
  val setup: theory -> theory
end

structure Fixrec : FIXREC =
struct

open HOLCF_Library

infixr 6 ->>
infix -->>
infix 9 `

val def_cont_fix_eq = @{thm def_cont_fix_eq}
val def_cont_fix_ind = @{thm def_cont_fix_ind}

fun fixrec_err s = error ("fixrec definition error:\n" ^ s)

(*************************************************************************)
(***************************** building types ****************************)
(*************************************************************************)

local

fun binder_cfun (Type(@{type_name cfun},[T, U])) = T :: binder_cfun U
  | binder_cfun (Type(@{type_name "fun"},[T, U])) = T :: binder_cfun U
  | binder_cfun _   =  []

fun body_cfun (Type(@{type_name cfun},[_, U])) = body_cfun U
  | body_cfun (Type(@{type_name "fun"},[_, U])) = body_cfun U
  | body_cfun T   =  T

in

fun matcherT (T, U) =
  body_cfun T ->> (binder_cfun T -->> U) ->> U

end

(*************************************************************************)
(***************************** building terms ****************************)
(*************************************************************************)

val mk_trp = HOLogic.mk_Trueprop

(* splits a cterm into the right and lefthand sides of equality *)
fun dest_eqs t = HOLogic.dest_eq (HOLogic.dest_Trueprop t)

(* similar to Thm.head_of, but for continuous application *)
fun chead_of (Const(@{const_name Rep_cfun},_)$f$_) = chead_of f
  | chead_of u = u

infix 1 === val (op ===) = HOLogic.mk_eq

fun mk_mplus (t, u) =
  let val mT = Term.fastype_of t
  in Const(@{const_name Fixrec.mplus}, mT ->> mT ->> mT) ` t ` u end

fun mk_run t =
  let
    val mT = Term.fastype_of t
    val T = dest_matchT mT
    val run = Const(@{const_name Fixrec.run}, mT ->> T)
  in
    case t of
      Const(@{const_name Rep_cfun}, _) $
        Const(@{const_name Fixrec.succeed}, _) $ u => u
    | _ => run ` t
  end


(*************************************************************************)
(************* fixed-point definitions and unfolding theorems ************)
(*************************************************************************)

structure FixrecUnfoldData = Generic_Data
(
  type T = thm Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data : T = Symtab.merge (K true) data
)

local

fun name_of (Const (n, _)) = n
  | name_of (Free (n, _)) = n
  | name_of t = raise TERM ("Fixrec.add_unfold: lhs not a constant", [t])

val lhs_name =
  name_of o head_of o fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of

in

val add_unfold : attribute =
  Thm.declaration_attribute
    (fn th => FixrecUnfoldData.map (Symtab.insert (K true) (lhs_name th, th)))

end

fun add_fixdefs
  (fixes : ((binding * typ) * mixfix) list)
  (spec : (Attrib.binding * term) list)
  (lthy : local_theory) =
  let
    val thy = Proof_Context.theory_of lthy
    val names = map (Binding.name_of o fst o fst) fixes
    val all_names = space_implode "_" names
    val (lhss, rhss) = ListPair.unzip (map (dest_eqs o snd) spec)
    val functional = lambda_tuple lhss (mk_tuple rhss)
    val fixpoint = mk_fix (mk_cabs functional)

    val cont_thm =
      let
        val prop = mk_trp (mk_cont functional)
        fun err _ = error (
          "Continuity proof failed please check that cont2cont rules\n" ^
          "or simp rules are configured for all non-HOLCF constants.\n" ^
          "The error occurred for the goal statement:\n" ^
          Syntax.string_of_term lthy prop)
        val rules = Cont2ContData.get lthy
        val fast_tac = SOLVED' (REPEAT_ALL_NEW (match_tac rules))
        val slow_tac = SOLVED' (simp_tac (simpset_of lthy))
        val tac = fast_tac 1 ORELSE slow_tac 1 ORELSE err
      in
        Goal.prove lthy [] [] prop (K tac)
      end

    fun one_def (Free(n,_)) r =
          let val b = Long_Name.base_name n
          in ((Binding.name (b^"_def"), []), r) end
      | one_def _ _ = fixrec_err "fixdefs: lhs not of correct form"
    fun defs [] _ = []
      | defs (l::[]) r = [one_def l r]
      | defs (l::ls) r = one_def l (mk_fst r) :: defs ls (mk_snd r)
    val fixdefs = defs lhss fixpoint
    val (fixdef_thms : (term * (string * thm)) list, lthy) = lthy
      |> fold_map Local_Theory.define (map (apfst fst) fixes ~~ fixdefs)
    fun pair_equalI (thm1, thm2) = @{thm Pair_equalI} OF [thm1, thm2]
    val tuple_fixdef_thm = foldr1 pair_equalI (map (snd o snd) fixdef_thms)
    val P = Var (("P", 0), map Term.fastype_of lhss ---> HOLogic.boolT)
    val predicate = lambda_tuple lhss (list_comb (P, lhss))
    val tuple_induct_thm = (def_cont_fix_ind OF [tuple_fixdef_thm, cont_thm])
      |> Drule.instantiate' [] [SOME (Thm.cterm_of thy predicate)]
      |> Local_Defs.unfold lthy @{thms split_paired_all split_conv split_strict}
    val tuple_unfold_thm = (def_cont_fix_eq OF [tuple_fixdef_thm, cont_thm])
      |> Local_Defs.unfold lthy @{thms split_conv}
    fun unfolds [] _ = []
      | unfolds (n::[]) thm = [(n, thm)]
      | unfolds (n::ns) thm = let
          val thmL = thm RS @{thm Pair_eqD1}
          val thmR = thm RS @{thm Pair_eqD2}
        in (n, thmL) :: unfolds ns thmR end
    val unfold_thms = unfolds names tuple_unfold_thm
    val induct_note : Attrib.binding * Thm.thm list =
      let
        val thm_name = Binding.qualify true all_names (Binding.name "induct")
      in
        ((thm_name, []), [tuple_induct_thm])
      end
    fun unfold_note (name, thm) : Attrib.binding * Thm.thm list =
      let
        val thm_name = Binding.qualify true name (Binding.name "unfold")
        val src = Attrib.internal (K add_unfold)
      in
        ((thm_name, [src]), [thm])
      end
    val (_, lthy) = lthy
      |> fold_map Local_Theory.note (induct_note :: map unfold_note unfold_thms)
  in
    (lthy, names, fixdef_thms, map snd unfold_thms)
  end

(*************************************************************************)
(*********** monadic notation and pattern matching compilation ***********)
(*************************************************************************)

structure FixrecMatchData = Theory_Data
(
  type T = string Symtab.table
  val empty = Symtab.empty
  val extend = I
  fun merge data = Symtab.merge (K true) data
)

(* associate match functions with pattern constants *)
fun add_matchers ms = FixrecMatchData.map (fold Symtab.update ms)

fun taken_names (t : term) : bstring list =
  let
    fun taken (Const(a,_), bs) = insert (op =) (Long_Name.base_name a) bs
      | taken (Free(a,_) , bs) = insert (op =) a bs
      | taken (f $ u     , bs) = taken (f, taken (u, bs))
      | taken (Abs(a,_,t), bs) = taken (t, insert (op =) a bs)
      | taken (_         , bs) = bs
  in
    taken (t, [])
  end

(* builds a monadic term for matching a pattern *)
(* returns (rhs, free variable, used varnames) *)
fun compile_pat match_name pat rhs taken =
  let
    fun comp_pat p rhs taken =
      if is_Free p then (rhs, p, taken)
      else comp_con (fastype_of p) p rhs [] taken
    (* compiles a monadic term for a constructor pattern *)
    and comp_con T p rhs vs taken =
      case p of
        Const(@{const_name Rep_cfun},_) $ f $ x =>
          let val (rhs', v, taken') = comp_pat x rhs taken
          in comp_con T f rhs' (v::vs) taken' end
      | f $ x =>
          let val (rhs', v, taken') = comp_pat x rhs taken
          in comp_con T f rhs' (v::vs) taken' end
      | Const (c, cT) =>
          let
            val n = singleton (Name.variant_list taken) "v"
            val v = Free(n, T)
            val m = Const(match_name c, matcherT (cT, fastype_of rhs))
            val k = big_lambdas vs rhs
          in
            (m`v`k, v, n::taken)
          end
      | _ => raise TERM ("fixrec: invalid pattern ", [p])
  in
    comp_pat pat rhs taken
  end

(* builds a monadic term for matching a function definition pattern *)
(* returns (constant, (vars, matcher)) *)
fun compile_lhs match_name pat rhs vs taken =
  case pat of
    Const(@{const_name Rep_cfun}, _) $ f $ x =>
      let val (rhs', v, taken') = compile_pat match_name x rhs taken
      in compile_lhs match_name f rhs' (v::vs) taken' end
  | Free(_,_) => (pat, (vs, rhs))
  | Const(_,_) => (pat, (vs, rhs))
  | _ => fixrec_err ("invalid function pattern: "
                    ^ ML_Syntax.print_term pat)

fun strip_alls t =
  if Logic.is_all t then strip_alls (snd (Logic.dest_all t)) else t

fun compile_eq match_name eq =
  let
    val (lhs,rhs) = dest_eqs (Logic.strip_imp_concl (strip_alls eq))
  in
    compile_lhs match_name lhs (mk_succeed rhs) [] (taken_names eq)
  end

(* this is the pattern-matching compiler function *)
fun compile_eqs match_name eqs =
  let
    val (consts, matchers) =
      ListPair.unzip (map (compile_eq match_name) eqs)
    val const =
        case distinct (op =) consts of
          [n] => n
        | [] => fixrec_err "no defining equations for function"
        | _ => fixrec_err "all equations in block must define the same function"
    val vars =
        case distinct (op = o pairself length) (map fst matchers) of
          [vars] => vars
        | _ => fixrec_err "all equations in block must have the same arity"
    (* rename so all matchers use same free variables *)
    fun rename (vs, t) = Term.subst_free (filter_out (op =) (vs ~~ vars)) t
    val rhs = big_lambdas vars (mk_run (foldr1 mk_mplus (map rename matchers)))
  in
    mk_trp (const === rhs)
  end

(*************************************************************************)
(********************** Proving associated theorems **********************)
(*************************************************************************)

fun eta_tac i = CONVERSION Thm.eta_conversion i

fun fixrec_simp_tac ctxt =
  let
    val tab = FixrecUnfoldData.get (Context.Proof ctxt)
    val ss = Simplifier.simpset_of ctxt
    fun concl t =
      if Logic.is_all t then concl (snd (Logic.dest_all t))
      else HOLogic.dest_Trueprop (Logic.strip_imp_concl t)
    fun tac (t, i) =
      let
        val (c, _) =
            (dest_Const o head_of o chead_of o fst o HOLogic.dest_eq o concl) t
        val unfold_thm = the (Symtab.lookup tab c)
        val rule = unfold_thm RS @{thm ssubst_lhs}
      in
        CHANGED (rtac rule i THEN eta_tac i THEN asm_simp_tac ss i)
      end
  in
    SUBGOAL (fn ti => the_default no_tac (try tac ti))
  end

(* proves a block of pattern matching equations as theorems, using unfold *)
fun make_simps ctxt (unfold_thm, eqns : (Attrib.binding * term) list) =
  let
    val ss = Simplifier.simpset_of ctxt
    val rule = unfold_thm RS @{thm ssubst_lhs}
    val tac = rtac rule 1 THEN eta_tac 1 THEN asm_simp_tac ss 1
    fun prove_term t = Goal.prove ctxt [] [] t (K tac)
    fun prove_eqn (bind, eqn_t) = (bind, prove_term eqn_t)
  in
    map prove_eqn eqns
  end

(*************************************************************************)
(************************* Main fixrec function **************************)
(*************************************************************************)

local
(* code adapted from HOL/Tools/primrec.ML *)

fun gen_fixrec
  prep_spec
  (raw_fixes : (binding * 'a option * mixfix) list)
  (raw_spec' : (bool * (Attrib.binding * 'b)) list)
  (lthy : local_theory) =
  let
    val (skips, raw_spec) = ListPair.unzip raw_spec'
    val (fixes : ((binding * typ) * mixfix) list,
         spec : (Attrib.binding * term) list) =
          fst (prep_spec raw_fixes raw_spec lthy)
    val names = map (Binding.name_of o fst o fst) fixes
    fun check_head name =
        member (op =) names name orelse
        fixrec_err ("Illegal equation head. Expected " ^ commas_quote names)
    val chead_of_spec =
      chead_of o fst o dest_eqs o Logic.strip_imp_concl o strip_alls o snd
    fun name_of (Free (n, _)) = tap check_head n
      | name_of _ = fixrec_err ("unknown term")
    val all_names = map (name_of o chead_of_spec) spec
    fun block_of_name n =
      map_filter
        (fn (m,eq) => if m = n then SOME eq else NONE)
        (all_names ~~ (spec ~~ skips))
    val blocks = map block_of_name names

    val matcher_tab = FixrecMatchData.get (Proof_Context.theory_of lthy)
    fun match_name c =
      case Symtab.lookup matcher_tab c of SOME m => m
        | NONE => fixrec_err ("unknown pattern constructor: " ^ c)

    val matches = map (compile_eqs match_name) (map (map (snd o fst)) blocks)
    val spec' = map (pair Attrib.empty_binding) matches
    val (lthy, _, _, unfold_thms) =
      add_fixdefs fixes spec' lthy

    val blocks' = map (map fst o filter_out snd) blocks
    val simps : (Attrib.binding * thm) list list =
      map (make_simps lthy) (unfold_thms ~~ blocks')
    fun mk_bind n : Attrib.binding =
     (Binding.qualify true n (Binding.name "simps"), @{attributes [simp]})
    val simps1 : (Attrib.binding * thm list) list =
      map (fn (n,xs) => (mk_bind n, map snd xs)) (names ~~ simps)
    val simps2 : (Attrib.binding * thm list) list =
      map (apsnd (fn thm => [thm])) (flat simps)
    val (_, lthy) = lthy
      |> fold_map Local_Theory.note (simps1 @ simps2)
  in
    lthy
  end

in

val add_fixrec = gen_fixrec Specification.check_spec
val add_fixrec_cmd = gen_fixrec Specification.read_spec

end (* local *)


(*************************************************************************)
(******************************** Parsers ********************************)
(*************************************************************************)

val opt_thm_name' : (bool * Attrib.binding) parser =
  Parse.$$$ "(" -- Parse.$$$ "unchecked" -- Parse.$$$ ")" >> K (true, Attrib.empty_binding)
    || Parse_Spec.opt_thm_name ":" >> pair false

val spec' : (bool * (Attrib.binding * string)) parser =
  opt_thm_name' -- Parse.prop >> (fn ((a, b), c) => (a, (b, c)))

val alt_specs' : (bool * (Attrib.binding * string)) list parser =
  let val unexpected = Scan.ahead (Parse.name || Parse.$$$ "[" || Parse.$$$ "(")
  in Parse.enum1 "|" (spec' --| Scan.option (unexpected -- Parse.!!! (Parse.$$$ "|"))) end

val _ =
  Outer_Syntax.local_theory "fixrec" "define recursive functions (HOLCF)" Keyword.thy_decl
    (Parse.fixes -- (Parse.where_ |-- Parse.!!! alt_specs')
      >> (fn (fixes, specs) => add_fixrec_cmd fixes specs))

val setup =
  Method.setup @{binding fixrec_simp}
    (Scan.succeed (SIMPLE_METHOD' o fixrec_simp_tac))
    "pattern prover for fixrec constants"

end
