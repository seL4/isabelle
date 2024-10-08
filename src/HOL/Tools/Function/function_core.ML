(*  Title:      HOL/Tools/Function/function_core.ML
    Author:     Alexander Krauss, TU Muenchen

Core of the function package.
*)

signature FUNCTION_CORE =
sig
  val trace: bool Unsynchronized.ref
  val prepare_function : Function_Common.function_config
    -> binding (* defname *)
    -> ((binding * typ) * mixfix) list (* defined symbol *)
    -> ((string * typ) list * term list * term * term) list (* specification *)
    -> local_theory
    -> (term   (* f *)
        * thm  (* goalstate *)
        * (Proof.context -> thm -> Function_Common.function_result) (* continuation *)
       ) * local_theory

end

structure Function_Core : FUNCTION_CORE =
struct

val trace = Unsynchronized.ref false
fun trace_msg msg = if ! trace then tracing (msg ()) else ()

val boolT = HOLogic.boolT
val mk_eq = HOLogic.mk_eq

open Function_Lib
open Function_Common

datatype globals = Globals of
 {fvar: term,
  domT: typ,
  ranT: typ,
  h: term,
  y: term,
  x: term,
  z: term,
  a: term,
  P: term,
  D: term,
  Pbool:term}

datatype rec_call_info = RCInfo of
 {RIvs: (string * typ) list,  (* Call context: fixes and assumes *)
  CCas: thm list,
  rcarg: term,                 (* The recursive argument *)
  llRI: thm,
  h_assum: term}


datatype clause_context = ClauseContext of
 {ctxt : Proof.context,
  qs : term list,
  gs : term list,
  lhs: term,
  rhs: term,
  cqs: cterm list,
  ags: thm list,
  case_hyp : thm}


fun transfer_clause_ctx thy (ClauseContext { ctxt, qs, gs, lhs, rhs, cqs, ags, case_hyp }) =
  ClauseContext { ctxt = Proof_Context.transfer thy ctxt,
    qs = qs, gs = gs, lhs = lhs, rhs = rhs, cqs = cqs, ags = ags, case_hyp = case_hyp }


datatype clause_info = ClauseInfo of
 {no: int,
  qglr : ((string * typ) list * term list * term * term),
  cdata : clause_context,
  tree: Function_Context_Tree.ctx_tree,
  lGI: thm,
  RCs: rec_call_info list}


(* Theory dependencies. *)
val acc_induct_rule = @{thm accp_induct_rule}

val ex1_implies_ex = @{thm Fun_Def.fundef_ex1_existence}
val ex1_implies_un = @{thm Fun_Def.fundef_ex1_uniqueness}
val ex1_implies_iff = @{thm Fun_Def.fundef_ex1_iff}

val acc_downward = @{thm accp_downward}
val accI = @{thm accp.accI}


fun find_calls tree =
  let
    fun add_Ri (fixes,assumes) (_ $ arg) _ (_, xs) =
      ([], (fixes, assumes, arg) :: xs)
      | add_Ri _ _ _ _ = raise Match
  in
    rev (Function_Context_Tree.traverse_tree add_Ri tree [])
  end


(** building proof obligations *)

fun mk_compat_proof_obligations domT ranT fvar f glrs =
  let
    fun mk_impl ((qs, gs, lhs, rhs),(qs', gs', lhs', rhs')) =
      let
        val shift = incr_boundvars (length qs')
      in
        Logic.mk_implies
          (HOLogic.mk_Trueprop (HOLogic.eq_const domT $ shift lhs $ lhs'),
            HOLogic.mk_Trueprop (HOLogic.eq_const ranT $ shift rhs $ rhs'))
        |> fold_rev (curry Logic.mk_implies) (map shift gs @ gs')
        |> fold_rev (fn (n,T) => fn b => Logic.all_const T $ Abs(n,T,b)) (qs @ qs')
        |> curry abstract_over fvar
        |> curry subst_bound f
      end
  in
    map mk_impl (unordered_pairs glrs)
  end


fun mk_completeness (Globals {x, Pbool, ...}) clauses qglrs =
  let
    fun mk_case (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) =
      HOLogic.mk_Trueprop Pbool
      |> curry Logic.mk_implies (HOLogic.mk_Trueprop (mk_eq (x, lhs)))
      |> fold_rev (curry Logic.mk_implies) gs
      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
  in
    HOLogic.mk_Trueprop Pbool
    |> fold_rev (curry Logic.mk_implies o mk_case) (clauses ~~ qglrs)
    |> mk_forall_rename ("x", x)
    |> mk_forall_rename ("P", Pbool)
  end

(** making a context with it's own local bindings **)

fun mk_clause_context x ctxt (pre_qs,pre_gs,pre_lhs,pre_rhs) =
  let
    val (qs, ctxt') = Variable.variant_fixes (map fst pre_qs) ctxt
      |>> map2 (fn (_, T) => fn n => Free (n, T)) pre_qs

    fun inst t = subst_bounds (rev qs, t)
    val gs = map inst pre_gs
    val lhs = inst pre_lhs
    val rhs = inst pre_rhs

    val cqs = map (Thm.cterm_of ctxt') qs
    val ags = map (Thm.assume o Thm.cterm_of ctxt') gs

    val case_hyp =
      Thm.assume (Thm.cterm_of ctxt' (HOLogic.mk_Trueprop (mk_eq (x, lhs))))
  in
    ClauseContext { ctxt = ctxt', qs = qs, gs = gs, lhs = lhs, rhs = rhs,
      cqs = cqs, ags = ags, case_hyp = case_hyp }
  end


(* lowlevel term function. FIXME: remove *)
fun abstract_over_list vs body =
  let
    fun abs lev v tm =
      if v aconv tm then Bound lev
      else
        (case tm of
          Abs (a, T, t) => Abs (a, T, abs (lev + 1) v t)
        | t $ u => abs lev v t $ abs lev v u
        | t => t)
  in
    fold_index (fn (i, v) => fn t => abs i v t) vs body
  end



fun mk_clause_info globals G f no cdata qglr tree RCs GIntro_thm RIntro_thms =
  let
    val Globals {h, ...} = globals

    val ClauseContext { ctxt, qs, cqs, ags, ... } = cdata

    (* Instantiate the GIntro thm with "f" and import into the clause context. *)
    val lGI = GIntro_thm
      |> Thm.forall_elim (Thm.cterm_of ctxt f)
      |> fold Thm.forall_elim cqs
      |> fold Thm.elim_implies ags

    fun mk_call_info (rcfix, rcassm, rcarg) RI =
      let
        val llRI = RI
          |> fold Thm.forall_elim cqs
          |> fold (Thm.forall_elim o Thm.cterm_of ctxt o Free) rcfix
          |> fold Thm.elim_implies ags
          |> fold Thm.elim_implies rcassm

        val h_assum =
          HOLogic.mk_Trueprop (G $ rcarg $ (h $ rcarg))
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) rcassm
          |> fold_rev (Logic.all o Free) rcfix
          |> Pattern.rewrite_term (Proof_Context.theory_of ctxt) [(f, h)] []
          |> abstract_over_list (rev qs)
      in
        RCInfo {RIvs=rcfix, rcarg=rcarg, CCas=rcassm, llRI=llRI, h_assum=h_assum}
      end

    val RC_infos = map2 mk_call_info RCs RIntro_thms
  in
    ClauseInfo {no=no, cdata=cdata, qglr=qglr, lGI=lGI, RCs=RC_infos,
      tree=tree}
  end


fun store_compat_thms 0 thms = []
  | store_compat_thms n thms =
  let
    val (thms1, thms2) = chop n thms
  in
    (thms1 :: store_compat_thms (n - 1) thms2)
  end

(* expects i <= j *)
fun lookup_compat_thm i j cts =
  nth (nth cts (i - 1)) (j - i)

(* Returns "Gsi, Gsj, lhs_i = lhs_j |-- rhs_j_f = rhs_i_f" *)
(* if j < i, then turn around *)
fun get_compat_thm ctxt cts i j ctxi ctxj =
  let
    val ClauseContext {cqs=cqsi,ags=agsi,lhs=lhsi,...} = ctxi
    val ClauseContext {cqs=cqsj,ags=agsj,lhs=lhsj,...} = ctxj

    val lhsi_eq_lhsj = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj)))
  in if j < i then
    let
      val compat = lookup_compat_thm j i cts
    in
      compat         (* "!!qj qi. Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
      |> fold Thm.forall_elim (cqsj @ cqsi) (* "Gsj => Gsi => lhsj = lhsi ==> rhsj = rhsi" *)
      |> fold Thm.elim_implies agsj
      |> fold Thm.elim_implies agsi
      |> Thm.elim_implies ((Thm.assume lhsi_eq_lhsj) RS sym) (* "Gsj, Gsi, lhsi = lhsj |-- rhsj = rhsi" *)
    end
    else
    let
      val compat = lookup_compat_thm i j cts
    in
      compat        (* "!!qi qj. Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
      |> fold Thm.forall_elim (cqsi @ cqsj) (* "Gsi => Gsj => lhsi = lhsj ==> rhsi = rhsj" *)
      |> fold Thm.elim_implies agsi
      |> fold Thm.elim_implies agsj
      |> Thm.elim_implies (Thm.assume lhsi_eq_lhsj)
      |> (fn thm => thm RS sym) (* "Gsi, Gsj, lhsi = lhsj |-- rhsj = rhsi" *)
    end
  end

(* Generates the replacement lemma in fully quantified form. *)
fun mk_replacement_lemma ctxt h ih_elim clause =
  let
    val ClauseInfo {cdata=ClauseContext {qs, cqs, ags, case_hyp, ...}, RCs, tree, ...} = clause
    local open Conv in
      val ih_conv = arg1_conv o arg_conv o arg_conv
    end

    val ih_elim_case =
      Conv.fconv_rule (ih_conv (K (case_hyp RS eq_reflection))) ih_elim

    val Ris = map (fn RCInfo {llRI, ...} => llRI) RCs
    val h_assums = map (fn RCInfo {h_assum, ...} =>
      Thm.assume (Thm.cterm_of ctxt (subst_bounds (rev qs, h_assum)))) RCs

    val (eql, _) =
      Function_Context_Tree.rewrite_by_tree ctxt h ih_elim_case (Ris ~~ h_assums) tree

    val replace_lemma = HOLogic.mk_obj_eq eql
      |> Thm.implies_intr (Thm.cprop_of case_hyp)
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) h_assums
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      |> fold_rev Thm.forall_intr cqs
      |> Thm.close_derivation \<^here>
  in
    replace_lemma
  end


fun mk_uniqueness_clause ctxt globals compat_store clausei clausej RLj =
  let
    val thy = Proof_Context.theory_of ctxt

    val Globals {h, y, x, fvar, ...} = globals
    val ClauseInfo {no=i, cdata=cctxi as ClauseContext {ctxt=ctxti, lhs=lhsi, case_hyp, ...}, ...} =
      clausei
    val ClauseInfo {no=j, qglr=cdescj, RCs=RCsj, ...} = clausej

    val cctxj as ClauseContext {ags = agsj', lhs = lhsj', rhs = rhsj', qs = qsj', cqs = cqsj', ...} =
      mk_clause_context x ctxti cdescj

    val rhsj'h = Pattern.rewrite_term thy [(fvar,h)] [] rhsj'
    val compat = get_compat_thm ctxt compat_store i j cctxi cctxj
    val Ghsj' =
      map (fn RCInfo {h_assum, ...} =>
        Thm.assume (Thm.cterm_of ctxt (subst_bounds (rev qsj', h_assum)))) RCsj

    val RLj_import = RLj
      |> fold Thm.forall_elim cqsj'
      |> fold Thm.elim_implies agsj'
      |> fold Thm.elim_implies Ghsj'

    val y_eq_rhsj'h = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_eq (y, rhsj'h))))
    val lhsi_eq_lhsj' = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_eq (lhsi, lhsj'))))
       (* lhs_i = lhs_j' |-- lhs_i = lhs_j' *)
  in
    (trans OF [case_hyp, lhsi_eq_lhsj']) (* lhs_i = lhs_j' |-- x = lhs_j' *)
    |> Thm.implies_elim RLj_import
      (* Rj1' ... Rjk', lhs_i = lhs_j' |-- rhs_j'_h = rhs_j'_f *)
    |> (fn it => trans OF [it, compat])
      (* lhs_i = lhs_j', Gj', Rj1' ... Rjk' |-- rhs_j'_h = rhs_i_f *)
    |> (fn it => trans OF [y_eq_rhsj'h, it])
      (* lhs_i = lhs_j', Gj', Rj1' ... Rjk', y = rhs_j_h' |-- y = rhs_i_f *)
    |> fold_rev (Thm.implies_intr o Thm.cprop_of) Ghsj'
    |> fold_rev (Thm.implies_intr o Thm.cprop_of) agsj'
      (* lhs_i = lhs_j' , y = rhs_j_h' |-- Gj', Rj1'...Rjk' ==> y = rhs_i_f *)
    |> Thm.implies_intr (Thm.cprop_of y_eq_rhsj'h)
    |> Thm.implies_intr (Thm.cprop_of lhsi_eq_lhsj')
    |> fold_rev Thm.forall_intr (Thm.cterm_of ctxt h :: cqsj')
  end



fun mk_uniqueness_case ctxt
    globals G f ihyp ih_intro G_cases compat_store clauses rep_lemmas clausei =
  let
    val thy = Proof_Context.theory_of ctxt
    val Globals {x, y, ranT, fvar, ...} = globals
    val ClauseInfo {cdata = ClauseContext {lhs, rhs, cqs, ags, case_hyp, ...}, lGI, RCs, ...} = clausei
    val rhsC = Pattern.rewrite_term thy [(fvar, f)] [] rhs

    val ih_intro_case = full_simplify (put_simpset HOL_basic_ss ctxt addsimps [case_hyp]) ih_intro

    fun prep_RC (RCInfo {llRI, RIvs, CCas, ...}) = (llRI RS ih_intro_case)
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) CCas
      |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt o Free) RIvs

    val existence = fold (curry op COMP o prep_RC) RCs lGI

    val P = Thm.cterm_of ctxt (mk_eq (y, rhsC))
    val G_lhs_y = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (G $ lhs $ y)))

    val unique_clauses =
      map2 (mk_uniqueness_clause ctxt globals compat_store clausei) clauses rep_lemmas

    fun elim_implies_eta A AB =
      Thm.bicompose (SOME ctxt) {flatten = false, match = true, incremented = false}
        (false, A, 0) 1 AB
      |> Seq.list_of |> the_single

    val uniqueness = G_cases
      |> Thm.forall_elim (Thm.cterm_of ctxt lhs)
      |> Thm.forall_elim (Thm.cterm_of ctxt y)
      |> Thm.forall_elim P
      |> Thm.elim_implies G_lhs_y
      |> fold elim_implies_eta unique_clauses
      |> Thm.implies_intr (Thm.cprop_of G_lhs_y)
      |> Thm.forall_intr (Thm.cterm_of ctxt y)

    val P2 = Thm.cterm_of ctxt (lambda y (G $ lhs $ y)) (* P2 y := (lhs, y): G *)

    val exactly_one =
      @{thm ex1I}
      |> Thm.instantiate'
          [SOME (Thm.ctyp_of ctxt ranT)]
          [SOME P2, SOME (Thm.cterm_of ctxt rhsC)]
      |> curry (op COMP) existence
      |> curry (op COMP) uniqueness
      |> simplify (put_simpset HOL_basic_ss ctxt addsimps [case_hyp RS sym])
      |> Thm.implies_intr (Thm.cprop_of case_hyp)
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
      |> fold_rev Thm.forall_intr cqs

    val function_value =
      existence
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr (Thm.cprop_of case_hyp)
      |> Thm.forall_intr (Thm.cterm_of ctxt x)
      |> Thm.forall_elim (Thm.cterm_of ctxt lhs)
      |> curry (op RS) refl
  in
    (exactly_one, function_value)
  end


fun prove_stuff ctxt globals G0 f R0 clauses complete compat compat_store G_elim f_def =
  let
    val Globals {h, domT, ranT, x = x0, ...} = globals

    val G = Thm.cterm_of ctxt G0
    val R = Thm.cterm_of ctxt R0

    val x = Thm.cterm_of ctxt x0

    val A = Thm.ctyp_of ctxt domT
    val B = Thm.ctyp_of ctxt ranT
    val C = Thm.ctyp_of_cterm x

    val ihyp =
      \<^instantiate>\<open>'a = A and 'b = B and 'c = C and x and R and G
        in cprop \<open>\<And>z::'a. R z x \<Longrightarrow> \<exists>!y::'b. G z y\<close> for x :: 'c\<close>

    val acc_R_x =
      \<^instantiate>\<open>'c = C and R and x
        in cprop \<open>Wellfounded.accp R x\<close> for x :: 'c\<close>

    val ihyp_thm = Thm.assume ihyp |> Thm.forall_elim_vars 0
    val ih_intro = ihyp_thm RS (f_def RS ex1_implies_ex)
    val ih_elim = ihyp_thm RS (f_def RS ex1_implies_un)
      |> Thm.instantiate' [] [NONE, SOME (Thm.cterm_of ctxt h)]

    val _ = trace_msg (K "Proving Replacement lemmas...")
    val repLemmas = map (mk_replacement_lemma ctxt h ih_elim) clauses

    val _ = trace_msg (K "Proving cases for unique existence...")
    val (ex1s, values) =
      split_list
        (map
          (mk_uniqueness_case ctxt globals G0 f ihyp ih_intro G_elim compat_store clauses repLemmas)
          clauses)

    val _ = trace_msg (K "Proving: Graph is a function")
    val graph_is_function = complete
      |> Thm.forall_elim_vars 0
      |> fold (curry op COMP) ex1s
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr acc_R_x
      |> Thm.forall_intr x
      |> (fn it => Drule.compose (it, 2, acc_induct_rule)) (* "EX! y. (?x,y):G" *)
      |> (fn it =>
          fold (Thm.forall_intr o Thm.cterm_of ctxt o Var)
            (Term.add_vars (Thm.prop_of it) []) it)

    val goalstate =  Conjunction.intr graph_is_function complete
      |> Thm.close_derivation \<^here>
      |> Goal.protect 0
      |> fold_rev (Thm.implies_intr o Thm.cprop_of) compat
      |> Thm.implies_intr (Thm.cprop_of complete)
  in
    (goalstate, values)
  end

(* wrapper -- restores quantifiers in rule specifications *)
fun inductive_def (binding as ((R, T), _)) intrs lthy =
  let
    val ({intrs = intrs_gen, elims = [elim_gen], preds = [ Rdef ], induct, ...}, lthy) =
      lthy
      |> Proof_Context.concealed
      |> Inductive.add_inductive
          {quiet_mode = true,
            verbose = ! trace,
            alt_name = Binding.empty,
            coind = false,
            no_elim = false,
            no_ind = false,
            skip_mono = true}
          [binding] (* relation *)
          [] (* no parameters *)
          (map (fn t => (Binding.empty_atts, t)) intrs) (* intro rules *)
          [] (* no special monos *)
      ||> Proof_Context.restore_naming lthy

    fun requantify orig_intro thm =
      let
        val (qs, t) = dest_all_all orig_intro
        val frees = Variable.add_frees lthy t [] |> remove (op =) (Binding.name_of R, T)
        val vars = Term.add_vars (Thm.prop_of thm) []
        val varmap = AList.lookup (op =) (frees ~~ map fst vars)
          #> the_default ("", 0)
      in
        fold_rev (fn Free (n, T) =>
          forall_intr_rename (n, Thm.cterm_of lthy (Var (varmap (n, T), T)))) qs thm
      end
  in
    ((Rdef, map2 requantify intrs intrs_gen, Thm.forall_intr_vars elim_gen, induct), lthy)
  end

fun define_graph (G_binding, G_type) fvar clauses RCss lthy =
  let
    val G = Free (Binding.name_of G_binding, G_type)
    fun mk_GIntro (ClauseContext {qs, gs, lhs, rhs, ...}) RCs =
      let
        fun mk_h_assm (rcfix, rcassm, rcarg) =
          HOLogic.mk_Trueprop (G $ rcarg $ (fvar $ rcarg))
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) rcassm
          |> fold_rev (Logic.all o Free) rcfix
      in
        HOLogic.mk_Trueprop (G $ lhs $ rhs)
        |> fold_rev (curry Logic.mk_implies o mk_h_assm) RCs
        |> fold_rev (curry Logic.mk_implies) gs
        |> fold_rev Logic.all (fvar :: qs)
      end

    val G_intros = map2 mk_GIntro clauses RCss
  in inductive_def ((G_binding, G_type), NoSyn) G_intros lthy end

fun define_function defname (fname, mixfix) domT ranT G default lthy =
  let
    val f_def_binding =
      Thm.make_def_binding (Config.get lthy function_internals)
        (derived_name_suffix defname "_sumC")
    val f_def =
      \<^instantiate>\<open>'a = domT and 'b = ranT and d = default and G
        in term \<open>\<lambda>x::'a. THE_default (d x) (\<lambda>y::'b. G x y)\<close>\<close>
      |> Syntax.check_term lthy
  in
    lthy |> Local_Theory.define
      ((Binding.map_name (suffix "C") fname, mixfix), ((f_def_binding, []), f_def))
  end

fun define_recursion_relation (R_binding, R_type) qglrs clauses RCss lthy =
  let
    val R = Free (Binding.name_of R_binding, R_type)
    fun mk_RIntro (ClauseContext {qs, gs, lhs, ...}, (oqs, _, _, _)) (rcfix, rcassm, rcarg) =
      HOLogic.mk_Trueprop (R $ rcarg $ lhs)
      |> fold_rev (curry Logic.mk_implies o Thm.prop_of) rcassm
      |> fold_rev (curry Logic.mk_implies) gs
      |> fold_rev (Logic.all o Free) rcfix
      |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
      (* "!!qs xs. CS ==> G => (r, lhs) : R" *)

    val R_intross = map2 (map o mk_RIntro) (clauses ~~ qglrs) RCss

    val ((R, RIntro_thms, R_elim, _), lthy) =
      inductive_def ((R_binding, R_type), NoSyn) (flat R_intross) lthy
  in
    ((R, Library.unflat R_intross RIntro_thms, R_elim), lthy)
  end


fun fix_globals domT ranT fvar ctxt =
  let
    val ([h, y, x, z, a, D, P, Pbool], ctxt') = Variable.variant_fixes
      ["h_fd", "y_fd", "x_fd", "z_fd", "a_fd", "D_fd", "P_fd", "Pb_fd"] ctxt
  in
    (Globals {h = Free (h, domT --> ranT),
      y = Free (y, ranT),
      x = Free (x, domT),
      z = Free (z, domT),
      a = Free (a, domT),
      D = Free (D, domT --> boolT),
      P = Free (P, domT --> boolT),
      Pbool = Free (Pbool, boolT),
      fvar = fvar,
      domT = domT,
      ranT = ranT},
    ctxt')
  end

fun inst_RC ctxt fvar f (rcfix, rcassm, rcarg) =
  let
    fun inst_term t = subst_bound(f, abstract_over (fvar, t))
  in
    (rcfix, map (Thm.assume o Thm.cterm_of ctxt o inst_term o Thm.prop_of) rcassm, inst_term rcarg)
  end



(**********************************************************
 *                   PROVING THE RULES
 **********************************************************)

fun mk_psimps ctxt globals R clauses valthms f_iff graph_is_function =
  let
    val Globals {domT, z, ...} = globals

    fun mk_psimp
      (ClauseInfo {qglr = (oqs, _, _, _), cdata = ClauseContext {cqs, lhs, ags, ...}, ...}) valthm =
      let
        val lhs_acc =
          Thm.cterm_of ctxt (HOLogic.mk_Trueprop (mk_acc domT R $ lhs)) (* "acc R lhs" *)
        val z_smaller =
          Thm.cterm_of ctxt (HOLogic.mk_Trueprop (R $ z $ lhs)) (* "R z lhs" *)
      in
        ((Thm.assume z_smaller) RS ((Thm.assume lhs_acc) RS acc_downward))
        |> (fn it => it COMP graph_is_function)
        |> Thm.implies_intr z_smaller
        |> Thm.forall_intr (Thm.cterm_of ctxt  z)
        |> (fn it => it COMP valthm)
        |> Thm.implies_intr lhs_acc
        |> asm_simplify (put_simpset HOL_basic_ss ctxt addsimps [f_iff])
        |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
        |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
      end
  in
    map2 mk_psimp clauses valthms
  end


(** Induction rule **)


val acc_subset_induct = @{thm predicate1I} RS @{thm accp_subset_induct}


fun mk_partial_induct_rule ctxt globals R complete_thm clauses =
  let
    val Globals {domT, x, z, a, P, D, ...} = globals
    val acc_R = mk_acc domT R

    val x_D = Thm.assume (Thm.cterm_of ctxt (HOLogic.mk_Trueprop (D $ x)))
    val a_D = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (D $ a))

    val D_subset =
      Thm.cterm_of ctxt (Logic.all x
        (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x), HOLogic.mk_Trueprop (acc_R $ x))))

    val D_dcl = (* "!!x z. [| x: D; (z,x):R |] ==> z:D" *)
      Logic.all x (Logic.all z (Logic.mk_implies (HOLogic.mk_Trueprop (D $ x),
        Logic.mk_implies (HOLogic.mk_Trueprop (R $ z $ x),
          HOLogic.mk_Trueprop (D $ z)))))
      |> Thm.cterm_of ctxt

    (* Inductive Hypothesis: !!z. (z,x):R ==> P z *)
    val ihyp = Logic.all_const domT $ Abs ("z", domT,
      Logic.mk_implies (HOLogic.mk_Trueprop (R $ Bound 0 $ x),
        HOLogic.mk_Trueprop (P $ Bound 0)))
      |> Thm.cterm_of ctxt

    val aihyp = Thm.assume ihyp

    fun prove_case clause =
      let
        val ClauseInfo {cdata = ClauseContext {ctxt = ctxt1, qs, cqs, ags, gs, lhs, case_hyp, ...},
          RCs, qglr = (oqs, _, _, _), ...} = clause

        val case_hyp_conv = K (case_hyp RS eq_reflection)
        local open Conv in
          val lhs_D = fconv_rule (arg_conv (arg_conv (case_hyp_conv))) x_D
          val sih =
            fconv_rule
              (binder_conv (K (arg1_conv (arg_conv (arg_conv case_hyp_conv)))) ctxt1) aihyp
        end

        fun mk_Prec (RCInfo {llRI, RIvs, CCas, rcarg, ...}) = sih
          |> Thm.forall_elim (Thm.cterm_of ctxt rcarg)
          |> Thm.elim_implies llRI
          |> fold_rev (Thm.implies_intr o Thm.cprop_of) CCas
          |> fold_rev (Thm.forall_intr o Thm.cterm_of ctxt o Free) RIvs

        val P_recs = map mk_Prec RCs   (*  [P rec1, P rec2, ... ]  *)

        val step = HOLogic.mk_Trueprop (P $ lhs)
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) P_recs
          |> fold_rev (curry Logic.mk_implies) gs
          |> curry Logic.mk_implies (HOLogic.mk_Trueprop (D $ lhs))
          |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
          |> Thm.cterm_of ctxt

        val P_lhs = Thm.assume step
          |> fold Thm.forall_elim cqs
          |> Thm.elim_implies lhs_D
          |> fold Thm.elim_implies ags
          |> fold Thm.elim_implies P_recs

        val res = Thm.cterm_of ctxt (HOLogic.mk_Trueprop (P $ x))
          |> Conv.arg_conv (Conv.arg_conv case_hyp_conv)
          |> Thm.symmetric (* P lhs == P x *)
          |> (fn eql => Thm.equal_elim eql P_lhs) (* "P x" *)
          |> Thm.implies_intr (Thm.cprop_of case_hyp)
          |> fold_rev (Thm.implies_intr o Thm.cprop_of) ags
          |> fold_rev Thm.forall_intr cqs
      in
        (res, step)
      end

    val (cases, steps) = split_list (map prove_case clauses)

    val istep = complete_thm
      |> Thm.forall_elim_vars 0
      |> fold (curry op COMP) cases (*  P x  *)
      |> Thm.implies_intr ihyp
      |> Thm.implies_intr (Thm.cprop_of x_D)
      |> Thm.forall_intr (Thm.cterm_of ctxt x)

    val subset_induct_rule =
      acc_subset_induct
      |> (curry op COMP) (Thm.assume D_subset)
      |> (curry op COMP) (Thm.assume D_dcl)
      |> (curry op COMP) (Thm.assume a_D)
      |> (curry op COMP) istep
      |> fold_rev Thm.implies_intr steps
      |> Thm.implies_intr a_D
      |> Thm.implies_intr D_dcl
      |> Thm.implies_intr D_subset

    val simple_induct_rule =
      subset_induct_rule
      |> Thm.forall_intr (Thm.cterm_of ctxt D)
      |> Thm.forall_elim (Thm.cterm_of ctxt acc_R)
      |> assume_tac ctxt 1 |> Seq.hd
      |> (curry op COMP) (acc_downward
        |> (Thm.instantiate' [SOME (Thm.ctyp_of ctxt domT)] (map (SOME o Thm.cterm_of ctxt) [R, x, z]))
        |> Thm.forall_intr (Thm.cterm_of ctxt z)
        |> Thm.forall_intr (Thm.cterm_of ctxt x))
      |> Thm.forall_intr (Thm.cterm_of ctxt a)
      |> Thm.forall_intr (Thm.cterm_of ctxt P)
  in
    simple_induct_rule
  end


(* FIXME: broken by design *)
fun mk_domain_intro ctxt (Globals {domT, ...}) R R_cases clause =
  let
    val ClauseInfo {cdata = ClauseContext {gs, lhs, cqs, ...},
      qglr = (oqs, _, _, _), ...} = clause
    val goal = HOLogic.mk_Trueprop (mk_acc domT R $ lhs)
      |> fold_rev (curry Logic.mk_implies) gs
      |> Thm.cterm_of ctxt
  in
    Goal.init goal
    |> (SINGLE (resolve_tac ctxt [accI] 1)) |> the
    |> (SINGLE (eresolve_tac ctxt [Thm.forall_elim_vars 0 R_cases] 1))  |> the
    |> (SINGLE (auto_tac ctxt)) |> the
    |> Goal.conclude
    |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)
  end



(** Termination rule **)

val wf_induct_rule = @{thm Wellfounded.wfp_induct_rule}
val wf_in_rel = @{thm Fun_Def.wf_in_rel}
val in_rel_def = @{thm Fun_Def.in_rel_def}

fun mk_nest_term_case ctxt globals R' ihyp clause =
  let
    val Globals {z, ...} = globals
    val ClauseInfo {cdata = ClauseContext {qs, cqs, ags, lhs, case_hyp, ...}, tree,
      qglr=(oqs, _, _, _), ...} = clause

    val ih_case = full_simplify (put_simpset HOL_basic_ss ctxt addsimps [case_hyp]) ihyp

    fun step (fixes, assumes) (_ $ arg) u (sub,(hyps,thms)) =
      let
        val used = (u @ sub)
          |> map (fn (ctx, thm) => Function_Context_Tree.export_thm ctxt ctx thm)

        val hyp = HOLogic.mk_Trueprop (R' $ arg $ lhs)
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) used (* additional hyps *)
          |> Function_Context_Tree.export_term (fixes, assumes)
          |> fold_rev (curry Logic.mk_implies o Thm.prop_of) ags
          |> fold_rev mk_forall_rename (map fst oqs ~~ qs)
          |> Thm.cterm_of ctxt

        val thm = Thm.assume hyp
          |> fold Thm.forall_elim cqs
          |> fold Thm.elim_implies ags
          |> Function_Context_Tree.import_thm ctxt (fixes, assumes)
          |> fold Thm.elim_implies used (*  "(arg, lhs) : R'"  *)

        val z_eq_arg = HOLogic.mk_Trueprop (mk_eq (z, arg))
          |> Thm.cterm_of ctxt |> Thm.assume

        val acc = thm COMP ih_case
        val z_acc_local = acc
          |> Conv.fconv_rule
              (Conv.arg_conv (Conv.arg_conv (K (Thm.symmetric (z_eq_arg RS eq_reflection)))))

        val ethm = z_acc_local
          |> Function_Context_Tree.export_thm ctxt (fixes,
               z_eq_arg :: case_hyp :: ags @ assumes)
          |> fold_rev forall_intr_rename (map fst oqs ~~ cqs)

        val sub' = sub @ [(([],[]), acc)]
      in
        (sub', (hyp :: hyps, ethm :: thms))
      end
      | step _ _ _ _ = raise Match
  in
    Function_Context_Tree.traverse_tree step tree
  end


fun mk_nest_term_rule ctxt globals R0 R_cases clauses =
  let
    val Globals { domT, x = x0, z = z0, ... } = globals

    val ([Rn], ctxt') = Variable.variant_fixes ["R"] ctxt

    val R = Thm.cterm_of ctxt' R0
    val R' = Thm.cterm_of ctxt' (Free (Rn, Thm.typ_of_cterm R))
    val Rrel = Thm.cterm_of ctxt' (Free (Rn, HOLogic.mk_setT (HOLogic.mk_prodT (domT, domT))))

    val x = Thm.cterm_of ctxt' x0
    val z = Thm.cterm_of ctxt' z0

    val A = Thm.ctyp_of ctxt' domT
    val B = Thm.ctyp_of_cterm x

    val acc_R_z =
      \<^instantiate>\<open>'a = A and R and z
        in cterm \<open>Wellfounded.accp R z\<close> for z :: 'a\<close>

    val inrel_R =
      \<^instantiate>\<open>'a = A and Rrel
        in cterm \<open>in_rel Rrel\<close> for Rrel :: \<open>('a \<times> 'a) set\<close>\<close>

    val wfR' = \<^instantiate>\<open>'a = A and R' in cprop \<open>wfP R'\<close>\<close>

    val ihyp =
      \<^instantiate>\<open>'a = A and 'b = B and x and R' and R
        in cprop \<open>\<And>z::'a. R' z x \<Longrightarrow> Wellfounded.accp R z\<close> for x :: 'b\<close>

    val ihyp_a = Thm.assume ihyp |> Thm.forall_elim_vars 0

    val R_z_x =
      \<^instantiate>\<open>'a = A and 'b = B and R and x and z
        in cprop \<open>R z x\<close> for x :: 'a and z :: 'b\<close>

    val (hyps, cases) =
      fold (mk_nest_term_case ctxt' globals (Thm.term_of R') ihyp_a) clauses ([], [])
  in
    R_cases
    |> Thm.forall_elim z
    |> Thm.forall_elim x
    |> Thm.forall_elim acc_R_z
    |> curry op COMP (Thm.assume R_z_x)
    |> fold_rev (curry op COMP) cases
    |> Thm.implies_intr R_z_x
    |> Thm.forall_intr z
    |> (fn it => it COMP accI)
    |> Thm.implies_intr ihyp
    |> Thm.forall_intr x
    |> (fn it => Drule.compose (it, 2, wf_induct_rule))
    |> curry op RS (Thm.assume wfR')
    |> Thm.forall_intr_vars
    |> (fn it => it COMP allI)
    |> fold Thm.implies_intr hyps
    |> Thm.implies_intr wfR'
    |> Thm.forall_intr R'
    |> Thm.forall_elim inrel_R
    |> curry op RS wf_in_rel
    |> full_simplify (put_simpset HOL_basic_ss ctxt' addsimps [in_rel_def])
    |> Thm.forall_intr_name ("R", Rrel)
  end



fun prepare_function config defname [((fname, fT), mixfix)] abstract_qglrs lthy =
  let
    val FunctionConfig {domintros, default=default_opt, ...} = config

    val default_str = the_default "%x. HOL.undefined" (* FIXME proper term!? *) default_opt
    val fvar = (Binding.name_of fname, fT)
    val domT = domain_type fT
    val ranT = range_type fT

    val default = Syntax.parse_term lthy default_str
      |> Type.constraint fT |> Syntax.check_term lthy

    val (globals, ctxt') = fix_globals domT ranT (Free fvar) lthy

    val Globals { x, h, ... } = globals

    val clauses = map (mk_clause_context x ctxt') abstract_qglrs

    val n = length abstract_qglrs

    fun build_tree (ClauseContext { ctxt, rhs, ...}) =
       Function_Context_Tree.mk_tree (Free fvar) h ctxt rhs

    val trees = map build_tree clauses
    val RCss = map find_calls trees

    val ((G, GIntro_thms, G_elim, G_induct), lthy) =
      PROFILE "def_graph"
        (define_graph
          (derived_name_suffix defname "_graph", domT --> ranT --> boolT) (Free fvar) clauses RCss)
        lthy

    val ((f, (_, f_defthm)), lthy) =
      PROFILE "def_fun" (define_function defname (fname, mixfix) domT ranT G default) lthy

    val RCss = map (map (inst_RC lthy (Free fvar) f)) RCss
    val trees = map (Function_Context_Tree.inst_tree lthy (Free fvar) f) trees

    val ((R, RIntro_thmss, R_elim), lthy) =
      PROFILE "def_rel"
        (define_recursion_relation (derived_name_suffix defname "_rel", domT --> domT --> boolT)
          abstract_qglrs clauses RCss) lthy

    val dom = mk_acc domT R
    val (_, lthy) =
      Local_Theory.abbrev Syntax.mode_default
        ((derived_name_suffix defname "_dom", NoSyn), dom) lthy

    val newthy = Proof_Context.theory_of lthy
    val clauses = map (transfer_clause_ctx newthy) clauses

    val xclauses = PROFILE "xclauses"
      (@{map 7} (mk_clause_info globals G f) (1 upto n) clauses abstract_qglrs trees
        RCss GIntro_thms) RIntro_thmss

    val complete =
      mk_completeness globals clauses abstract_qglrs |> Thm.cterm_of lthy |> Thm.assume

    val compat =
      mk_compat_proof_obligations domT ranT (Free fvar) f abstract_qglrs
      |> map (Thm.cterm_of lthy #> Thm.assume)

    val compat_store = store_compat_thms n compat

    val (goalstate, values) = PROFILE "prove_stuff"
      (prove_stuff lthy globals G f R xclauses complete compat
         compat_store G_elim) f_defthm

    fun mk_partial_rules newctxt provedgoal =
      let
        val (graph_is_function, complete_thm) =
          provedgoal
          |> Conjunction.elim
          |> apfst (Thm.forall_elim_vars 0)

        val f_iff = graph_is_function RS (f_defthm RS ex1_implies_iff)

        val psimps = PROFILE "Proving simplification rules"
          (mk_psimps newctxt globals R xclauses values f_iff) graph_is_function

        val simple_pinduct = PROFILE "Proving partial induction rule"
          (mk_partial_induct_rule newctxt globals R complete_thm) xclauses

        val total_intro = PROFILE "Proving nested termination rule"
          (mk_nest_term_rule newctxt globals R R_elim) xclauses

        val dom_intros =
          if domintros then SOME (PROFILE "Proving domain introduction rules"
             (map (mk_domain_intro lthy globals R R_elim)) xclauses)
           else NONE
      in
        FunctionResult {fs=[f], G=G, R=R, dom=dom,
          cases=[complete_thm], psimps=psimps, pelims=[],
          simple_pinducts=[simple_pinduct],
          termination=total_intro, domintros=dom_intros}
      end
  in
    ((f, goalstate, mk_partial_rules), lthy)
  end

end
