(*  Title:      HOL/Tools/Metis/metis_reconstruct.ML
    Author:     Kong W. Susanto, Cambridge University Computer Laboratory
    Author:     Lawrence C. Paulson, Cambridge University Computer Laboratory
    Author:     Jasmin Blanchette, TU Muenchen
    Copyright   Cambridge University 2007

Proof reconstruction for Metis.
*)

signature METIS_RECONSTRUCT =
sig
  type type_enc = ATP_Problem_Generate.type_enc

  exception METIS_RECONSTRUCT of string * string

  val hol_term_of_metis : Proof.context -> type_enc -> int Symtab.table ->
    Metis_Term.term -> term
  val hol_clause_of_metis : Proof.context -> type_enc -> int Symtab.table ->
    (string * term) list * (string * term) list -> Metis_Thm.thm -> term
  val lookth : (Metis_Thm.thm * 'a) list -> Metis_Thm.thm -> 'a
  val replay_one_inference : Proof.context -> type_enc ->
    (string * term) list * (string * term) list -> int Symtab.table ->
    Metis_Thm.thm * Metis_Proof.inference -> (Metis_Thm.thm * thm) list ->
    (Metis_Thm.thm * thm) list
  val discharge_skolem_premises : Proof.context -> (thm * term) option list -> thm -> thm
end;

structure Metis_Reconstruct : METIS_RECONSTRUCT =
struct

open ATP_Problem
open ATP_Problem_Generate
open ATP_Proof_Reconstruct
open Metis_Generate

exception METIS_RECONSTRUCT of string * string

val meta_not_not = @{thms not_not[THEN eq_reflection]}

fun atp_name_of_metis type_enc s =
  (case find_first (fn (_, (f, _)) => f type_enc = s) metis_name_table of
    SOME ((s, _), (_, swap)) => (s, swap)
  | _ => (s, false))

fun atp_term_of_metis type_enc (Metis_Term.Fn (s, tms)) =
      let val (s, swap) = atp_name_of_metis type_enc (Metis_Name.toString s)
      in ATerm ((s, []), tms |> map (atp_term_of_metis type_enc) |> swap ? rev) end
  | atp_term_of_metis _ (Metis_Term.Var s) =
      ATerm ((Metis_Name.toString s, []), [])

fun hol_term_of_metis ctxt type_enc sym_tab =
  atp_term_of_metis type_enc #> term_of_atp ctxt ATP_Problem.CNF type_enc false sym_tab NONE

fun atp_literal_of_metis type_enc (pos, atom) =
  atom |> Metis_Term.Fn |> atp_term_of_metis type_enc
       |> AAtom |> not pos ? mk_anot

fun atp_clause_of_metis _ [] = AAtom (ATerm ((tptp_false, []), []))
  | atp_clause_of_metis type_enc lits =
    lits |> map (atp_literal_of_metis type_enc) |> mk_aconns AOr

fun polish_hol_terms ctxt (lifted, old_skolems) =
  map (reveal_lam_lifted lifted #> reveal_old_skolem_terms old_skolems) #>
  Type_Infer_Context.infer_types_finished (Proof_Context.set_mode Proof_Context.mode_pattern ctxt)

fun hol_clause_of_metis ctxt type_enc sym_tab concealed =
  Metis_Thm.clause
  #> Metis_LiteralSet.toList
  #> atp_clause_of_metis type_enc
  #> prop_of_atp ctxt ATP_Problem.CNF type_enc false sym_tab
  #> singleton (polish_hol_terms ctxt concealed)

fun hol_terms_of_metis ctxt type_enc concealed sym_tab fol_tms =
  let
    val ts = map (hol_term_of_metis ctxt type_enc sym_tab) fol_tms
    val _ = trace_msg ctxt (fn () => "  calling type inference:")
    val _ = List.app (fn t => trace_msg ctxt (fn () => Syntax.string_of_term ctxt t)) ts
    val ts' = ts |> polish_hol_terms ctxt concealed
    val _ = List.app (fn t => trace_msg ctxt
                  (fn () => "  final term: " ^ Syntax.string_of_term ctxt t ^
                            " of type " ^ Syntax.string_of_typ ctxt (type_of t))) ts'
  in ts' end
  handle ERROR msg => raise METIS_RECONSTRUCT ("hol_terms_of_metis", msg)



(** FOL step Inference Rules **)

fun lookth th_pairs fol_th =
  (case AList.lookup (uncurry Metis_Thm.equal) th_pairs fol_th of
    SOME th => th
  | NONE => raise Fail ("Failed to find Metis theorem " ^ Metis_Thm.toString fol_th))

fun cterm_incr_types ctxt idx =
  Thm.cterm_of ctxt o map_types (Logic.incr_tvar idx)


(* INFERENCE RULE: AXIOM *)

(*This causes variables to have an index of 1 by default. See also
  "term_of_atp" in "ATP_Proof_Reconstruct".*)
val axiom_inference = Thm.incr_indexes 1 oo lookth


(* INFERENCE RULE: ASSUME *)

fun excluded_middle P =
  \<^instantiate>\<open>P in lemma (open) \<open>P \<Longrightarrow> \<not> P \<Longrightarrow> False\<close> by (rule notE)\<close>

fun assume_inference ctxt type_enc concealed sym_tab atom =
  singleton (hol_terms_of_metis ctxt type_enc concealed sym_tab) (Metis_Term.Fn atom)
  |> Thm.cterm_of ctxt |> excluded_middle


(* INFERENCE RULE: INSTANTIATE (SUBST). *)

(*Type instantiations are ignored. Trying to reconstruct them admits new
  possibilities of errors, e.g. concerning sorts. Instead we try to arrange
  hat new TVars are distinct and that types can be inferred from terms.*)

fun inst_inference ctxt type_enc concealed sym_tab th_pairs fsubst th =
  let
    val i_th = lookth th_pairs th
    val i_th_vars = Term.add_vars (Thm.prop_of i_th) []

    fun find_var x = the (List.find (fn ((a,_),_) => a=x) i_th_vars)
    fun subst_translation (x,y) =
      let
        val v = find_var x
        (*We call "polish_hol_terms" below.*)
        val t = hol_term_of_metis ctxt type_enc sym_tab y
      in
        SOME (Thm.cterm_of ctxt (Var v), t)
      end
      handle Option.Option =>
             (trace_msg ctxt (fn () =>
                "\"find_var\" failed for " ^ x ^ " in " ^ Thm.string_of_thm ctxt i_th);
              NONE)
           | TYPE _ =>
             (trace_msg ctxt (fn () =>
                "\"hol_term_of_metis\" failed for " ^ x ^ " in " ^ Thm.string_of_thm ctxt i_th);
              NONE)
    fun remove_typeinst (a, t) =
      let val a = Metis_Name.toString a in
        (case unprefix_and_unascii schematic_var_prefix a of
          SOME b => SOME (b, t)
        | NONE =>
          (case unprefix_and_unascii tvar_prefix a of
            SOME _ => NONE (*type instantiations are forbidden*)
          | NONE => SOME (a, t) (*internal Metis var?*)))
      end
    val _ = trace_msg ctxt (fn () => "  isa th: " ^ Thm.string_of_thm ctxt i_th)
    val substs = map_filter remove_typeinst (Metis_Subst.toList fsubst)
    val (vars, tms) =
      ListPair.unzip (map_filter subst_translation substs)
      ||> polish_hol_terms ctxt concealed
    val ctm_of = cterm_incr_types ctxt (Thm.maxidx_of i_th + 1)
    val substs' = ListPair.zip (vars, map ctm_of tms)
    val _ = trace_msg ctxt (fn () =>
      cat_lines ("subst_translations:" ::
        (substs' |> map (fn (x, y) =>
          Syntax.string_of_term ctxt (Thm.term_of x) ^ " |-> " ^
          Syntax.string_of_term ctxt (Thm.term_of y)))))
  in
    infer_instantiate_types ctxt (map (apfst (dest_Var o Thm.term_of)) substs') i_th
  end
  handle THM (msg, _, _) => raise METIS_RECONSTRUCT ("inst_inference", msg)
       | ERROR msg => raise METIS_RECONSTRUCT ("inst_inference", msg)


(* INFERENCE RULE: RESOLVE *)

(*Increment the indexes of only the type variables*)
fun incr_type_indexes ctxt inc th =
  let
    val tvs = Term.add_tvars (Thm.full_prop_of th) []
    fun inc_tvar ((a, i), s) = (((a, i), s), Thm.ctyp_of ctxt (TVar ((a, i + inc), s)))
  in
    Thm.instantiate (TVars.make (map inc_tvar tvs), Vars.empty) th
  end

(*Like RSN, but we rename apart only the type variables. Vars here typically
  have an index of 1, and the use of RSN would increase this typically to 3.
  Instantiations of those Vars could then fail.*)
fun resolve_inc_tyvars ctxt th1 i th2 =
  let
    val th1' = incr_type_indexes ctxt (Thm.maxidx_of th2 + 1) th1
    fun res (tha, thb) =
      (case Thm.bicompose (SOME ctxt) {flatten = true, match = false, incremented = true}
            (false, Thm.close_derivation \<^here> tha, Thm.nprems_of tha) i thb
           |> Seq.list_of |> distinct Thm.eq_thm of
        [th] => th
      | _ =>
        let
          val thaa'bb' as [(tha', _), (thb', _)] =
            map (`(Local_Defs.unfold0 ctxt meta_not_not)) [tha, thb]
        in
          if forall Thm.eq_thm_prop thaa'bb' then
            raise THM ("resolve_inc_tyvars: unique result expected", i, [tha, thb])
          else
            res (tha', thb')
        end)
  in
    res (th1', th2)
    handle TERM z =>
      let
        val tyenv = []
          |> fold (Term.add_vars o Thm.prop_of) [th1', th2]
          |> AList.group (op =)
          |> maps (fn ((s, _), T :: Ts) => map (fn T' => (Free (s, T), Free (s, T'))) Ts)
          |> rpair Envir.init
          |-> fold (Pattern.unify (Context.Proof ctxt))
          |> Envir.type_env
        val instT =
          TVars.build (tyenv |> Vartab.fold (fn (x, (S, T)) =>
            TVars.add ((x, S), Thm.ctyp_of ctxt (Envir.norm_type tyenv T))))
      in
        (*The unifier, which is invoked from "Thm.bicompose", will sometimes refuse to unify
          "?a::?'a" with "?a::?'b" or "?a::nat" and throw a "TERM" exception (with "add_ffpair" as
          first argument). We then perform unification of the types of variables by hand and try
          again. We could do this the first time around but this error occurs seldom and we don't
          want to break existing proofs in subtle ways or slow them down.*)
        if TVars.is_empty instT then raise TERM z
        else res (apply2 (Drule.instantiate_normalize (instT, Vars.empty)) (th1', th2))
      end
  end

fun s_not \<^Const_>\<open>Not for t\<close> = t
  | s_not t = HOLogic.mk_not t
fun simp_not_not \<^Const_>\<open>Trueprop for t\<close> = \<^Const>\<open>Trueprop for \<open>simp_not_not t\<close>\<close>
  | simp_not_not \<^Const_>\<open>Not for t\<close> = s_not (simp_not_not t)
  | simp_not_not t = t

val normalize_literal = simp_not_not o Envir.eta_contract

(*Find the relative location of an untyped term within a list of terms as a
  1-based index. Returns 0 in case of failure.*)
fun index_of_literal lit haystack =
  let
    fun match_lit normalize =
      HOLogic.dest_Trueprop #> normalize
      #> curry Term.aconv_untyped (lit |> normalize)
  in
    (case find_index (match_lit I) haystack of
       ~1 => find_index (match_lit (simp_not_not o Envir.eta_contract)) haystack
     | j => j) + 1
  end

(*Permute a rule's premises to move the i-th premise to the last position.*)
fun make_last i th =
  let val n = Thm.nprems_of th in
    if i >= 1 andalso i <= n then Thm.permute_prems (i - 1) 1 th
    else raise THM ("select_literal", i, [th])
  end

(*Maps a rule that ends "... ==> P ==> False" to "... ==> ~ P" while avoiding
  to create double negations. The "select" wrapper is a trick to ensure that
  "P ==> ~ False ==> False" is rewritten to "P ==> False", not to "~ P". We
  don't use this trick in general because it makes the proof object uglier than
  necessary. FIXME.*)
fun negate_head ctxt th =
  if exists (fn t => t aconv \<^prop>\<open>\<not> False\<close>) (Thm.prems_of th) then
    (th RS @{thm select_FalseI})
    |> fold (rewrite_rule ctxt o single) @{thms not_atomize_select atomize_not_select}
  else
    th |> fold (rewrite_rule ctxt o single) @{thms not_atomize atomize_not}

(* Maps the clause  [P1,...Pn]==>False to [P1,...,P(i-1),P(i+1),...Pn] ==> ~P *)
fun select_literal ctxt = negate_head ctxt oo make_last

fun resolve_inference ctxt type_enc concealed sym_tab th_pairs atom th1 th2 =
  let
    val (i_th1, i_th2) = apply2 (lookth th_pairs) (th1, th2)
    val _ = trace_msg ctxt (fn () =>
        "  isa th1 (pos): " ^ Thm.string_of_thm ctxt i_th1 ^ "\n\
        \  isa th2 (neg): " ^ Thm.string_of_thm ctxt i_th2)
  in
    (* Trivial cases where one operand is type info *)
    if Thm.eq_thm (TrueI, i_th1) then
      i_th2
    else if Thm.eq_thm (TrueI, i_th2) then
      i_th1
    else
      let
        val i_atom =
          singleton (hol_terms_of_metis ctxt type_enc concealed sym_tab) (Metis_Term.Fn atom)
        val _ = trace_msg ctxt (fn () => "  atom: " ^ Syntax.string_of_term ctxt i_atom)
      in
        (case index_of_literal (s_not i_atom) (Thm.prems_of i_th1) of
          0 => (trace_msg ctxt (fn () => "Failed to find literal in \"th1\""); i_th1)
        | j1 =>
          (trace_msg ctxt (fn () => "  index th1: " ^ string_of_int j1);
           (case index_of_literal i_atom (Thm.prems_of i_th2) of
             0 => (trace_msg ctxt (fn () => "Failed to find literal in \"th2\""); i_th2)
           | j2 =>
             (trace_msg ctxt (fn () => "  index th2: " ^ string_of_int j2);
              resolve_inc_tyvars ctxt (select_literal ctxt j1 i_th1) j2 i_th2
              handle TERM (s, _) => raise METIS_RECONSTRUCT ("resolve_inference", s)))))
      end
  end


(* INFERENCE RULE: REFL *)

val REFL_THM = Thm.incr_indexes 2 @{lemma "x \<noteq> x \<Longrightarrow> False" by (drule notE) (rule refl)}
val [refl_x] = Term.add_vars (Thm.prop_of REFL_THM) [];

fun refl_inference ctxt type_enc concealed sym_tab t =
  let
    val i_t = singleton (hol_terms_of_metis ctxt type_enc concealed sym_tab) t
    val _ = trace_msg ctxt (fn () => "  term: " ^ Syntax.string_of_term ctxt i_t)
    val c_t = cterm_incr_types ctxt (Thm.maxidx_of REFL_THM + 1) i_t
  in infer_instantiate_types ctxt [(refl_x, c_t)] REFL_THM end


(* INFERENCE RULE: EQUALITY *)

val subst_em = @{lemma "s = t \<Longrightarrow> P s \<Longrightarrow> \<not> P t \<Longrightarrow> False" by (erule notE) (erule subst)}
val ssubst_em = @{lemma "s = t \<Longrightarrow> P t \<Longrightarrow> \<not> P s \<Longrightarrow> False" by (erule notE) (erule ssubst)}

fun equality_inference ctxt type_enc concealed sym_tab (pos, atom) fp fr =
  let
    val m_tm = Metis_Term.Fn atom
    val [i_atom, i_tm] = hol_terms_of_metis ctxt type_enc concealed sym_tab [m_tm, fr]
    val _ = trace_msg ctxt (fn () => "sign of the literal: " ^ Bool.toString pos)
    fun replace_item_list lx 0 (_::ls) = lx::ls
      | replace_item_list lx i (l::ls) = l :: replace_item_list lx (i-1) ls
    fun path_finder_fail tm ps t =
      raise METIS_RECONSTRUCT ("equality_inference (path_finder)",
                "path = " ^ implode_space (map string_of_int ps) ^
                " isa-term: " ^ Syntax.string_of_term ctxt tm ^
                (case t of
                  SOME t => " fol-term: " ^ Metis_Term.toString t
                | NONE => ""))
    fun path_finder tm [] _ = (tm, Bound 0)
      | path_finder tm (p :: ps) (t as Metis_Term.Fn (s, ts)) =
          let
            val s = s |> Metis_Name.toString
                      |> perhaps (try (unprefix_and_unascii const_prefix
                                       #> the #> unmangled_const_name #> hd))
          in
            if s = metis_predicator orelse s = predicator_name orelse
               s = metis_systematic_type_tag orelse s = metis_ad_hoc_type_tag
               orelse s = type_tag_name then
              path_finder tm ps (nth ts p)
            else if s = metis_app_op orelse s = app_op_name then
              let
                val (tm1, tm2) = dest_comb tm
                val p' = p - (length ts - 2)
              in
                if p' = 0 then path_finder tm1 ps (nth ts p) ||> (fn y => y $ tm2)
                else path_finder tm2 ps (nth ts p) ||> (fn y => tm1 $ y)
              end
            else
              let
                val (tm1, args) = strip_comb tm
                val adjustment = length ts - length args
                val p' = if adjustment > p then p else p - adjustment
                val tm_p = nth args p'
                  handle General.Subscript => path_finder_fail tm (p :: ps) (SOME t)
                val _ = trace_msg ctxt (fn () =>
                    "path_finder: " ^ string_of_int p ^ "  " ^
                    Syntax.string_of_term ctxt tm_p)
                val (r, t) = path_finder tm_p ps (nth ts p)
              in (r, list_comb (tm1, replace_item_list t p' args)) end
          end
      | path_finder tm ps t = path_finder_fail tm ps (SOME t)
    val (tm_subst, body) = path_finder i_atom fp m_tm
    val tm_abs = Abs ("x", type_of tm_subst, body)
    val _ = trace_msg ctxt (fn () => "abstraction: " ^ Syntax.string_of_term ctxt tm_abs)
    val _ = trace_msg ctxt (fn () => "i_tm: " ^ Syntax.string_of_term ctxt i_tm)
    val _ = trace_msg ctxt (fn () => "located term: " ^ Syntax.string_of_term ctxt tm_subst)
    val maxidx = fold Term.maxidx_term [i_tm, tm_abs, tm_subst] ~1
    val subst' = Thm.incr_indexes (maxidx + 1) (if pos then subst_em else ssubst_em)
    val _ = trace_msg ctxt (fn () => "subst' " ^ Thm.string_of_thm ctxt subst')
    val eq_terms =
      map (apply2 (Thm.cterm_of ctxt))
        (ListPair.zip (Misc_Legacy.term_vars (Thm.prop_of subst'), [tm_abs, tm_subst, i_tm]))
  in
    infer_instantiate_types ctxt (map (apfst (dest_Var o Thm.term_of)) eq_terms) subst'
  end

val factor = Seq.hd o distinct_subgoals_tac

fun one_step ctxt type_enc concealed sym_tab th_pairs (fol_th, inference) =
  (case inference of
    Metis_Proof.Axiom _ =>
      axiom_inference th_pairs fol_th |> factor
  | Metis_Proof.Assume atom =>
      assume_inference ctxt type_enc concealed sym_tab atom
  | Metis_Proof.Metis_Subst (subst, th1) =>
      inst_inference ctxt type_enc concealed sym_tab th_pairs subst th1 |> factor
  | Metis_Proof.Resolve (atom, th1, th2) =>
      resolve_inference ctxt type_enc concealed sym_tab th_pairs atom th1 th2 |> factor
  | Metis_Proof.Refl tm =>
      refl_inference ctxt type_enc concealed sym_tab tm
  | Metis_Proof.Equality (lit, p, r) =>
      equality_inference ctxt type_enc concealed sym_tab lit p r)

fun flexflex_first_order ctxt th =
  (case Thm.tpairs_of th of
    [] => th
  | pairs =>
      let
        val thy = Proof_Context.theory_of ctxt
        val (tyenv, tenv) = fold (Pattern.first_order_match thy) pairs (Vartab.empty, Vartab.empty)

        fun mkT (v, (S, T)) = ((v, S), Thm.ctyp_of ctxt T)
        fun mk (v, (T, t)) = ((v, Envir.subst_type tyenv T), Thm.cterm_of ctxt t)

        val instsT = Vartab.fold (cons o mkT) tyenv []
        val insts = Vartab.fold (cons o mk) tenv []
      in
        Thm.instantiate (TVars.make instsT, Vars.make insts) th
      end
      handle THM _ => th)

fun is_metis_literal_genuine (_, (s, _)) =
  not (String.isPrefix class_prefix (Metis_Name.toString s))
fun is_isabelle_literal_genuine t =
  (case t of _ $ \<^Const_>\<open>Meson.skolem _ for _\<close> => false | _ => true)

fun count p xs = fold (fn x => if p x then Integer.add 1 else I) xs 0

(*Seldomly needed hack. A Metis clause is represented as a set, so duplicate
  disjuncts are impossible. In the Isabelle proof, in spite of efforts to
  eliminate them, duplicates sometimes appear with slightly different (but
  unifiable) types.*)
fun resynchronize ctxt fol_th th =
  let
    val num_metis_lits =
      count is_metis_literal_genuine (Metis_LiteralSet.toList (Metis_Thm.clause fol_th))
    val num_isabelle_lits = count is_isabelle_literal_genuine (Thm.prems_of th)
  in
    if num_metis_lits >= num_isabelle_lits then
      th
    else
      let
        val (prems0, concl) = th |> Thm.prop_of |> Logic.strip_horn
        val prems = prems0 |> map normalize_literal |> distinct Term.aconv_untyped
        val goal = Logic.list_implies (prems, concl)
        val ctxt' = fold Thm.declare_hyps (Thm.chyps_of th) ctxt
        val tac =
          cut_tac th 1 THEN
          rewrite_goals_tac ctxt' meta_not_not THEN
          ALLGOALS (assume_tac ctxt')
      in
        if length prems = length prems0 then
          raise METIS_RECONSTRUCT ("resynchronize", "Out of sync")
        else
          Goal.prove ctxt' [] [] goal (K tac)
          |> resynchronize ctxt' fol_th
      end
  end

fun replay_one_inference ctxt type_enc concealed sym_tab (fol_th, inf) th_pairs =
  if not (null th_pairs) andalso Thm.prop_of (snd (hd th_pairs)) aconv \<^prop>\<open>False\<close> then
    (*Isabelle sometimes identifies literals (premises) that are distinct in
      Metis (e.g., because of type variables). We give the Isabelle proof the
      benefice of the doubt.*)
    th_pairs
  else
    let
      val _ = trace_msg ctxt (fn () => "=============================================")
      val _ = trace_msg ctxt (fn () => "METIS THM: " ^ Metis_Thm.toString fol_th)
      val _ = trace_msg ctxt (fn () => "INFERENCE: " ^ Metis_Proof.inferenceToString inf)
      val th = one_step ctxt type_enc concealed sym_tab th_pairs (fol_th, inf)
        |> flexflex_first_order ctxt
        |> resynchronize ctxt fol_th
      val _ = trace_msg ctxt (fn () => "ISABELLE THM: " ^ Thm.string_of_thm ctxt th)
      val _ = trace_msg ctxt (fn () => "=============================================")
    in
      (fol_th, th) :: th_pairs
    end

(*It is normally sufficient to apply "assume_tac" to unify the conclusion with
  one of the premises. Unfortunately, this sometimes yields "Variable
  has two distinct types" errors. To avoid this, we instantiate the
  variables before applying "assume_tac". Typical constraints are of the form
    ?SK_a_b_c_x SK_d_e_f_y ... SK_a_b_c_x ... SK_g_h_i_z \<equiv>\<^sup>? SK_a_b_c_x,
  where the nonvariables are goal parameters.*)
fun unify_first_prem_with_concl ctxt i th =
  let
    val goal = Logic.get_goal (Thm.prop_of th) i |> Envir.beta_eta_contract
    val prem = goal |> Logic.strip_assums_hyp |> hd
    val concl = goal |> Logic.strip_assums_concl

    fun pair_untyped_aconv (t1, t2) (u1, u2) =
      Term.aconv_untyped (t1, u1) andalso Term.aconv_untyped (t2, u2)

    fun add_terms tp inst =
      if exists (pair_untyped_aconv tp) inst then inst
      else tp :: map (apsnd (subst_atomic [tp])) inst

    fun is_flex t =
      (case strip_comb t of
        (Var _, args) => forall is_Bound args
      | _ => false)

    fun unify_flex flex rigid =
      (case strip_comb flex of
        (Var (z as (_, T)), args) =>
        add_terms (Var z,
          fold_rev absdummy (take (length args) (binder_types T)) rigid)
      | _ => I)

    fun unify_potential_flex comb atom =
      if is_flex comb then unify_flex comb atom
      else if is_Var atom then add_terms (atom, comb)
      else I

    fun unify_terms (t, u) =
      (case (t, u) of
        (t1 $ t2, u1 $ u2) =>
        if is_flex t then unify_flex t u
        else if is_flex u then unify_flex u t
        else fold unify_terms [(t1, u1), (t2, u2)]
      | (_ $ _, _) => unify_potential_flex t u
      | (_, _ $ _) => unify_potential_flex u t
      | (Var _, _) => add_terms (t, u)
      | (_, Var _) => add_terms (u, t)
      | _ => I)

    val t_inst =
      [] |> try (unify_terms (prem, concl) #> map (apply2 (Thm.cterm_of ctxt)))
         |> the_default [] (* FIXME *)
  in
    infer_instantiate_types ctxt (map (apfst (dest_Var o Thm.term_of)) t_inst) th
  end

val copy_prem = @{lemma "P \<Longrightarrow> (P \<Longrightarrow> P \<Longrightarrow> Q) \<Longrightarrow> Q" by assumption}

fun copy_prems_tac ctxt [] ns i =
      if forall (curry (op =) 1) ns then all_tac else copy_prems_tac ctxt (rev ns) [] i
  | copy_prems_tac ctxt (1 :: ms) ns i = rotate_tac 1 i THEN copy_prems_tac ctxt ms (1 :: ns) i
  | copy_prems_tac ctxt (m :: ms) ns i =
      eresolve_tac ctxt [copy_prem] i THEN copy_prems_tac ctxt ms (m div 2 :: (m + 1) div 2 :: ns) i

(*Metis generates variables of the form _nnn.*)
val is_metis_fresh_variable = String.isPrefix "_"

fun instantiate_forall_tac ctxt t i st =
  let
    val params = Logic.strip_params (Logic.get_goal (Thm.prop_of st) i) |> rev

    fun repair (t as (Var ((s, _), _))) =
          (case find_index (fn (s', _) => s' = s) params of
            ~1 => t
          | j => Bound j)
      | repair (t $ u) =
          (case (repair t, repair u) of
            (t as Bound j, u as Bound k) =>
            (*This is a trick to repair the discrepancy between the fully skolemized term that MESON
              gives us (where existentials were pulled out) and the reality.*)
            if k > j then t else t $ u
          | (t, u) => t $ u)
      | repair t = t

    val t' = t |> repair |> fold (absdummy o snd) params

    fun do_instantiate th =
      (case Term.add_vars (Thm.prop_of th) []
            |> filter_out ((Meson_Clausify.is_zapped_var_name orf is_metis_fresh_variable) o fst
              o fst) of
        [] => th
      | [var as (_, T)] =>
        let
          val var_binder_Ts = T |> binder_types |> take (length params) |> rev
          val var_body_T = T |> funpow (length params) range_type
          val tyenv =
            Vartab.empty |> Type.raw_unifys (fastype_of t :: map snd params,
                                             var_body_T :: var_binder_Ts)
          val env =
            Envir.Envir {maxidx = Vartab.fold (Integer.max o snd o fst) tyenv 0,
              tenv = Vartab.empty, tyenv = tyenv}
          val ty_inst =
            Vartab.fold (fn (x, (S, T)) => cons (((x, S), Thm.ctyp_of ctxt T)))
              tyenv []
          val t_inst = [apply2 (Thm.cterm_of ctxt o Envir.norm_term env) (Var var, t')]
        in
          Drule.instantiate_normalize
            (TVars.make ty_inst, Vars.make (map (apfst (dest_Var o Thm.term_of)) t_inst)) th
        end
      | _ => raise Fail "expected a single non-zapped, non-Metis Var")
  in
    (DETERM (eresolve_tac ctxt @{thms allE} i THEN rotate_tac ~1 i) THEN PRIMITIVE do_instantiate) st
  end

fun fix_exists_tac ctxt t = eresolve_tac ctxt [exE] THEN' rename_tac [t |> dest_Var |> fst |> fst]

fun release_quantifier_tac ctxt (skolem, t) =
  (if skolem then fix_exists_tac ctxt else instantiate_forall_tac ctxt) t

fun release_clusters_tac _ _ _ [] = K all_tac
  | release_clusters_tac ctxt ax_counts substs ((ax_no, cluster_no) :: clusters) =
    let
      val cluster_of_var = Meson_Clausify.cluster_of_zapped_var_name o fst o fst o dest_Var
      fun in_right_cluster ((_, (cluster_no', _)), _) = cluster_no' = cluster_no
      val cluster_substs =
        substs
        |> map_filter (fn (ax_no', (_, (_, tsubst))) =>
                          if ax_no' = ax_no then
                            tsubst |> map (apfst cluster_of_var)
                                   |> filter (in_right_cluster o fst)
                                   |> map (apfst snd)
                                   |> SOME
                          else
                            NONE)
      fun do_cluster_subst cluster_subst =
        map (release_quantifier_tac ctxt) cluster_subst @ [rotate_tac 1]
      val first_prem = find_index (fn (ax_no', _) => ax_no' = ax_no) substs
    in
      rotate_tac first_prem
      THEN' (EVERY' (maps do_cluster_subst cluster_substs))
      THEN' rotate_tac (~ first_prem - length cluster_substs)
      THEN' release_clusters_tac ctxt ax_counts substs clusters
    end

fun cluster_key ((ax_no, (cluster_no, index_no)), skolem) =
  (ax_no, (cluster_no, (skolem, index_no)))
fun cluster_ord p =
  prod_ord int_ord (prod_ord int_ord (prod_ord bool_ord int_ord)) (apply2 cluster_key p)

val tysubst_ord =
  list_ord (prod_ord Term_Ord.fast_indexname_ord (prod_ord Term_Ord.sort_ord Term_Ord.typ_ord))

structure Int_Tysubst_Table = Table
(
  type key = int * (indexname * (sort * typ)) list
  val ord = prod_ord int_ord tysubst_ord
)

structure Int_Pair_Graph = Graph(
  type key = int * int
  val ord = prod_ord int_ord int_ord
)

fun shuffle_key (((axiom_no, (_, index_no)), _), _) = (axiom_no, index_no)
fun shuffle_ord p = prod_ord int_ord int_ord (apply2 shuffle_key p)

(*Attempts to derive the theorem "False" from a theorem of the form
  "P1 ==> ... ==> Pn ==> False", where the "Pi"s are to be discharged using the
  specified axioms. The axioms have leading "All" and "Ex" quantifiers, which
  must be eliminated first.*)
fun discharge_skolem_premises ctxt axioms prems_imp_false =
  if Thm.prop_of prems_imp_false aconv \<^prop>\<open>False\<close> then prems_imp_false
  else
    let
      val thy = Proof_Context.theory_of ctxt

      fun match_term p =
        let
          val (tyenv, tenv) =
            Pattern.first_order_match thy p (Vartab.empty, Vartab.empty)
          val tsubst =
            tenv |> Vartab.dest
                 |> filter (Meson_Clausify.is_zapped_var_name o fst o fst)
                 |> sort (cluster_ord
                          o apply2 (Meson_Clausify.cluster_of_zapped_var_name
                                      o fst o fst))
                 |> map (fn (xi, (T, t)) => apply2 (Envir.subst_term_types tyenv) (Var (xi, T), t))
          val tysubst = tyenv |> Vartab.dest
        in (tysubst, tsubst) end

      fun subst_info_of_prem subgoal_no prem =
        (case prem of
          _ $ \<^Const_>\<open>Meson.skolem _ for \<open>_ $ t $ num\<close>\<close> =>
            let val ax_no = HOLogic.dest_nat num in
              (ax_no, (subgoal_no,
                       match_term (nth axioms ax_no |> the |> snd, t)))
            end
        | _ => raise TERM ("discharge_skolem_premises: Malformed premise", [prem]))

      fun cluster_of_var_name skolem s =
        (case try Meson_Clausify.cluster_of_zapped_var_name s of
          NONE => NONE
        | SOME ((ax_no, (cluster_no, _)), skolem') =>
          if skolem' = skolem andalso cluster_no > 0 then SOME (ax_no, cluster_no) else NONE)

      fun clusters_in_term skolem t =
        Term.add_var_names t [] |> map_filter (cluster_of_var_name skolem o fst)

      fun deps_of_term_subst (var, t) =
        (case clusters_in_term false var of
          [] => NONE
        | [(ax_no, cluster_no)] =>
          SOME ((ax_no, cluster_no),
            clusters_in_term true t |> cluster_no > 1 ? cons (ax_no, cluster_no - 1))
        | _ => raise TERM ("discharge_skolem_premises: Expected Var", [var]))
      val prems = Logic.strip_imp_prems (Thm.prop_of prems_imp_false)
      val substs =
        map_index (fn (i, prem) => subst_info_of_prem (i + 1) prem) prems
        |> sort (int_ord o apply2 fst)
      val depss = maps (map_filter deps_of_term_subst o snd o snd o snd) substs
      val clusters = maps (op ::) depss
      val ordered_clusters =
        Int_Pair_Graph.empty
        |> fold Int_Pair_Graph.default_node (map (rpair ()) clusters)
        |> fold Int_Pair_Graph.add_deps_acyclic depss
        |> Int_Pair_Graph.topological_order
        handle Int_Pair_Graph.CYCLES _ =>
               error "Cannot replay Metis proof in Isabelle without \"Hilbert_Choice\""
      val ax_counts =
        Int_Tysubst_Table.empty
        |> fold (fn (ax_no, (_, (tysubst, _))) =>
                    Int_Tysubst_Table.map_default ((ax_no, tysubst), 0)
                                                  (Integer.add 1)) substs
        |> Int_Tysubst_Table.dest
      val needed_axiom_props =
        map_index I axioms
        |> map_filter (fn (_, NONE) => NONE
                        | (ax_no, SOME (_, t)) =>
                          if exists (fn ((ax_no', _), n) =>
                                        ax_no' = ax_no andalso n > 0)
                                    ax_counts then
                            SOME t
                          else
                            NONE)
      val outer_param_names =
        [] |> fold Term.add_var_names needed_axiom_props
           |> filter (Meson_Clausify.is_zapped_var_name o fst)
           |> map (`(Meson_Clausify.cluster_of_zapped_var_name o fst))
           |> filter (fn (((_, (cluster_no, _)), skolem), _) =>
                         cluster_no = 0 andalso skolem)
           |> sort shuffle_ord |> map (fst o snd)

(* for debugging only:
      fun string_of_subst_info (ax_no, (subgoal_no, (tysubst, tsubst))) =
        "ax: " ^ string_of_int ax_no ^ "; asm: " ^ string_of_int subgoal_no ^
        "; tysubst: " ^ @{make_string} tysubst ^ "; tsubst: {" ^
        commas (map ((fn (s, t) => s ^ " |-> " ^ t)
                     o apply2 (Syntax.string_of_term ctxt)) tsubst) ^ "}"
      val _ = tracing ("ORDERED CLUSTERS: " ^ @{make_string} ordered_clusters)
      val _ = tracing ("AXIOM COUNTS: " ^ @{make_string} ax_counts)
      val _ = tracing ("OUTER PARAMS: " ^ @{make_string} outer_param_names)
      val _ = tracing ("SUBSTS (" ^ string_of_int (length substs) ^ "):\n" ^
                       cat_lines (map string_of_subst_info substs))
*)
      val ctxt' = fold Thm.declare_hyps (Thm.chyps_of prems_imp_false) ctxt

      fun cut_and_ex_tac axiom =
        cut_tac axiom 1 THEN TRY (REPEAT_ALL_NEW (eresolve_tac ctxt' @{thms exE}) 1)
      fun rotation_of_subgoal i =
        find_index (fn (_, (subgoal_no, _)) => subgoal_no = i) substs
    in
      Goal.prove ctxt' [] [] \<^prop>\<open>False\<close>
        (K (DETERM (EVERY (map (cut_and_ex_tac o fst o the o nth axioms o fst o fst) ax_counts)
              THEN rename_tac outer_param_names 1
              THEN copy_prems_tac ctxt' (map snd ax_counts) [] 1)
            THEN release_clusters_tac ctxt' ax_counts substs ordered_clusters 1
            THEN match_tac ctxt' [prems_imp_false] 1
            THEN ALLGOALS (fn i => resolve_tac ctxt' @{thms Meson.skolem_COMBK_I} i
              THEN rotate_tac (rotation_of_subgoal i) i
              THEN PRIMITIVE (unify_first_prem_with_concl ctxt' i)
              THEN assume_tac ctxt' i
              THEN flexflex_tac ctxt')))
      handle ERROR msg =>
        cat_error msg
          "Cannot replay Metis proof in Isabelle: error when discharging Skolem assumptions"
    end

end;
