(*  Title:      HOL/Tools/TFL/rules.ML
    Author:     Konrad Slind, Cambridge University Computer Laboratory

Emulation of HOL inference rules for TFL.
*)

signature RULES =
sig
  val dest_thm: thm -> term list * term

  (* Inference rules *)
  val REFL: cterm -> thm
  val ASSUME: cterm -> thm
  val MP: thm -> thm -> thm
  val MATCH_MP: thm -> thm -> thm
  val CONJUNCT1: thm -> thm
  val CONJUNCT2: thm -> thm
  val CONJUNCTS: thm -> thm list
  val DISCH: cterm -> thm -> thm
  val UNDISCH: thm  -> thm
  val SPEC: cterm -> thm -> thm
  val ISPEC: cterm -> thm -> thm
  val ISPECL: cterm list -> thm -> thm
  val GEN: cterm -> thm -> thm
  val GENL: cterm list -> thm -> thm
  val LIST_CONJ: thm list -> thm

  val SYM: thm -> thm
  val DISCH_ALL: thm -> thm
  val FILTER_DISCH_ALL: (term -> bool) -> thm -> thm
  val SPEC_ALL: thm -> thm
  val GEN_ALL: thm -> thm
  val IMP_TRANS: thm -> thm -> thm
  val PROVE_HYP: thm -> thm -> thm

  val CHOOSE: cterm * thm -> thm -> thm
  val EXISTS: cterm * cterm -> thm -> thm
  val EXISTL: cterm list -> thm -> thm
  val IT_EXISTS: (cterm*cterm) list -> thm -> thm

  val EVEN_ORS: thm list -> thm list
  val DISJ_CASESL: thm -> thm list -> thm

  val list_beta_conv: cterm -> cterm list -> thm
  val SUBS: thm list -> thm -> thm
  val simpl_conv: simpset -> thm list -> cterm -> thm

  val rbeta: thm -> thm
  val tracing: bool Unsynchronized.ref
  val CONTEXT_REWRITE_RULE: term * term list * thm * thm list
                             -> thm -> thm * term list
  val RIGHT_ASSOC: thm -> thm

  val prove: bool -> cterm * tactic -> thm
end;

structure Rules: RULES =
struct

fun RULES_ERR func mesg = Utils.ERR {module = "Rules", func = func, mesg = mesg};


fun cconcl thm = Dcterm.drop_prop (#prop (Thm.crep_thm thm));
fun chyps thm = map Dcterm.drop_prop (#hyps (Thm.crep_thm thm));

fun dest_thm thm =
  let val {prop,hyps,...} = Thm.rep_thm thm
  in (map HOLogic.dest_Trueprop hyps, HOLogic.dest_Trueprop prop) end
  handle TERM _ => raise RULES_ERR "dest_thm" "missing Trueprop";


(* Inference rules *)

(*---------------------------------------------------------------------------
 *        Equality (one step)
 *---------------------------------------------------------------------------*)

fun REFL tm = Thm.reflexive tm RS meta_eq_to_obj_eq
  handle THM (msg, _, _) => raise RULES_ERR "REFL" msg;

fun SYM thm = thm RS sym
  handle THM (msg, _, _) => raise RULES_ERR "SYM" msg;

fun ALPHA thm ctm1 =
  let
    val ctm2 = Thm.cprop_of thm;
    val ctm2_eq = Thm.reflexive ctm2;
    val ctm1_eq = Thm.reflexive ctm1;
  in Thm.equal_elim (Thm.transitive ctm2_eq ctm1_eq) thm end
  handle THM (msg, _, _) => raise RULES_ERR "ALPHA" msg;

fun rbeta th =
  (case Dcterm.strip_comb (cconcl th) of
    (_, [l, r]) => Thm.transitive th (Thm.beta_conversion false r)
  | _ => raise RULES_ERR "rbeta" "");


(*----------------------------------------------------------------------------
 *        Implication and the assumption list
 *
 * Assumptions get stuck on the meta-language assumption list. Implications
 * are in the object language, so discharging an assumption "A" from theorem
 * "B" results in something that looks like "A --> B".
 *---------------------------------------------------------------------------*)

fun ASSUME ctm = Thm.assume (Dcterm.mk_prop ctm);


(*---------------------------------------------------------------------------
 * Implication in TFL is -->. Meta-language implication (==>) is only used
 * in the implementation of some of the inference rules below.
 *---------------------------------------------------------------------------*)
fun MP th1 th2 = th2 RS (th1 RS mp)
  handle THM (msg, _, _) => raise RULES_ERR "MP" msg;

(*forces the first argument to be a proposition if necessary*)
fun DISCH tm thm = Thm.implies_intr (Dcterm.mk_prop tm) thm COMP impI
  handle THM (msg, _, _) => raise RULES_ERR "DISCH" msg;

fun DISCH_ALL thm = fold_rev DISCH (#hyps (Thm.crep_thm thm)) thm;


fun FILTER_DISCH_ALL P thm =
 let fun check tm = P (#t (Thm.rep_cterm tm))
 in  fold_rev (fn tm => fn th => if check tm then DISCH tm th else th) (chyps thm) thm
 end;

fun UNDISCH thm =
   let val tm = Dcterm.mk_prop (#1 (Dcterm.dest_imp (cconcl thm)))
   in Thm.implies_elim (thm RS mp) (ASSUME tm) end
   handle Utils.ERR _ => raise RULES_ERR "UNDISCH" ""
     | THM _ => raise RULES_ERR "UNDISCH" "";

fun PROVE_HYP ath bth = MP (DISCH (cconcl ath) bth) ath;

fun IMP_TRANS th1 th2 = th2 RS (th1 RS Thms.imp_trans)
  handle THM (msg, _, _) => raise RULES_ERR "IMP_TRANS" msg;


(*----------------------------------------------------------------------------
 *        Conjunction
 *---------------------------------------------------------------------------*)

fun CONJUNCT1 thm = thm RS conjunct1
  handle THM (msg, _, _) => raise RULES_ERR "CONJUNCT1" msg;

fun CONJUNCT2 thm = thm RS conjunct2
  handle THM (msg, _, _) => raise RULES_ERR "CONJUNCT2" msg;

fun CONJUNCTS th = CONJUNCTS (CONJUNCT1 th) @ CONJUNCTS (CONJUNCT2 th) handle Utils.ERR _ => [th];

fun LIST_CONJ [] = raise RULES_ERR "LIST_CONJ" "empty list"
  | LIST_CONJ [th] = th
  | LIST_CONJ (th :: rst) = MP (MP (conjI COMP (impI RS impI)) th) (LIST_CONJ rst)
      handle THM (msg, _, _) => raise RULES_ERR "LIST_CONJ" msg;


(*----------------------------------------------------------------------------
 *        Disjunction
 *---------------------------------------------------------------------------*)
local val thy = Thm.theory_of_thm disjI1
      val prop = Thm.prop_of disjI1
      val [P,Q] = Misc_Legacy.term_vars prop
      val disj1 = Thm.forall_intr (Thm.cterm_of thy Q) disjI1
in
fun DISJ1 thm tm = thm RS (Thm.forall_elim (Dcterm.drop_prop tm) disj1)
  handle THM (msg, _, _) => raise RULES_ERR "DISJ1" msg;
end;

local val thy = Thm.theory_of_thm disjI2
      val prop = Thm.prop_of disjI2
      val [P,Q] = Misc_Legacy.term_vars prop
      val disj2 = Thm.forall_intr (Thm.cterm_of thy P) disjI2
in
fun DISJ2 tm thm = thm RS (Thm.forall_elim (Dcterm.drop_prop tm) disj2)
  handle THM (msg, _, _) => raise RULES_ERR "DISJ2" msg;
end;


(*----------------------------------------------------------------------------
 *
 *                   A1 |- M1, ..., An |- Mn
 *     ---------------------------------------------------
 *     [A1 |- M1 \/ ... \/ Mn, ..., An |- M1 \/ ... \/ Mn]
 *
 *---------------------------------------------------------------------------*)


fun EVEN_ORS thms =
  let fun blue ldisjs [] _ = []
        | blue ldisjs (th::rst) rdisjs =
            let val tail = tl rdisjs
                val rdisj_tl = Dcterm.list_mk_disj tail
            in fold_rev DISJ2 ldisjs (DISJ1 th rdisj_tl)
               :: blue (ldisjs @ [cconcl th]) rst tail
            end handle Utils.ERR _ => [fold_rev DISJ2 ldisjs th]
   in blue [] thms (map cconcl thms) end;


(*----------------------------------------------------------------------------
 *
 *         A |- P \/ Q   B,P |- R    C,Q |- R
 *     ---------------------------------------------------
 *                     A U B U C |- R
 *
 *---------------------------------------------------------------------------*)

fun DISJ_CASES th1 th2 th3 =
  let
    val c = Dcterm.drop_prop (cconcl th1);
    val (disj1, disj2) = Dcterm.dest_disj c;
    val th2' = DISCH disj1 th2;
    val th3' = DISCH disj2 th3;
  in
    th3' RS (th2' RS (th1 RS Thms.tfl_disjE))
      handle THM (msg, _, _) => raise RULES_ERR "DISJ_CASES" msg
  end;


(*-----------------------------------------------------------------------------
 *
 *       |- A1 \/ ... \/ An     [A1 |- M, ..., An |- M]
 *     ---------------------------------------------------
 *                           |- M
 *
 * Note. The list of theorems may be all jumbled up, so we have to
 * first organize it to align with the first argument (the disjunctive
 * theorem).
 *---------------------------------------------------------------------------*)

fun organize eq =    (* a bit slow - analogous to insertion sort *)
 let fun extract a alist =
     let fun ex (_,[]) = raise RULES_ERR "organize" "not a permutation.1"
           | ex(left,h::t) = if (eq h a) then (h,rev left@t) else ex(h::left,t)
     in ex ([],alist)
     end
     fun place [] [] = []
       | place (a::rst) alist =
           let val (item,next) = extract a alist
           in item::place rst next
           end
       | place _ _ = raise RULES_ERR "organize" "not a permutation.2"
 in place
 end;

fun DISJ_CASESL disjth thl =
   let val c = cconcl disjth
       fun eq th atm = exists (fn t => HOLogic.dest_Trueprop t aconv term_of atm) (Thm.hyps_of th)
       val tml = Dcterm.strip_disj c
       fun DL th [] = raise RULES_ERR "DISJ_CASESL" "no cases"
         | DL th [th1] = PROVE_HYP th th1
         | DL th [th1,th2] = DISJ_CASES th th1 th2
         | DL th (th1::rst) =
            let val tm = #2 (Dcterm.dest_disj (Dcterm.drop_prop(cconcl th)))
             in DISJ_CASES th th1 (DL (ASSUME tm) rst) end
   in DL disjth (organize eq tml thl)
   end;


(*----------------------------------------------------------------------------
 *        Universals
 *---------------------------------------------------------------------------*)
local (* this is fragile *)
      val thy = Thm.theory_of_thm spec
      val prop = Thm.prop_of spec
      val x = hd (tl (Misc_Legacy.term_vars prop))
      val cTV = ctyp_of thy (type_of x)
      val gspec = Thm.forall_intr (cterm_of thy x) spec
in
fun SPEC tm thm =
   let val gspec' = Drule.instantiate_normalize ([(cTV, Thm.ctyp_of_term tm)], []) gspec
   in thm RS (Thm.forall_elim tm gspec') end
end;

fun SPEC_ALL thm = fold SPEC (#1 (Dcterm.strip_forall(cconcl thm))) thm;

val ISPEC = SPEC
val ISPECL = fold ISPEC;

(* Not optimized! Too complicated. *)
local val thy = Thm.theory_of_thm allI
      val prop = Thm.prop_of allI
      val [P] = Misc_Legacy.add_term_vars (prop, [])
      fun cty_theta s = map (fn (i, (S, ty)) => (ctyp_of s (TVar (i, S)), ctyp_of s ty))
      fun ctm_theta s = map (fn (i, (_, tm2)) =>
                             let val ctm2 = cterm_of s tm2
                             in (cterm_of s (Var(i,#T(rep_cterm ctm2))), ctm2)
                             end)
      fun certify s (ty_theta,tm_theta) =
        (cty_theta s (Vartab.dest ty_theta),
         ctm_theta s (Vartab.dest tm_theta))
in
fun GEN v th =
   let val gth = Thm.forall_intr v th
       val thy = Thm.theory_of_thm gth
       val Const("all",_)$Abs(x,ty,rst) = Thm.prop_of gth
       val P' = Abs(x,ty, HOLogic.dest_Trueprop rst)  (* get rid of trueprop *)
       val theta = Pattern.match thy (P,P') (Vartab.empty, Vartab.empty);
       val allI2 = Drule.instantiate_normalize (certify thy theta) allI
       val thm = Thm.implies_elim allI2 gth
       val tp $ (A $ Abs(_,_,M)) = Thm.prop_of thm
       val prop' = tp $ (A $ Abs(x,ty,M))
   in ALPHA thm (cterm_of thy prop')
   end
end;

val GENL = fold_rev GEN;

fun GEN_ALL thm =
   let val thy = Thm.theory_of_thm thm
       val prop = Thm.prop_of thm
       val tycheck = cterm_of thy
       val vlist = map tycheck (Misc_Legacy.add_term_vars (prop, []))
  in GENL vlist thm
  end;


fun MATCH_MP th1 th2 =
   if (Dcterm.is_forall (Dcterm.drop_prop(cconcl th1)))
   then MATCH_MP (th1 RS spec) th2
   else MP th1 th2;


(*----------------------------------------------------------------------------
 *        Existentials
 *---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------
 * Existential elimination
 *
 *      A1 |- ?x.t[x]   ,   A2, "t[v]" |- t'
 *      ------------------------------------     (variable v occurs nowhere)
 *                A1 u A2 |- t'
 *
 *---------------------------------------------------------------------------*)

fun CHOOSE (fvar, exth) fact =
  let
    val lam = #2 (Dcterm.dest_comb (Dcterm.drop_prop (cconcl exth)))
    val redex = Dcterm.capply lam fvar
    val thy = Thm.theory_of_cterm redex
    val t$u = Thm.term_of redex
    val residue = Thm.cterm_of thy (Term.betapply (t, u))
  in
    GEN fvar (DISCH residue fact) RS (exth RS Thms.choose_thm)
      handle THM (msg, _, _) => raise RULES_ERR "CHOOSE" msg
  end;

local val thy = Thm.theory_of_thm exI
      val prop = Thm.prop_of exI
      val [P,x] = Misc_Legacy.term_vars prop
in
fun EXISTS (template,witness) thm =
   let val thy = Thm.theory_of_thm thm
       val prop = Thm.prop_of thm
       val P' = cterm_of thy P
       val x' = cterm_of thy x
       val abstr = #2 (Dcterm.dest_comb template)
   in
   thm RS (cterm_instantiate[(P',abstr), (x',witness)] exI)
     handle THM (msg, _, _) => raise RULES_ERR "EXISTS" msg
   end
end;

(*----------------------------------------------------------------------------
 *
 *         A |- M
 *   -------------------   [v_1,...,v_n]
 *    A |- ?v1...v_n. M
 *
 *---------------------------------------------------------------------------*)

fun EXISTL vlist th =
  fold_rev (fn v => fn thm => EXISTS(Dcterm.mk_exists(v,cconcl thm), v) thm)
           vlist th;


(*----------------------------------------------------------------------------
 *
 *       A |- M[x_1,...,x_n]
 *   ----------------------------   [(x |-> y)_1,...,(x |-> y)_n]
 *       A |- ?y_1...y_n. M
 *
 *---------------------------------------------------------------------------*)
(* Could be improved, but needs "subst_free" for certified terms *)

fun IT_EXISTS blist th =
   let val thy = Thm.theory_of_thm th
       val tych = cterm_of thy
       val blist' = map (pairself Thm.term_of) blist
       fun ex v M  = cterm_of thy (USyntax.mk_exists{Bvar=v,Body = M})

  in
  fold_rev (fn (b as (r1,r2)) => fn thm =>
        EXISTS(ex r2 (subst_free [b]
                   (HOLogic.dest_Trueprop(Thm.prop_of thm))), tych r1)
              thm)
       blist' th
  end;

(*---------------------------------------------------------------------------
 *  Faster version, that fails for some as yet unknown reason
 * fun IT_EXISTS blist th =
 *    let val {thy,...} = rep_thm th
 *        val tych = cterm_of thy
 *        fun detype (x,y) = ((#t o rep_cterm) x, (#t o rep_cterm) y)
 *   in
 *  fold (fn (b as (r1,r2), thm) =>
 *  EXISTS(D.mk_exists(r2, tych(subst_free[detype b](#t(rep_cterm(cconcl thm))))),
 *           r1) thm)  blist th
 *   end;
 *---------------------------------------------------------------------------*)

(*----------------------------------------------------------------------------
 *        Rewriting
 *---------------------------------------------------------------------------*)

fun SUBS thl =
  rewrite_rule (map (fn th => th RS eq_reflection handle THM _ => th) thl);

val rew_conv = Raw_Simplifier.rewrite_cterm (true, false, false) (K (K NONE));

fun simpl_conv ss thl ctm =
 rew_conv (ss addsimps thl) ctm RS meta_eq_to_obj_eq;


val RIGHT_ASSOC = rewrite_rule [Thms.disj_assoc];



(*---------------------------------------------------------------------------
 *                  TERMINATION CONDITION EXTRACTION
 *---------------------------------------------------------------------------*)


(* Object language quantifier, i.e., "!" *)
fun Forall v M = USyntax.mk_forall{Bvar=v, Body=M};


(* Fragile: it's a cong if it is not "R y x ==> cut f R x y = f y" *)
fun is_cong thm =
  case (Thm.prop_of thm)
     of (Const("==>",_)$(Const(@{const_name Trueprop},_)$ _) $
         (Const("==",_) $ (Const (@{const_name Wfrec.cut},_) $ f $ R $ a $ x) $ _)) => false
      | _ => true;


fun dest_equal(Const ("==",_) $
               (Const (@{const_name Trueprop},_) $ lhs)
               $ (Const (@{const_name Trueprop},_) $ rhs)) = {lhs=lhs, rhs=rhs}
  | dest_equal(Const ("==",_) $ lhs $ rhs)  = {lhs=lhs, rhs=rhs}
  | dest_equal tm = USyntax.dest_eq tm;

fun get_lhs tm = #lhs(dest_equal (HOLogic.dest_Trueprop tm));

fun dest_all used (Const("all",_) $ (a as Abs _)) = USyntax.dest_abs used a
  | dest_all _ _ = raise RULES_ERR "dest_all" "not a !!";

val is_all = can (dest_all []);

fun strip_all used fm =
   if (is_all fm)
   then let val ({Bvar, Body}, used') = dest_all used fm
            val (bvs, core, used'') = strip_all used' Body
        in ((Bvar::bvs), core, used'')
        end
   else ([], fm, used);

fun break_all(Const("all",_) $ Abs (_,_,body)) = body
  | break_all _ = raise RULES_ERR "break_all" "not a !!";

fun list_break_all(Const("all",_) $ Abs (s,ty,body)) =
     let val (L,core) = list_break_all body
     in ((s,ty)::L, core)
     end
  | list_break_all tm = ([],tm);

(*---------------------------------------------------------------------------
 * Rename a term of the form
 *
 *      !!x1 ...xn. x1=M1 ==> ... ==> xn=Mn
 *                  ==> ((%v1...vn. Q) x1 ... xn = g x1 ... xn.
 * to one of
 *
 *      !!v1 ... vn. v1=M1 ==> ... ==> vn=Mn
 *      ==> ((%v1...vn. Q) v1 ... vn = g v1 ... vn.
 *
 * This prevents name problems in extraction, and helps the result to read
 * better. There is a problem with varstructs, since they can introduce more
 * than n variables, and some extra reasoning needs to be done.
 *---------------------------------------------------------------------------*)

fun get ([],_,L) = rev L
  | get (ant::rst,n,L) =
      case (list_break_all ant)
        of ([],_) => get (rst, n+1,L)
         | (vlist,body) =>
            let val eq = Logic.strip_imp_concl body
                val (f,args) = USyntax.strip_comb (get_lhs eq)
                val (vstrl,_) = USyntax.strip_abs f
                val names  =
                  Name.variant_list (Misc_Legacy.add_term_names(body, [])) (map (#1 o dest_Free) vstrl)
            in get (rst, n+1, (names,n)::L) end
            handle TERM _ => get (rst, n+1, L)
              | Utils.ERR _ => get (rst, n+1, L);

(* Note: Thm.rename_params_rule counts from 1, not 0 *)
fun rename thm =
  let val thy = Thm.theory_of_thm thm
      val tych = cterm_of thy
      val ants = Logic.strip_imp_prems (Thm.prop_of thm)
      val news = get (ants,1,[])
  in
  fold Thm.rename_params_rule news thm
  end;


(*---------------------------------------------------------------------------
 * Beta-conversion to the rhs of an equation (taken from hol90/drule.sml)
 *---------------------------------------------------------------------------*)

fun list_beta_conv tm =
  let fun rbeta th = Thm.transitive th (Thm.beta_conversion false (#2(Dcterm.dest_eq(cconcl th))))
      fun iter [] = Thm.reflexive tm
        | iter (v::rst) = rbeta (Thm.combination(iter rst) (Thm.reflexive v))
  in iter  end;


(*---------------------------------------------------------------------------
 * Trace information for the rewriter
 *---------------------------------------------------------------------------*)
val tracing = Unsynchronized.ref false;

fun say s = if !tracing then writeln s else ();

fun print_thms s L =
  say (cat_lines (s :: map Display.string_of_thm_without_context L));

fun print_cterm s ct =
  say (cat_lines [s, Syntax.string_of_term_global (Thm.theory_of_cterm ct) (Thm.term_of ct)]);


(*---------------------------------------------------------------------------
 * General abstraction handlers, should probably go in USyntax.
 *---------------------------------------------------------------------------*)
fun mk_aabs (vstr, body) =
  USyntax.mk_abs {Bvar = vstr, Body = body}
  handle Utils.ERR _ => USyntax.mk_pabs {varstruct = vstr, body = body};

fun list_mk_aabs (vstrl,tm) =
    fold_rev (fn vstr => fn tm => mk_aabs(vstr,tm)) vstrl tm;

fun dest_aabs used tm =
   let val ({Bvar,Body}, used') = USyntax.dest_abs used tm
   in (Bvar, Body, used') end
   handle Utils.ERR _ =>
     let val {varstruct, body, used} = USyntax.dest_pabs used tm
     in (varstruct, body, used) end;

fun strip_aabs used tm =
   let val (vstr, body, used') = dest_aabs used tm
       val (bvs, core, used'') = strip_aabs used' body
   in (vstr::bvs, core, used'') end
   handle Utils.ERR _ => ([], tm, used);

fun dest_combn tm 0 = (tm,[])
  | dest_combn tm n =
     let val {Rator,Rand} = USyntax.dest_comb tm
         val (f,rands) = dest_combn Rator (n-1)
     in (f,Rand::rands)
     end;




local fun dest_pair M = let val {fst,snd} = USyntax.dest_pair M in (fst,snd) end
      fun mk_fst tm =
          let val ty as Type(@{type_name Product_Type.prod}, [fty,sty]) = type_of tm
          in  Const ("Product_Type.fst", ty --> fty) $ tm  end
      fun mk_snd tm =
          let val ty as Type(@{type_name Product_Type.prod}, [fty,sty]) = type_of tm
          in  Const ("Product_Type.snd", ty --> sty) $ tm  end
in
fun XFILL tych x vstruct =
  let fun traverse p xocc L =
        if (is_Free p)
        then tych xocc::L
        else let val (p1,p2) = dest_pair p
             in traverse p1 (mk_fst xocc) (traverse p2  (mk_snd xocc) L)
             end
  in
  traverse vstruct x []
end end;

(*---------------------------------------------------------------------------
 * Replace a free tuple (vstr) by a universally quantified variable (a).
 * Note that the notion of "freeness" for a tuple is different than for a
 * variable: if variables in the tuple also occur in any other place than
 * an occurrences of the tuple, they aren't "free" (which is thus probably
 *  the wrong word to use).
 *---------------------------------------------------------------------------*)

fun VSTRUCT_ELIM tych a vstr th =
  let val L = USyntax.free_vars_lr vstr
      val bind1 = tych (HOLogic.mk_Trueprop (HOLogic.mk_eq(a,vstr)))
      val thm1 = Thm.implies_intr bind1 (SUBS [SYM(Thm.assume bind1)] th)
      val thm2 = forall_intr_list (map tych L) thm1
      val thm3 = forall_elim_list (XFILL tych a vstr) thm2
  in refl RS
     rewrite_rule [Thm.symmetric (@{thm surjective_pairing} RS eq_reflection)] thm3
  end;

fun PGEN tych a vstr th =
  let val a1 = tych a
      val vstr1 = tych vstr
  in
  Thm.forall_intr a1
     (if (is_Free vstr)
      then cterm_instantiate [(vstr1,a1)] th
      else VSTRUCT_ELIM tych a vstr th)
  end;


(*---------------------------------------------------------------------------
 * Takes apart a paired beta-redex, looking like "(\(x,y).N) vstr", into
 *
 *     (([x,y],N),vstr)
 *---------------------------------------------------------------------------*)
fun dest_pbeta_redex used M n =
  let val (f,args) = dest_combn M n
      val dummy = dest_aabs used f
  in (strip_aabs used f,args)
  end;

fun pbeta_redex M n = can (Utils.C (dest_pbeta_redex []) n) M;

fun dest_impl tm =
  let val ants = Logic.strip_imp_prems tm
      val eq = Logic.strip_imp_concl tm
  in (ants,get_lhs eq)
  end;

fun restricted t = is_some (USyntax.find_term
                            (fn (Const(@{const_name Wfrec.cut},_)) =>true | _ => false)
                            t)

fun CONTEXT_REWRITE_RULE (func, G, cut_lemma, congs) th =
 let val globals = func::G
     val ss0 = Simplifier.global_context (Thm.theory_of_thm th) empty_ss
     val pbeta_reduce = simpl_conv ss0 [@{thm split_conv} RS eq_reflection];
     val tc_list = Unsynchronized.ref []: term list Unsynchronized.ref
     val cut_lemma' = cut_lemma RS eq_reflection
     fun prover used ss thm =
     let fun cong_prover ss thm =
         let val dummy = say "cong_prover:"
             val cntxt = Simplifier.prems_of ss
             val dummy = print_thms "cntxt:" cntxt
             val dummy = say "cong rule:"
             val dummy = say (Display.string_of_thm_without_context thm)
             (* Unquantified eliminate *)
             fun uq_eliminate (thm,imp,thy) =
                 let val tych = cterm_of thy
                     val dummy = print_cterm "To eliminate:" (tych imp)
                     val ants = map tych (Logic.strip_imp_prems imp)
                     val eq = Logic.strip_imp_concl imp
                     val lhs = tych(get_lhs eq)
                     val ss' = Simplifier.add_prems (map ASSUME ants) ss
                     val lhs_eq_lhs1 = Raw_Simplifier.rewrite_cterm (false,true,false) (prover used) ss' lhs
                       handle Utils.ERR _ => Thm.reflexive lhs
                     val dummy = print_thms "proven:" [lhs_eq_lhs1]
                     val lhs_eq_lhs2 = implies_intr_list ants lhs_eq_lhs1
                     val lhs_eeq_lhs2 = lhs_eq_lhs2 RS meta_eq_to_obj_eq
                  in
                  lhs_eeq_lhs2 COMP thm
                  end
             fun pq_eliminate (thm,thy,vlist,imp_body,lhs_eq) =
              let val ((vstrl, _, used'), args) = dest_pbeta_redex used lhs_eq (length vlist)
                  val dummy = forall (op aconv) (ListPair.zip (vlist, args))
                    orelse error "assertion failed in CONTEXT_REWRITE_RULE"
                  val imp_body1 = subst_free (ListPair.zip (args, vstrl))
                                             imp_body
                  val tych = cterm_of thy
                  val ants1 = map tych (Logic.strip_imp_prems imp_body1)
                  val eq1 = Logic.strip_imp_concl imp_body1
                  val Q = get_lhs eq1
                  val QeqQ1 = pbeta_reduce (tych Q)
                  val Q1 = #2(Dcterm.dest_eq(cconcl QeqQ1))
                  val ss' = Simplifier.add_prems (map ASSUME ants1) ss
                  val Q1eeqQ2 = Raw_Simplifier.rewrite_cterm (false,true,false) (prover used') ss' Q1
                                handle Utils.ERR _ => Thm.reflexive Q1
                  val Q2 = #2 (Logic.dest_equals (Thm.prop_of Q1eeqQ2))
                  val Q3 = tych(list_comb(list_mk_aabs(vstrl,Q2),vstrl))
                  val Q2eeqQ3 = Thm.symmetric(pbeta_reduce Q3 RS eq_reflection)
                  val thA = Thm.transitive(QeqQ1 RS eq_reflection) Q1eeqQ2
                  val QeeqQ3 = Thm.transitive thA Q2eeqQ3 handle THM _ =>
                               ((Q2eeqQ3 RS meta_eq_to_obj_eq)
                                RS ((thA RS meta_eq_to_obj_eq) RS trans))
                                RS eq_reflection
                  val impth = implies_intr_list ants1 QeeqQ3
                  val impth1 = impth RS meta_eq_to_obj_eq
                  (* Need to abstract *)
                  val ant_th = Utils.itlist2 (PGEN tych) args vstrl impth1
              in ant_th COMP thm
              end
             fun q_eliminate (thm,imp,thy) =
              let val (vlist, imp_body, used') = strip_all used imp
                  val (ants,Q) = dest_impl imp_body
              in if (pbeta_redex Q) (length vlist)
                 then pq_eliminate (thm,thy,vlist,imp_body,Q)
                 else
                 let val tych = cterm_of thy
                     val ants1 = map tych ants
                     val ss' = Simplifier.add_prems (map ASSUME ants1) ss
                     val Q_eeq_Q1 = Raw_Simplifier.rewrite_cterm
                        (false,true,false) (prover used') ss' (tych Q)
                      handle Utils.ERR _ => Thm.reflexive (tych Q)
                     val lhs_eeq_lhs2 = implies_intr_list ants1 Q_eeq_Q1
                     val lhs_eq_lhs2 = lhs_eeq_lhs2 RS meta_eq_to_obj_eq
                     val ant_th = forall_intr_list(map tych vlist)lhs_eq_lhs2
                 in
                 ant_th COMP thm
              end end

             fun eliminate thm =
               case Thm.prop_of thm
               of Const("==>",_) $ imp $ _ =>
                   eliminate
                    (if not(is_all imp)
                     then uq_eliminate (thm, imp, Thm.theory_of_thm thm)
                     else q_eliminate (thm, imp, Thm.theory_of_thm thm))
                            (* Assume that the leading constant is ==,   *)
                | _ => thm  (* if it is not a ==>                        *)
         in SOME(eliminate (rename thm)) end
         handle Utils.ERR _ => NONE    (* FIXME handle THM as well?? *)

        fun restrict_prover ss thm =
          let val dummy = say "restrict_prover:"
              val cntxt = rev (Simplifier.prems_of ss)
              val dummy = print_thms "cntxt:" cntxt
              val thy = Thm.theory_of_thm thm
              val Const("==>",_) $ (Const(@{const_name Trueprop},_) $ A) $ _ = Thm.prop_of thm
              fun genl tm = let val vlist = subtract (op aconv) globals
                                           (Misc_Legacy.add_term_frees(tm,[]))
                            in fold_rev Forall vlist tm
                            end
              (*--------------------------------------------------------------
               * This actually isn't quite right, since it will think that
               * not-fully applied occs. of "f" in the context mean that the
               * current call is nested. The real solution is to pass in a
               * term "f v1..vn" which is a pattern that any full application
               * of "f" will match.
               *-------------------------------------------------------------*)
              val func_name = #1(dest_Const func)
              fun is_func (Const (name,_)) = (name = func_name)
                | is_func _                = false
              val rcontext = rev cntxt
              val cncl = HOLogic.dest_Trueprop o Thm.prop_of
              val antl = case rcontext of [] => []
                         | _   => [USyntax.list_mk_conj(map cncl rcontext)]
              val TC = genl(USyntax.list_mk_imp(antl, A))
              val dummy = print_cterm "func:" (cterm_of thy func)
              val dummy = print_cterm "TC:" (cterm_of thy (HOLogic.mk_Trueprop TC))
              val dummy = tc_list := (TC :: !tc_list)
              val nestedp = is_some (USyntax.find_term is_func TC)
              val dummy = if nestedp then say "nested" else say "not_nested"
              val th' = if nestedp then raise RULES_ERR "solver" "nested function"
                        else let val cTC = cterm_of thy
                                              (HOLogic.mk_Trueprop TC)
                             in case rcontext of
                                [] => SPEC_ALL(ASSUME cTC)
                               | _ => MP (SPEC_ALL (ASSUME cTC))
                                         (LIST_CONJ rcontext)
                             end
              val th'' = th' RS thm
          in SOME (th'')
          end handle Utils.ERR _ => NONE    (* FIXME handle THM as well?? *)
    in
    (if (is_cong thm) then cong_prover else restrict_prover) ss thm
    end
    val ctm = cprop_of th
    val names = Misc_Legacy.add_term_names (term_of ctm, [])
    val th1 =
      Raw_Simplifier.rewrite_cterm (false, true, false)
        (prover names) (ss0 addsimps [cut_lemma'] |> fold Simplifier.add_eqcong congs) ctm
    val th2 = Thm.equal_elim th1 th
 in
 (th2, filter_out restricted (!tc_list))
 end;


fun prove strict (ptm, tac) =
  let
    val thy = Thm.theory_of_cterm ptm;
    val t = Thm.term_of ptm;
    val ctxt = Proof_Context.init_global thy |> Variable.auto_fixes t;
  in
    if strict then Goal.prove ctxt [] [] t (K tac)
    else Goal.prove ctxt [] [] t (K tac)
      handle ERROR msg => (warning msg; raise RULES_ERR "prove" msg)
  end;

end;
