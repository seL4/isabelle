(*  Title:      HOL/Tools/reification.ML
    Author:     Amine Chaieb, TU Muenchen

A trial for automatical reification.
*)

signature REIFICATION =
sig
  val conv: Proof.context -> thm list -> conv
  val tac: Proof.context -> thm list -> term option -> int -> tactic
  val lift_conv: Proof.context -> conv -> term option -> int -> tactic
  val dereify: Proof.context -> thm list -> conv
end;

structure Reification : REIFICATION =
struct

fun dest_listT (Type (\<^type_name>\<open>list\<close>, [T])) = T;

val FWD = curry (op OF);

fun rewrite_with ctxt eqs = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt addsimps eqs);

val pure_subst = @{lemma "x == y ==> PROP P y ==> PROP P x" by simp}

fun lift_conv ctxt conv some_t = Subgoal.FOCUS (fn {context = ctxt', concl, ...} =>
  let
    val ct =
      (case some_t of
        NONE => Thm.dest_arg concl
      | SOME t => Thm.cterm_of ctxt' t)
    val thm = conv ct;
  in
    if Thm.is_reflexive thm then no_tac
    else ALLGOALS (resolve_tac ctxt [pure_subst OF [thm]])
  end) ctxt;

(* Make a congruence rule out of a defining equation for the interpretation

   th is one defining equation of f,
     i.e. th is "f (Cp ?t1 ... ?tn) = P(f ?t1, .., f ?tn)" 
   Cp is a constructor pattern and P is a pattern 

   The result is:
     [|?A1 = f ?t1 ; .. ; ?An= f ?tn |] ==> P (?A1, .., ?An) = f (Cp ?t1 .. ?tn)
       + the a list of names of the A1 .. An, Those are fresh in the ctxt *)

fun mk_congeq ctxt fs th =
  let
    val Const (fN, _) = th |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
      |> fst |> strip_comb |> fst;
    val ((_, [th']), ctxt') = Variable.import true [th] ctxt;
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th'));
    fun add_fterms (t as t1 $ t2) =
          if exists (fn f => Term.could_unify (t |> strip_comb |> fst, f)) fs
          then insert (op aconv) t
          else add_fterms t1 #> add_fterms t2
      | add_fterms (t as Abs _) =
          if exists_Const (fn (c, _) => c = fN) t
          then K [t]
          else K []
      | add_fterms _ = I;
    val fterms = add_fterms rhs [];
    val (xs, ctxt'') = Variable.variant_fixes (replicate (length fterms) "x") ctxt';
    val tys = map fastype_of fterms;
    val vs = map Free (xs ~~ tys);
    val env = fterms ~~ vs; (*FIXME*)
    fun replace_fterms (t as t1 $ t2) =
        (case AList.lookup (op aconv) env t of
            SOME v => v
          | NONE => replace_fterms t1 $ replace_fterms t2)
      | replace_fterms t =
        (case AList.lookup (op aconv) env t of
            SOME v => v
          | NONE => t);
    fun mk_def (Abs (x, xT, t), v) =
          HOLogic.mk_Trueprop (HOLogic.all_const xT $ Abs (x, xT, HOLogic.mk_eq (v $ Bound 0, t)))
      | mk_def (t, v) = HOLogic.mk_Trueprop (HOLogic.mk_eq (v, t));
    fun tryext x =
      (x RS @{lemma "(\<forall>x. f x = g x) \<Longrightarrow> f = g" by blast} handle THM _ => x);
    val cong =
      (Goal.prove ctxt'' [] (map mk_def env)
        (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, replace_fterms rhs)))
        (fn {context, prems, ...} =>
          Local_Defs.unfold0_tac context (map tryext prems) THEN resolve_tac ctxt'' [th'] 1)) RS sym;
    val (cong' :: vars') =
      Variable.export ctxt'' ctxt (cong :: map (Drule.mk_term o Thm.cterm_of ctxt'') vs);
    val vs' = map (fst o fst o Term.dest_Var o Thm.term_of o Drule.dest_term) vars';

  in (vs', cong') end;

(* congs is a list of pairs (P,th) where th is a theorem for
     [| f p1 = A1; ...; f pn = An|] ==> f (C p1 .. pn) = P *)

fun rearrange congs =
  let
    fun P (_, th) =
      let val \<^term>\<open>Trueprop\<close> $ (Const (\<^const_name>\<open>HOL.eq\<close>, _) $ l $ _) = Thm.concl_of th
      in can dest_Var l end;
    val (yes, no) = List.partition P congs;
  in no @ yes end;

fun dereify ctxt eqs =
  rewrite_with ctxt (eqs @ @{thms nth_Cons_0 nth_Cons_Suc});

fun index_of t bds =
  let
    val tt = HOLogic.listT (fastype_of t);
  in
    (case AList.lookup Type.could_unify bds tt of
        NONE => error "index_of: type not found in environements!"
      | SOME (tbs, tats) =>
          let
            val i = find_index (fn t' => t' = t) tats;
            val j = find_index (fn t' => t' = t) tbs;
          in
            if j = ~1 then
              if i = ~1
              then (length tbs + length tats, AList.update Type.could_unify (tt, (tbs, tats @ [t])) bds)
              else (i, bds)
            else (j, bds)
          end)
  end;

(* Generic decomp for reification : matches the actual term with the
   rhs of one cong rule. The result of the matching guides the
   proof synthesis: The matches of the introduced Variables A1 .. An are
   processed recursively
   The rest is instantiated in the cong rule,i.e. no reification is needed *)

(* da is the decomposition for atoms, ie. it returns ([],g) where g
   returns the right instance f (AtC n) = t , where AtC is the Atoms
   constructor and n is the number of the atom corresponding to t *)
fun decomp_reify da cgns (ct, ctxt) bds =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun tryabsdecomp (ct, ctxt) bds =
      (case Thm.term_of ct of
        Abs (_, xT, ta) =>
          let
            val ([raw_xn], ctxt') = Variable.variant_fixes ["x"] ctxt;
            val (xn, ta) = Syntax_Trans.variant_abs (raw_xn, xT, ta);  (* FIXME !? *)
            val x = Free (xn, xT);
            val cx = Thm.cterm_of ctxt' x;
            val cta = Thm.cterm_of ctxt' ta;
            val bds = (case AList.lookup Type.could_unify bds (HOLogic.listT xT) of
                NONE => error "tryabsdecomp: Type not found in the Environement"
              | SOME (bsT, atsT) => AList.update Type.could_unify (HOLogic.listT xT,
                  (x :: bsT, atsT)) bds);
           in (([(cta, ctxt')],
                fn ([th], bds) =>
                  (hd (Variable.export ctxt' ctxt [(Thm.forall_intr cx th) COMP allI]),
                   let
                     val (bsT, asT) = the (AList.lookup Type.could_unify bds (HOLogic.listT xT));
                   in
                     AList.update Type.could_unify (HOLogic.listT xT, (tl bsT, asT)) bds
                   end)),
               bds)
           end
       | _ => da (ct, ctxt) bds)
  in
    (case cgns of
      [] => tryabsdecomp (ct, ctxt) bds
    | ((vns, cong) :: congs) =>
        (let
          val (tyenv, tmenv) =
            Pattern.match thy
              ((fst o HOLogic.dest_eq o HOLogic.dest_Trueprop) (Thm.concl_of cong), Thm.term_of ct)
              (Vartab.empty, Vartab.empty);
          val (fnvs, invs) = List.partition (fn ((vn, _),_) => member (op =) vns vn) (Vartab.dest tmenv);
          val (fts, its) =
            (map (snd o snd) fnvs,
             map (fn ((vn, vi), (tT, t)) => (((vn, vi), tT), Thm.cterm_of ctxt t)) invs);
          val ctyenv =
            map (fn ((vn, vi), (s, ty)) => (((vn, vi), s), Thm.ctyp_of ctxt ty))
              (Vartab.dest tyenv);
        in
          ((map (Thm.cterm_of ctxt) fts ~~ replicate (length fts) ctxt,
             apfst (FWD (Drule.instantiate_normalize (TVars.make ctyenv, Vars.make its) cong))), bds)
        end handle Pattern.MATCH => decomp_reify da congs (ct, ctxt) bds))
  end;

fun get_nths (t as (Const (\<^const_name>\<open>List.nth\<close>, _) $ vs $ n)) =
      AList.update (op aconv) (t, (vs, n))
  | get_nths (t1 $ t2) = get_nths t1 #> get_nths t2
  | get_nths (Abs (_, _, t')) = get_nths t'
  | get_nths _ = I;

fun tryeqs [] (ct, ctxt) bds = error "Cannot find the atoms equation"
  | tryeqs (eq :: eqs) (ct, ctxt) bds = ((
      let
        val rhs = eq |> Thm.prop_of |> HOLogic.dest_Trueprop  |> HOLogic.dest_eq |> snd;
        val nths = get_nths rhs [];
        val (vss, _) = fold_rev (fn (_, (vs, n)) => fn (vss, ns) =>
          (insert (op aconv) vs vss, insert (op aconv) n ns)) nths ([], []);
        val (vsns, ctxt') = Variable.variant_fixes (replicate (length vss) "vs") ctxt;
        val (xns, ctxt'') = Variable.variant_fixes (replicate (length nths) "x") ctxt';
        val thy = Proof_Context.theory_of ctxt'';
        val vsns_map = vss ~~ vsns;
        val xns_map = fst (split_list nths) ~~ xns;
        val subst = map (fn (nt, xn) => (nt, Var ((xn, 0), fastype_of nt))) xns_map;
        val rhs_P = subst_free subst rhs;
        val (tyenv, tmenv) = Pattern.match thy (rhs_P, Thm.term_of ct) (Vartab.empty, Vartab.empty);
        val sbst = Envir.subst_term (tyenv, tmenv);
        val sbsT = Envir.subst_type tyenv;
        val subst_ty =
          map (fn (n, (s, t)) => ((n, s), Thm.ctyp_of ctxt'' t)) (Vartab.dest tyenv)
        val tml = Vartab.dest tmenv;
        val (subst_ns, bds) = fold_map
          (fn (Const _ $ _ $ n, Var (xn0, _)) => fn bds =>
            let
              val name = snd (the (AList.lookup (op =) tml xn0));
              val (idx, bds) = index_of name bds;
            in (apply2 (Thm.cterm_of ctxt'') (n, idx |> HOLogic.mk_nat), bds) end) subst bds;
        val subst_vs =
          let
            fun h (Const _ $ (vs as Var (_, lT)) $ _, Var (_, T)) =
              let
                val cns = sbst (Const (\<^const_name>\<open>List.Cons\<close>, T --> lT --> lT));
                val lT' = sbsT lT;
                val (bsT, _) = the (AList.lookup Type.could_unify bds lT);
                val vsn = the (AList.lookup (op =) vsns_map vs);
                val vs' = fold_rev (fn x => fn xs => cns $ x $xs) bsT (Free (vsn, lT'));
              in apply2 (Thm.cterm_of ctxt'') (vs, vs') end;
          in map h subst end;
        val cts =
          map (fn ((vn, vi), (tT, t)) => apply2 (Thm.cterm_of ctxt'') (Var ((vn, vi), tT), t))
            (fold (AList.delete (fn (((a : string), _), (b, _)) => a = b))
              (map (fn n => (n, 0)) xns) tml);
        val substt =
          let
            val ih = Drule.cterm_rule (Thm.instantiate (TVars.make subst_ty, Vars.empty));
          in map (apply2 ih) (subst_ns @ subst_vs @ cts) end;
        val th =
          (Drule.instantiate_normalize
            (TVars.make subst_ty, Vars.make (map (apfst (dest_Var o Thm.term_of)) substt)) eq)
            RS sym;
      in (hd (Variable.export ctxt'' ctxt [th]), bds) end)
      handle Pattern.MATCH => tryeqs eqs (ct, ctxt) bds);

(* looks for the atoms equation and instantiates it with the right number *)

fun mk_decompatom eqs (ct, ctxt) bds = (([], fn (_, bds) =>
  let
    val tT = fastype_of (Thm.term_of ct);
    fun isat eq =
      let
        val rhs = eq |> Thm.prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd;
      in exists_Const
        (fn (n, ty) => n = \<^const_name>\<open>List.nth\<close>
          andalso AList.defined Type.could_unify bds (domain_type ty)) rhs
          andalso Type.could_unify (fastype_of rhs, tT)
      end;
  in tryeqs (filter isat eqs) (ct, ctxt) bds end), bds);

(* Generic reification procedure: *)
(* creates all needed cong rules and then just uses the theorem synthesis *)

fun mk_congs ctxt eqs =
  let
    val fs = fold_rev (fn eq => insert (op =) (eq |> Thm.prop_of |> HOLogic.dest_Trueprop
      |> HOLogic.dest_eq |> fst |> strip_comb
      |> fst)) eqs [];
    val tys = fold_rev (fn f => fold (insert (op =)) (f |> fastype_of |> binder_types |> tl)) fs [];
    val (vs, ctxt') = Variable.variant_fixes (replicate (length tys) "vs") ctxt;
    val subst =
      the o AList.lookup (op =)
        (map2 (fn T => fn v => (T, Thm.cterm_of ctxt' (Free (v, T)))) tys vs);
    fun prep_eq eq =
      let
        val (_, _ :: vs) = eq |> Thm.prop_of |> HOLogic.dest_Trueprop
          |> HOLogic.dest_eq |> fst |> strip_comb;
        val subst = map_filter (fn Var v => SOME (v, subst (#2 v)) | _ => NONE) vs;
      in Thm.instantiate (TVars.empty, Vars.make subst) eq end;
    val (ps, congs) = map_split (mk_congeq ctxt' fs o prep_eq) eqs;
    val bds = AList.make (K ([], [])) tys;
  in (ps ~~ Variable.export ctxt' ctxt congs, bds) end

fun conv ctxt eqs ct =
  let
    val (congs, bds) = mk_congs ctxt eqs;
    val congs = rearrange congs;
    val (th, bds') =
      apfst mk_eq (divide_and_conquer' (decomp_reify (mk_decompatom eqs) congs) (ct, ctxt) bds);
    fun is_list_var (Var (_, t)) = can dest_listT t
      | is_list_var _ = false;
    val vars = th |> Thm.prop_of |> Logic.dest_equals |> snd
      |> strip_comb |> snd |> filter is_list_var;
    val vs = map (fn Var (v as (_, T)) =>
      (v, the (AList.lookup Type.could_unify bds' T) |> snd |> HOLogic.mk_list (dest_listT T))) vars;
    val th' =
      Drule.instantiate_normalize (TVars.empty, Vars.make (map (apsnd (Thm.cterm_of ctxt)) vs)) th;
    val th'' = Thm.symmetric (dereify ctxt [] (Thm.lhs_of th'));
  in Thm.transitive th'' th' end;

fun tac ctxt eqs =
  lift_conv ctxt (conv ctxt eqs);

end;
