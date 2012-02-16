(*  Title:      HOL/Library/reflection.ML
    Author:     Amine Chaieb, TU Muenchen

A trial for automatical reification.
*)

signature REFLECTION =
sig
  val genreify_tac: Proof.context -> thm list -> term option -> int -> tactic
  val reflection_tac: Proof.context -> thm list -> thm list -> term option -> int -> tactic
  val gen_reflection_tac: Proof.context -> (cterm -> thm)
    -> thm list -> thm list -> term option -> int -> tactic
  val genreif : Proof.context -> thm list -> term -> thm
end;

structure Reflection : REFLECTION =
struct

  (* Make a congruence rule out of a defining equation for the interpretation *)
  (* th is one defining equation of f, i.e.
     th is "f (Cp ?t1 ... ?tn) = P(f ?t1, .., f ?tn)" *)
  (* Cp is a constructor pattern and P is a pattern *)

  (* The result is:
      [|?A1 = f ?t1 ; .. ; ?An= f ?tn |] ==> P (?A1, .., ?An) = f (Cp ?t1 .. ?tn) *)
  (*  + the a list of names of the A1 .. An, Those are fresh in the ctxt*)

fun mk_congeq ctxt fs th =
  let
   val (f as Const(fN,fT)) = th |> prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq
     |> fst |> strip_comb |> fst
   val thy = Proof_Context.theory_of ctxt
   val cert = Thm.cterm_of thy
   val (((_,_),[th']), ctxt') = Variable.import true [th] ctxt
   val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop (Thm.prop_of th'))
   fun add_fterms (t as t1 $ t2) =
       if exists (fn f => Term.could_unify (t |> strip_comb |> fst, f)) fs then insert (op aconv) t
       else add_fterms t1 #> add_fterms t2
     | add_fterms (t as Abs(xn,xT,t')) =
       if exists_Const (fn (c, _) => c = fN) t then (fn _ => [t]) else (fn _ => [])
     | add_fterms _ = I
   val fterms = add_fterms rhs []
   val (xs, ctxt'') = Variable.variant_fixes (replicate (length fterms) "x") ctxt'
   val tys = map fastype_of fterms
   val vs = map Free (xs ~~ tys)
   val env = fterms ~~ vs
                    (* FIXME!!!!*)
   fun replace_fterms (t as t1 $ t2) =
       (case AList.lookup (op aconv) env t of
            SOME v => v
          | NONE => replace_fterms t1 $ replace_fterms t2)
     | replace_fterms t = (case AList.lookup (op aconv) env t of
                               SOME v => v
                             | NONE => t)

   fun mk_def (Abs(x,xT,t),v) = HOLogic.mk_Trueprop ((HOLogic.all_const xT)$ Abs(x,xT,HOLogic.mk_eq(v$(Bound 0), t)))
     | mk_def (t, v) = HOLogic.mk_Trueprop (HOLogic.mk_eq (v, t))
   fun tryext x = (x RS @{lemma "(\<forall>x. f x = g x) \<Longrightarrow> f = g" by blast} handle THM _ =>  x)
   val cong =
    (Goal.prove ctxt'' [] (map mk_def env)
      (HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs, replace_fterms rhs)))
      (fn {context, prems, ...} =>
        Local_Defs.unfold_tac context (map tryext prems) THEN rtac th' 1)) RS sym

   val (cong' :: vars') =
       Variable.export ctxt'' ctxt (cong :: map (Drule.mk_term o cert) vs)
   val vs' = map (fst o fst o Term.dest_Var o Thm.term_of o Drule.dest_term) vars'

  in  (vs', cong') end;
 (* congs is a list of pairs (P,th) where th is a theorem for *)
        (* [| f p1 = A1; ...; f pn = An|] ==> f (C p1 .. pn) = P *)
val FWD = curry (op OF);


exception REIF of string;

fun dest_listT (Type (@{type_name "list"}, [T])) = T;

fun rearrange congs =
  let
    fun P (_, th) =
      let val @{term "Trueprop"}$(Const (@{const_name HOL.eq},_) $l$_) = concl_of th
      in can dest_Var l end
    val (yes,no) = List.partition P congs
  in no @ yes end

fun genreif ctxt raw_eqs t =
  let
    fun index_of t bds =
      let
        val tt = HOLogic.listT (fastype_of t)
      in
       (case AList.lookup Type.could_unify bds tt of
          NONE => error "index_of : type not found in environements!"
        | SOME (tbs,tats) =>
          let
            val i = find_index (fn t' => t' = t) tats
            val j = find_index (fn t' => t' = t) tbs
          in (if j = ~1 then
              if i = ~1
              then (length tbs + length tats,
                    AList.update Type.could_unify (tt,(tbs,tats@[t])) bds)
              else (i, bds) else (j, bds))
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
    fun decomp_genreif da cgns (t,ctxt) bds =
      let
        val thy = Proof_Context.theory_of ctxt
        val cert = cterm_of thy
        fun tryabsdecomp (s,ctxt) bds =
          (case s of
             Abs(xn,xT,ta) => (
               let
                 val ([xn],ctxt') = Variable.variant_fixes ["x"] ctxt
                 val (xn,ta) = Syntax_Trans.variant_abs (xn,xT,ta)  (* FIXME !? *)
                 val x = Free(xn,xT)
                 val bds = (case AList.lookup Type.could_unify bds (HOLogic.listT xT)
                          of NONE => error "tryabsdecomp: Type not found in the Environement"
                           | SOME (bsT,atsT) =>
                             (AList.update Type.could_unify (HOLogic.listT xT, ((x::bsT), atsT)) bds))
               in (([(ta, ctxt')],
                    fn ([th], bds) =>
                      (hd (Variable.export ctxt' ctxt [(Thm.forall_intr (cert x) th) COMP allI]),
                       let val (bsT,asT) = the(AList.lookup Type.could_unify bds (HOLogic.listT xT))
                       in AList.update Type.could_unify (HOLogic.listT xT,(tl bsT,asT)) bds
                       end)),
                   bds)
               end)
           | _ => da (s,ctxt) bds)
      in
        (case cgns of
          [] => tryabsdecomp (t,ctxt) bds
        | ((vns,cong)::congs) =>
            (let
              val cert = cterm_of thy
              val certy = ctyp_of thy
              val (tyenv, tmenv) =
                Pattern.match thy
                  ((fst o HOLogic.dest_eq o HOLogic.dest_Trueprop) (concl_of cong), t)
                  (Vartab.empty, Vartab.empty)
              val (fnvs,invs) = List.partition (fn ((vn,_),_) => member (op =) vns vn) (Vartab.dest tmenv)
              val (fts,its) =
                (map (snd o snd) fnvs,
                 map (fn ((vn,vi),(tT,t)) => (cert(Var ((vn,vi),tT)), cert t)) invs)
              val ctyenv = map (fn ((vn,vi),(s,ty)) => (certy (TVar((vn,vi),s)), certy ty)) (Vartab.dest tyenv)
            in ((fts ~~ (replicate (length fts) ctxt),
                 Library.apfst (FWD (Drule.instantiate_normalize (ctyenv, its) cong))), bds)
            end handle Pattern.MATCH => decomp_genreif da congs (t,ctxt) bds))
      end;

 (* looks for the atoms equation and instantiates it with the right number *)
    fun mk_decompatom eqs (t,ctxt) bds = (([], fn (_, bds) =>
      let
        val tT = fastype_of t
        fun isat eq =
          let
            val rhs = eq |> prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
          in exists_Const
            (fn (n,ty) => n = @{const_name "List.nth"}
                          andalso
                          AList.defined Type.could_unify bds (domain_type ty)) rhs
            andalso Type.could_unify (fastype_of rhs, tT)
          end

        fun get_nths t acc =
          case t of
            Const(@{const_name "List.nth"},_)$vs$n => insert (fn ((a,_),(b,_)) => a aconv b) (t,(vs,n)) acc
          | t1$t2 => get_nths t1 (get_nths t2 acc)
          | Abs(_,_,t') => get_nths t'  acc
          | _ => acc

        fun
           tryeqs [] bds = error "Can not find the atoms equation"
         | tryeqs (eq::eqs) bds = ((
          let
            val rhs = eq |> prop_of |> HOLogic.dest_Trueprop  |> HOLogic.dest_eq |> snd
            val nths = get_nths rhs []
            val (vss,ns) = fold_rev (fn (_,(vs,n)) => fn (vss,ns) =>
                                      (insert (op aconv) vs vss, insert (op aconv) n ns)) nths ([],[])
            val (vsns, ctxt') = Variable.variant_fixes (replicate (length vss) "vs") ctxt
            val (xns, ctxt'') = Variable.variant_fixes (replicate (length nths) "x") ctxt'
            val thy = Proof_Context.theory_of ctxt''
            val cert = cterm_of thy
            val certT = ctyp_of thy
            val vsns_map = vss ~~ vsns
            val xns_map = (fst (split_list nths)) ~~ xns
            val subst = map (fn (nt, xn) => (nt, Var ((xn,0), fastype_of nt))) xns_map
            val rhs_P = subst_free subst rhs
            val (tyenv, tmenv) = Pattern.match thy (rhs_P, t) (Vartab.empty, Vartab.empty)
            val sbst = Envir.subst_term (tyenv, tmenv)
            val sbsT = Envir.subst_type tyenv
            val subst_ty = map (fn (n,(s,t)) => (certT (TVar (n, s)), certT t))
                               (Vartab.dest tyenv)
            val tml = Vartab.dest tmenv
            val t's = map (fn xn => snd (the (AList.lookup (op =) tml (xn,0)))) xns (* FIXME : Express with sbst*)
            val (subst_ns, bds) = fold_map
                (fn (Const _ $ vs $ n, Var (xn0,T)) => fn bds =>
                  let
                    val name = snd (the (AList.lookup (op =) tml xn0))
                    val (idx, bds) = index_of name bds
                  in ((cert n, idx |> (HOLogic.mk_nat #> cert)), bds) end) subst bds
            val subst_vs =
              let
                fun ty (Const _ $ (vs as Var (vsn,lT)) $ n, Var (xn0,T)) = (certT T, certT (sbsT T))
                fun h (Const _ $ (vs as Var (vsn,lT)) $ n, Var (xn0,T)) =
                  let
                    val cns = sbst (Const(@{const_name "List.Cons"}, T --> lT --> lT))
                    val lT' = sbsT lT
                    val (bsT,asT) = the (AList.lookup Type.could_unify bds lT)
                    val vsn = the (AList.lookup (op =) vsns_map vs)
                    val cvs = cert (fold_rev (fn x => fn xs => cns$x$xs) bsT (Free (vsn, lT')))
                  in (cert vs, cvs) end
              in map h subst end
            val cts = map (fn ((vn,vi),(tT,t)) => (cert(Var ((vn,vi),tT)), cert t))
                          (fold (AList.delete (fn (((a: string),_),(b,_)) => a = b))
                                (map (fn n => (n,0)) xns) tml)
            val substt =
              let val ih = Drule.cterm_rule (Thm.instantiate (subst_ty,[]))
              in map (fn (v,t) => (ih v, ih t)) (subst_ns@subst_vs@cts)  end
            val th = (Drule.instantiate_normalize (subst_ty, substt)  eq) RS sym
          in (hd (Variable.export ctxt'' ctxt [th]), bds) end)
          handle Pattern.MATCH => tryeqs eqs bds)
      in tryeqs (filter isat eqs) bds end), bds);

  (* Generic reification procedure: *)
  (* creates all needed cong rules and then just uses the theorem synthesis *)

    fun mk_congs ctxt raw_eqs =
      let
        val fs = fold_rev (fn eq =>
                           insert (op =) (eq |> prop_of |> HOLogic.dest_Trueprop
                           |> HOLogic.dest_eq |> fst |> strip_comb
                           |> fst)) raw_eqs []
        val tys = fold_rev (fn f => fold (insert (op =)) (f |> fastype_of |> binder_types |> tl)
                            ) fs []
        val (vs, ctxt') = Variable.variant_fixes (replicate (length tys) "vs") ctxt
        val thy = Proof_Context.theory_of ctxt'
        val cert = cterm_of thy
        val vstys = map (fn (t,v) => (t,SOME (cert (Free(v,t)))))
                    (tys ~~ vs)
        val is_Var = can dest_Var
        fun insteq eq vs =
          let
            val subst = map (fn (v as Var(n,t)) => (cert v, (the o the) (AList.lookup (op =) vstys t)))
                        (filter is_Var vs)
          in Thm.instantiate ([],subst) eq
          end

        val bds = AList.make (fn _ => ([],[])) tys
        val eqs = map (fn eq => eq |> prop_of |> HOLogic.dest_Trueprop
                                   |> HOLogic.dest_eq |> fst |> strip_comb |> snd |> tl
                                   |> (insteq eq)) raw_eqs
        val (ps,congs) = split_list (map (mk_congeq ctxt' fs) eqs)
      in (ps ~~ (Variable.export ctxt' ctxt congs), bds)
      end

    val (congs, bds) = mk_congs ctxt raw_eqs
    val congs = rearrange congs
    val (th, bds) = divide_and_conquer' (decomp_genreif (mk_decompatom raw_eqs) congs) (t,ctxt) bds
    fun is_listVar (Var (_,t)) = can dest_listT t
         | is_listVar _ = false
    val vars = th |> prop_of |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> snd
                  |> strip_comb |> snd |> filter is_listVar
    val cert = cterm_of (Proof_Context.theory_of ctxt)
    val cvs = map (fn (v as Var(n,t)) => (cert v,
                  the (AList.lookup Type.could_unify bds t) |> snd |> HOLogic.mk_list (dest_listT t) |> cert)) vars
    val th' = Drule.instantiate_normalize ([], cvs) th
    val t' = (fst o HOLogic.dest_eq o HOLogic.dest_Trueprop o prop_of) th'
    val th'' = Goal.prove ctxt [] [] (HOLogic.mk_Trueprop (HOLogic.mk_eq (t, t')))
               (fn _ => simp_tac (simpset_of ctxt) 1)
  in FWD trans [th'',th']
  end


fun genreflect ctxt conv corr_thms raw_eqs t =
  let
    val reifth = genreif ctxt raw_eqs t
    fun trytrans [] = error "No suitable correctness theorem found"
      | trytrans (th::ths) =
           (FWD trans [reifth, th RS sym] handle THM _ => trytrans ths)
    val th = trytrans corr_thms
    val ft = (Thm.dest_arg1 o Thm.dest_arg o Thm.dest_arg o cprop_of) th
    val rth = conv ft
  in
    simplify (HOL_basic_ss addsimps raw_eqs addsimps @{thms nth_Cons_0 nth_Cons_Suc})
             (simplify (HOL_basic_ss addsimps [rth]) th)
  end

fun genreify_tac ctxt eqs to = SUBGOAL (fn (goal, i) =>
  let
    val t = (case to of NONE => HOLogic.dest_Trueprop goal | SOME x => x)
    val th = genreif ctxt eqs t RS ssubst
  in rtac th i end);

    (* Reflection calls reification and uses the correctness *)
        (* theorem assumed to be the head of the list *)
fun gen_reflection_tac ctxt conv corr_thms raw_eqs to = SUBGOAL (fn (goal, i) =>
  let
    val t = (case to of NONE => HOLogic.dest_Trueprop goal | SOME x => x)
    val th = genreflect ctxt conv corr_thms raw_eqs t RS ssubst
  in rtac th i THEN TRY (rtac TrueI i) end);  (* FIXME THEN_ALL_NEW !? *)

fun reflection_tac ctxt = gen_reflection_tac ctxt
  (Code_Evaluation.dynamic_conv (Proof_Context.theory_of ctxt));
  (*FIXME why Code_Evaluation.dynamic_conv?  very specific...*)

end
