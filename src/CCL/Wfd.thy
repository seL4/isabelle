(*  Title:      CCL/Wfd.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

header {* Well-founded relations in CCL *}

theory Wfd
imports Trancl Type Hered
begin

consts
      (*** Predicates ***)
  Wfd        ::       "[i set] => o"
      (*** Relations ***)
  wf         ::       "[i set] => i set"
  wmap       ::       "[i=>i,i set] => i set"
  lex        ::       "[i set,i set] => i set"      (infixl "**" 70)
  NatPR      ::       "i set"
  ListPR     ::       "i set => i set"

defs

  Wfd_def:
  "Wfd(R) == ALL P.(ALL x.(ALL y.<y,x> : R --> y:P) --> x:P) --> (ALL a. a:P)"

  wf_def:         "wf(R) == {x. x:R & Wfd(R)}"

  wmap_def:       "wmap(f,R) == {p. EX x y. p=<x,y>  &  <f(x),f(y)> : R}"
  lex_def:
  "ra**rb == {p. EX a a' b b'. p = <<a,b>,<a',b'>> & (<a,a'> : ra | (a=a' & <b,b'> : rb))}"

  NatPR_def:      "NatPR == {p. EX x:Nat. p=<x,succ(x)>}"
  ListPR_def:     "ListPR(A) == {p. EX h:A. EX t:List(A). p=<t,h$t>}"


lemma wfd_induct:
  assumes 1: "Wfd(R)"
    and 2: "!!x.[| ALL y. <y,x>: R --> P(y) |] ==> P(x)"
  shows "P(a)"
  apply (rule 1 [unfolded Wfd_def, rule_format, THEN CollectD])
  using 2 apply blast
  done

lemma wfd_strengthen_lemma:
  assumes 1: "!!x y.<x,y> : R ==> Q(x)"
    and 2: "ALL x. (ALL y. <y,x> : R --> y : P) --> x : P"
    and 3: "!!x. Q(x) ==> x:P"
  shows "a:P"
  apply (rule 2 [rule_format])
  using 1 3
  apply blast
  done

ML {*
  fun wfd_strengthen_tac ctxt s i =
    res_inst_tac ctxt [(("Q", 0), s)] @{thm wfd_strengthen_lemma} i THEN assume_tac (i+1)
*}

lemma wf_anti_sym: "[| Wfd(r);  <a,x>:r;  <x,a>:r |] ==> P"
  apply (subgoal_tac "ALL x. <a,x>:r --> <x,a>:r --> P")
   apply blast
  apply (erule wfd_induct)
  apply blast
  done

lemma wf_anti_refl: "[| Wfd(r);  <a,a>: r |] ==> P"
  apply (rule wf_anti_sym)
  apply assumption+
  done


subsection {* Irreflexive transitive closure *}

lemma trancl_wf:
  assumes 1: "Wfd(R)"
  shows "Wfd(R^+)"
  apply (unfold Wfd_def)
  apply (rule allI ballI impI)+
(*must retain the universal formula for later use!*)
  apply (rule allE, assumption)
  apply (erule mp)
  apply (rule 1 [THEN wfd_induct])
  apply (rule impI [THEN allI])
  apply (erule tranclE)
   apply blast
  apply (erule spec [THEN mp, THEN spec, THEN mp])
   apply assumption+
  done


subsection {* Lexicographic Ordering *}

lemma lexXH:
  "p : ra**rb <-> (EX a a' b b'. p = <<a,b>,<a',b'>> & (<a,a'> : ra | a=a' & <b,b'> : rb))"
  unfolding lex_def by blast

lemma lexI1: "<a,a'> : ra ==> <<a,b>,<a',b'>> : ra**rb"
  by (blast intro!: lexXH [THEN iffD2])

lemma lexI2: "<b,b'> : rb ==> <<a,b>,<a,b'>> : ra**rb"
  by (blast intro!: lexXH [THEN iffD2])

lemma lexE:
  assumes 1: "p : ra**rb"
    and 2: "!!a a' b b'.[| <a,a'> : ra; p=<<a,b>,<a',b'>> |] ==> R"
    and 3: "!!a b b'.[| <b,b'> : rb;  p = <<a,b>,<a,b'>> |] ==> R"
  shows R
  apply (rule 1 [THEN lexXH [THEN iffD1], THEN exE])
  using 2 3
  apply blast
  done

lemma lex_pair: "[| p : r**s;  !!a a' b b'. p = <<a,b>,<a',b'>> ==> P |] ==>P"
  apply (erule lexE)
   apply blast+
  done

lemma lex_wf:
  assumes 1: "Wfd(R)"
    and 2: "Wfd(S)"
  shows "Wfd(R**S)"
  apply (unfold Wfd_def)
  apply safe
  apply (tactic {* wfd_strengthen_tac @{context} "%x. EX a b. x=<a,b>" 1 *})
   apply (blast elim!: lex_pair)
  apply (subgoal_tac "ALL a b.<a,b>:P")
   apply blast
  apply (rule 1 [THEN wfd_induct, THEN allI])
  apply (rule 2 [THEN wfd_induct, THEN allI]) back
  apply (fast elim!: lexE)
  done


subsection {* Mapping *}

lemma wmapXH: "p : wmap(f,r) <-> (EX x y. p=<x,y>  &  <f(x),f(y)> : r)"
  unfolding wmap_def by blast

lemma wmapI: "<f(a),f(b)> : r ==> <a,b> : wmap(f,r)"
  by (blast intro!: wmapXH [THEN iffD2])

lemma wmapE: "[| p : wmap(f,r);  !!a b.[| <f(a),f(b)> : r;  p=<a,b> |] ==> R |] ==> R"
  by (blast dest!: wmapXH [THEN iffD1])

lemma wmap_wf:
  assumes 1: "Wfd(r)"
  shows "Wfd(wmap(f,r))"
  apply (unfold Wfd_def)
  apply clarify
  apply (subgoal_tac "ALL b. ALL a. f (a) =b-->a:P")
   apply blast
  apply (rule 1 [THEN wfd_induct, THEN allI])
  apply clarify
  apply (erule spec [THEN mp])
  apply (safe elim!: wmapE)
  apply (erule spec [THEN mp, THEN spec, THEN mp])
   apply assumption
   apply (rule refl)
  done


subsection {* Projections *}

lemma wfstI: "<xa,ya> : r ==> <<xa,xb>,<ya,yb>> : wmap(fst,r)"
  apply (rule wmapI)
  apply simp
  done

lemma wsndI: "<xb,yb> : r ==> <<xa,xb>,<ya,yb>> : wmap(snd,r)"
  apply (rule wmapI)
  apply simp
  done

lemma wthdI: "<xc,yc> : r ==> <<xa,<xb,xc>>,<ya,<yb,yc>>> : wmap(thd,r)"
  apply (rule wmapI)
  apply simp
  done


subsection {* Ground well-founded relations *}

lemma wfI: "[| Wfd(r);  a : r |] ==> a : wf(r)"
  unfolding wf_def by blast

lemma Empty_wf: "Wfd({})"
  unfolding Wfd_def by (blast elim: EmptyXH [THEN iffD1, THEN FalseE])

lemma wf_wf: "Wfd(wf(R))"
  unfolding wf_def
  apply (rule_tac Q = "Wfd(R)" in excluded_middle [THEN disjE])
   apply simp_all
  apply (rule Empty_wf)
  done

lemma NatPRXH: "p : NatPR <-> (EX x:Nat. p=<x,succ(x)>)"
  unfolding NatPR_def by blast

lemma ListPRXH: "p : ListPR(A) <-> (EX h:A. EX t:List(A).p=<t,h$t>)"
  unfolding ListPR_def by blast

lemma NatPRI: "x : Nat ==> <x,succ(x)> : NatPR"
  by (auto simp: NatPRXH)

lemma ListPRI: "[| t : List(A); h : A |] ==> <t,h $ t> : ListPR(A)"
  by (auto simp: ListPRXH)

lemma NatPR_wf: "Wfd(NatPR)"
  apply (unfold Wfd_def)
  apply clarify
  apply (tactic {* wfd_strengthen_tac @{context} "%x. x:Nat" 1 *})
   apply (fastforce iff: NatPRXH)
  apply (erule Nat_ind)
   apply (fastforce iff: NatPRXH)+
  done

lemma ListPR_wf: "Wfd(ListPR(A))"
  apply (unfold Wfd_def)
  apply clarify
  apply (tactic {* wfd_strengthen_tac @{context} "%x. x:List (A)" 1 *})
   apply (fastforce iff: ListPRXH)
  apply (erule List_ind)
   apply (fastforce iff: ListPRXH)+
  done


subsection {* General Recursive Functions *}

lemma letrecT:
  assumes 1: "a : A"
    and 2: "!!p g.[| p:A; ALL x:{x: A. <x,p>:wf(R)}. g(x) : D(x) |] ==> h(p,g) : D(p)"
  shows "letrec g x be h(x,g) in g(a) : D(a)"
  apply (rule 1 [THEN rev_mp])
  apply (rule wf_wf [THEN wfd_induct])
  apply (subst letrecB)
  apply (rule impI)
  apply (erule 2)
  apply blast
  done

lemma SPLITB: "SPLIT(<a,b>,B) = B(a,b)"
  unfolding SPLIT_def
  apply (rule set_ext)
  apply blast
  done

lemma letrec2T:
  assumes "a : A"
    and "b : B"
    and "!!p q g.[| p:A; q:B;
              ALL x:A. ALL y:{y: B. <<x,y>,<p,q>>:wf(R)}. g(x,y) : D(x,y) |] ==> 
                h(p,q,g) : D(p,q)"
  shows "letrec g x y be h(x,y,g) in g(a,b) : D(a,b)"
  apply (unfold letrec2_def)
  apply (rule SPLITB [THEN subst])
  apply (assumption | rule letrecT pairT splitT assms)+
  apply (subst SPLITB)
  apply (assumption | rule ballI SubtypeI assms)+
  apply (rule SPLITB [THEN subst])
  apply (assumption | rule letrecT SubtypeI pairT splitT assms |
    erule bspec SubtypeE sym [THEN subst])+
  done

lemma lem: "SPLIT(<a,<b,c>>,%x xs. SPLIT(xs,%y z. B(x,y,z))) = B(a,b,c)"
  by (simp add: SPLITB)

lemma letrec3T:
  assumes "a : A"
    and "b : B"
    and "c : C"
    and "!!p q r g.[| p:A; q:B; r:C;
       ALL x:A. ALL y:B. ALL z:{z:C. <<x,<y,z>>,<p,<q,r>>> : wf(R)}.  
                                                        g(x,y,z) : D(x,y,z) |] ==> 
                h(p,q,r,g) : D(p,q,r)"
  shows "letrec g x y z be h(x,y,z,g) in g(a,b,c) : D(a,b,c)"
  apply (unfold letrec3_def)
  apply (rule lem [THEN subst])
  apply (assumption | rule letrecT pairT splitT assms)+
  apply (simp add: SPLITB)
  apply (assumption | rule ballI SubtypeI assms)+
  apply (rule lem [THEN subst])
  apply (assumption | rule letrecT SubtypeI pairT splitT assms |
    erule bspec SubtypeE sym [THEN subst])+
  done

lemmas letrecTs = letrecT letrec2T letrec3T


subsection {* Type Checking for Recursive Calls *}

lemma rcallT:
  "[| ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x);  
      g(a) : D(a) ==> g(a) : E;  a:A;  <a,p>:wf(R) |] ==>  
  g(a) : E"
  by blast

lemma rcall2T:
  "[| ALL x:A. ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y);  
      g(a,b) : D(a,b) ==> g(a,b) : E;  a:A;  b:B;  <<a,b>,<p,q>>:wf(R) |] ==>  
  g(a,b) : E"
  by blast

lemma rcall3T:
  "[| ALL x:A. ALL y:B. ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}. g(x,y,z):D(x,y,z);  
      g(a,b,c) : D(a,b,c) ==> g(a,b,c) : E;   
      a:A;  b:B;  c:C;  <<a,<b,c>>,<p,<q,r>>> : wf(R) |] ==>  
  g(a,b,c) : E"
  by blast

lemmas rcallTs = rcallT rcall2T rcall3T


subsection {* Instantiating an induction hypothesis with an equality assumption *}

lemma hyprcallT:
  assumes 1: "g(a) = b"
    and 2: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x)"
    and 3: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) ==> b=g(a) ==> g(a) : D(a) ==> P"
    and 4: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) ==> a:A"
    and 5: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) ==> <a,p>:wf(R)"
  shows P
  apply (rule 3 [OF 2, OF 1 [symmetric]])
  apply (rule rcallT [OF 2])
    apply assumption
   apply (rule 4 [OF 2])
  apply (rule 5 [OF 2])
  done

lemma hyprcall2T:
  assumes 1: "g(a,b) = c"
    and 2: "ALL x:A. ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y)"
    and 3: "[| c=g(a,b);  g(a,b) : D(a,b) |] ==> P"
    and 4: "a:A"
    and 5: "b:B"
    and 6: "<<a,b>,<p,q>>:wf(R)"
  shows P
  apply (rule 3)
    apply (rule 1 [symmetric])
  apply (rule rcall2T)
      apply (rule 2)
     apply assumption
    apply (rule 4)
   apply (rule 5)
  apply (rule 6)
  done

lemma hyprcall3T:
  assumes 1: "g(a,b,c) = d"
    and 2: "ALL x:A. ALL y:B. ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}.g(x,y,z):D(x,y,z)"
    and 3: "[| d=g(a,b,c);  g(a,b,c) : D(a,b,c) |] ==> P"
    and 4: "a:A"
    and 5: "b:B"
    and 6: "c:C"
    and 7: "<<a,<b,c>>,<p,<q,r>>> : wf(R)"
  shows P
  apply (rule 3)
   apply (rule 1 [symmetric])
  apply (rule rcall3T)
       apply (rule 2)
      apply assumption
     apply (rule 4)
    apply (rule 5)
   apply (rule 6)
  apply (rule 7)
  done

lemmas hyprcallTs = hyprcallT hyprcall2T hyprcall3T


subsection {* Rules to Remove Induction Hypotheses after Type Checking *}

lemma rmIH1: "[| ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x); P |] ==> P" .

lemma rmIH2: "[| ALL x:A. ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y); P |] ==> P" .
  
lemma rmIH3:
 "[| ALL x:A. ALL y:B. ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}.g(x,y,z):D(x,y,z);  
     P |] ==>  
     P" .

lemmas rmIHs = rmIH1 rmIH2 rmIH3


subsection {* Lemmas for constructors and subtypes *}

(* 0-ary constructors do not need additional rules as they are handled *)
(*                                      correctly by applying SubtypeI *)

lemma Subtype_canTs:
  "!!a b A B P. a : {x:A. b:{y:B(a).P(<x,y>)}} ==> <a,b> : {x:Sigma(A,B).P(x)}"
  "!!a A B P. a : {x:A. P(inl(x))} ==> inl(a) : {x:A+B. P(x)}"
  "!!b A B P. b : {x:B. P(inr(x))} ==> inr(b) : {x:A+B. P(x)}"
  "!!a P. a : {x:Nat. P(succ(x))} ==> succ(a) : {x:Nat. P(x)}"
  "!!h t A P. h : {x:A. t : {y:List(A).P(x$y)}} ==> h$t : {x:List(A).P(x)}"
  by (assumption | rule SubtypeI canTs icanTs | erule SubtypeE)+

lemma letT: "[| f(t):B;  ~t=bot  |] ==> let x be t in f(x) : B"
  apply (erule letB [THEN ssubst])
  apply assumption
  done

lemma applyT2: "[| a:A;  f : Pi(A,B)  |] ==> f ` a  : B(a)"
  apply (erule applyT)
  apply assumption
  done

lemma rcall_lemma1: "[| a:A;  a:A ==> P(a) |] ==> a : {x:A. P(x)}"
  by blast

lemma rcall_lemma2: "[| a:{x:A. Q(x)};  [| a:A; Q(a) |] ==> P(a) |] ==> a : {x:A. P(x)}"
  by blast

lemmas rcall_lemmas = asm_rl rcall_lemma1 SubtypeD1 rcall_lemma2


subsection {* Typechecking *}

ML {*

local

val type_rls =
  @{thms canTs} @ @{thms icanTs} @ @{thms applyT2} @ @{thms ncanTs} @ @{thms incanTs} @
  @{thms precTs} @ @{thms letrecTs} @ @{thms letT} @ @{thms Subtype_canTs};

fun bvars (Const(@{const_name all},_) $ Abs(s,_,t)) l = bvars t (s::l)
  | bvars _ l = l

fun get_bno l n (Const(@{const_name all},_) $ Abs(s,_,t)) = get_bno (s::l) n t
  | get_bno l n (Const(@{const_name Trueprop},_) $ t) = get_bno l n t
  | get_bno l n (Const(@{const_name Ball},_) $ _ $ Abs(s,_,t)) = get_bno (s::l) (n+1) t
  | get_bno l n (Const(@{const_name mem},_) $ t $ _) = get_bno l n t
  | get_bno l n (t $ s) = get_bno l n t
  | get_bno l n (Bound m) = (m-length(l),n)

(* Not a great way of identifying induction hypothesis! *)
fun could_IH x = Term.could_unify(x,hd (prems_of @{thm rcallT})) orelse
                 Term.could_unify(x,hd (prems_of @{thm rcall2T})) orelse
                 Term.could_unify(x,hd (prems_of @{thm rcall3T}))

fun IHinst tac rls = SUBGOAL (fn (Bi,i) =>
  let val bvs = bvars Bi []
      val ihs = filter could_IH (Logic.strip_assums_hyp Bi)
      val rnames = map (fn x=>
                    let val (a,b) = get_bno [] 0 x
                    in (nth bvs a, b) end) ihs
      fun try_IHs [] = no_tac
        | try_IHs ((x,y)::xs) = tac [(("g", 0), x)] (nth rls (y - 1)) i ORELSE (try_IHs xs)
  in try_IHs rnames end)

fun is_rigid_prog t =
     case (Logic.strip_assums_concl t) of
        (Const(@{const_name Trueprop},_) $ (Const(@{const_name mem},_) $ a $ _)) => null (Term.add_vars a [])
       | _ => false
in

fun rcall_tac ctxt i =
  let fun tac ps rl i = res_inst_tac ctxt ps rl i THEN atac i
  in IHinst tac @{thms rcallTs} i end
  THEN eresolve_tac @{thms rcall_lemmas} i

fun raw_step_tac ctxt prems i = ares_tac (prems@type_rls) i ORELSE
                           rcall_tac ctxt i ORELSE
                           ematch_tac [@{thm SubtypeE}] i ORELSE
                           match_tac [@{thm SubtypeI}] i

fun tc_step_tac ctxt prems = SUBGOAL (fn (Bi,i) =>
          if is_rigid_prog Bi then raw_step_tac ctxt prems i else no_tac)

fun typechk_tac ctxt rls i = SELECT_GOAL (REPEAT_FIRST (tc_step_tac ctxt rls)) i

fun tac ctxt = typechk_tac ctxt [] 1

(*** Clean up Correctness Condictions ***)

val clean_ccs_tac = REPEAT_FIRST (eresolve_tac ([@{thm SubtypeE}] @ @{thms rmIHs}) ORELSE'
                                 hyp_subst_tac)

fun clean_ccs_tac ctxt =
  let fun tac ps rl i = eres_inst_tac ctxt ps rl i THEN atac i in
    TRY (REPEAT_FIRST (IHinst tac @{thms hyprcallTs} ORELSE'
    eresolve_tac ([asm_rl, @{thm SubtypeE}] @ @{thms rmIHs}) ORELSE'
    hyp_subst_tac))
  end

fun gen_ccs_tac ctxt rls i =
  SELECT_GOAL (REPEAT_FIRST (tc_step_tac ctxt rls) THEN clean_ccs_tac ctxt) i

end
*}


subsection {* Evaluation *}

ML {*
structure Eval_Rules =
  Named_Thms(val name = @{binding eval} val description = "evaluation rules");

fun eval_tac ths =
  Subgoal.FOCUS_PREMS (fn {context, prems, ...} =>
    DEPTH_SOLVE_1 (resolve_tac (ths @ prems @ Eval_Rules.get context) 1));
*}
setup Eval_Rules.setup

method_setup eval = {*
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (CHANGED o eval_tac ths ctxt))
*}


lemmas eval_rls [eval] = trueV falseV pairV lamV caseVtrue caseVfalse caseVpair caseVlam

lemma applyV [eval]:
  assumes "f ---> lam x. b(x)"
    and "b(a) ---> c"
  shows "f ` a ---> c"
  unfolding apply_def by (eval assms)

lemma letV:
  assumes 1: "t ---> a"
    and 2: "f(a) ---> c"
  shows "let x be t in f(x) ---> c"
  apply (unfold let_def)
  apply (rule 1 [THEN canonical])
  apply (tactic {*
    REPEAT (DEPTH_SOLVE_1 (resolve_tac (@{thms assms} @ @{thms eval_rls}) 1 ORELSE
      etac @{thm substitute} 1)) *})
  done

lemma fixV: "f(fix(f)) ---> c ==> fix(f) ---> c"
  apply (unfold fix_def)
  apply (rule applyV)
   apply (rule lamV)
  apply assumption
  done

lemma letrecV:
  "h(t,%y. letrec g x be h(x,g) in g(y)) ---> c ==>  
                 letrec g x be h(x,g) in g(t) ---> c"
  apply (unfold letrec_def)
  apply (assumption | rule fixV applyV  lamV)+
  done

lemmas [eval] = letV letrecV fixV

lemma V_rls [eval]:
  "true ---> true"
  "false ---> false"
  "!!b c t u. [| b--->true;  t--->c |] ==> if b then t else u ---> c"
  "!!b c t u. [| b--->false;  u--->c |] ==> if b then t else u ---> c"
  "!!a b. <a,b> ---> <a,b>"
  "!!a b c t h. [| t ---> <a,b>;  h(a,b) ---> c |] ==> split(t,h) ---> c"
  "zero ---> zero"
  "!!n. succ(n) ---> succ(n)"
  "!!c n t u. [| n ---> zero; t ---> c |] ==> ncase(n,t,u) ---> c"
  "!!c n t u x. [| n ---> succ(x); u(x) ---> c |] ==> ncase(n,t,u) ---> c"
  "!!c n t u. [| n ---> zero; t ---> c |] ==> nrec(n,t,u) ---> c"
  "!!c n t u x. [| n--->succ(x); u(x,nrec(x,t,u))--->c |] ==> nrec(n,t,u)--->c"
  "[] ---> []"
  "!!h t. h$t ---> h$t"
  "!!c l t u. [| l ---> []; t ---> c |] ==> lcase(l,t,u) ---> c"
  "!!c l t u x xs. [| l ---> x$xs; u(x,xs) ---> c |] ==> lcase(l,t,u) ---> c"
  "!!c l t u. [| l ---> []; t ---> c |] ==> lrec(l,t,u) ---> c"
  "!!c l t u x xs. [| l--->x$xs; u(x,xs,lrec(xs,t,u))--->c |] ==> lrec(l,t,u)--->c"
  unfolding data_defs by eval+


subsection {* Factorial *}

schematic_lemma
  "letrec f n be ncase(n,succ(zero),%x. nrec(n,zero,%y g. nrec(f(x),g,%z h. succ(h))))  
   in f(succ(succ(zero))) ---> ?a"
  by eval

schematic_lemma
  "letrec f n be ncase(n,succ(zero),%x. nrec(n,zero,%y g. nrec(f(x),g,%z h. succ(h))))  
   in f(succ(succ(succ(zero)))) ---> ?a"
  by eval

subsection {* Less Than Or Equal *}

schematic_lemma
  "letrec f p be split(p,%m n. ncase(m,true,%x. ncase(n,false,%y. f(<x,y>))))
   in f(<succ(zero), succ(zero)>) ---> ?a"
  by eval

schematic_lemma
  "letrec f p be split(p,%m n. ncase(m,true,%x. ncase(n,false,%y. f(<x,y>))))
   in f(<succ(zero), succ(succ(succ(succ(zero))))>) ---> ?a"
  by eval

schematic_lemma
  "letrec f p be split(p,%m n. ncase(m,true,%x. ncase(n,false,%y. f(<x,y>))))
   in f(<succ(succ(succ(succ(succ(zero))))), succ(succ(succ(succ(zero))))>) ---> ?a"
  by eval


subsection {* Reverse *}

schematic_lemma
  "letrec id l be lcase(l,[],%x xs. x$id(xs))  
   in id(zero$succ(zero)$[]) ---> ?a"
  by eval

schematic_lemma
  "letrec rev l be lcase(l,[],%x xs. lrec(rev(xs),x$[],%y ys g. y$g))  
   in rev(zero$succ(zero)$(succ((lam x. x)`succ(zero)))$([])) ---> ?a"
  by eval

end
