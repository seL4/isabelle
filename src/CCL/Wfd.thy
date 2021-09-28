(*  Title:      CCL/Wfd.thy
    Author:     Martin Coen, Cambridge University Computer Laboratory
    Copyright   1993  University of Cambridge
*)

section \<open>Well-founded relations in CCL\<close>

theory Wfd
imports Trancl Type Hered
begin

definition Wfd :: "[i set] \<Rightarrow> o"
  where "Wfd(R) == ALL P.(ALL x.(ALL y.<y,x> : R \<longrightarrow> y:P) \<longrightarrow> x:P) \<longrightarrow> (ALL a. a:P)"

definition wf :: "[i set] \<Rightarrow> i set"
  where "wf(R) == {x. x:R \<and> Wfd(R)}"

definition wmap :: "[i\<Rightarrow>i,i set] \<Rightarrow> i set"
  where "wmap(f,R) == {p. EX x y. p=<x,y> \<and> <f(x),f(y)> : R}"

definition lex :: "[i set,i set] => i set"      (infixl "**" 70)
  where "ra**rb == {p. EX a a' b b'. p = <<a,b>,<a',b'>> \<and> (<a,a'> : ra | (a=a' \<and> <b,b'> : rb))}"

definition NatPR :: "i set"
  where "NatPR == {p. EX x:Nat. p=<x,succ(x)>}"

definition ListPR :: "i set \<Rightarrow> i set"
  where "ListPR(A) == {p. EX h:A. EX t:List(A). p=<t,h$t>}"


lemma wfd_induct:
  assumes 1: "Wfd(R)"
    and 2: "\<And>x. ALL y. <y,x>: R \<longrightarrow> P(y) \<Longrightarrow> P(x)"
  shows "P(a)"
  apply (rule 1 [unfolded Wfd_def, rule_format, THEN CollectD])
  using 2 apply blast
  done

lemma wfd_strengthen_lemma:
  assumes 1: "\<And>x y.<x,y> : R \<Longrightarrow> Q(x)"
    and 2: "ALL x. (ALL y. <y,x> : R \<longrightarrow> y : P) \<longrightarrow> x : P"
    and 3: "\<And>x. Q(x) \<Longrightarrow> x:P"
  shows "a:P"
  apply (rule 2 [rule_format])
  using 1 3
  apply blast
  done

method_setup wfd_strengthen = \<open>
  Scan.lift Args.embedded_inner_syntax >> (fn s => fn ctxt =>
    SIMPLE_METHOD' (fn i =>
      Rule_Insts.res_inst_tac ctxt [((("Q", 0), Position.none), s)] [] @{thm wfd_strengthen_lemma} i
        THEN assume_tac ctxt (i + 1)))
\<close>

lemma wf_anti_sym: "\<lbrakk>Wfd(r); <a,x>:r; <x,a>:r\<rbrakk> \<Longrightarrow> P"
  apply (subgoal_tac "ALL x. <a,x>:r \<longrightarrow> <x,a>:r \<longrightarrow> P")
   apply blast
  apply (erule wfd_induct)
  apply blast
  done

lemma wf_anti_refl: "\<lbrakk>Wfd(r); <a,a>: r\<rbrakk> \<Longrightarrow> P"
  apply (rule wf_anti_sym)
  apply assumption+
  done


subsection \<open>Irreflexive transitive closure\<close>

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


subsection \<open>Lexicographic Ordering\<close>

lemma lexXH:
  "p : ra**rb \<longleftrightarrow> (EX a a' b b'. p = <<a,b>,<a',b'>> \<and> (<a,a'> : ra | a=a' \<and> <b,b'> : rb))"
  unfolding lex_def by blast

lemma lexI1: "<a,a'> : ra \<Longrightarrow> <<a,b>,<a',b'>> : ra**rb"
  by (blast intro!: lexXH [THEN iffD2])

lemma lexI2: "<b,b'> : rb \<Longrightarrow> <<a,b>,<a,b'>> : ra**rb"
  by (blast intro!: lexXH [THEN iffD2])

lemma lexE:
  assumes 1: "p : ra**rb"
    and 2: "\<And>a a' b b'. \<lbrakk><a,a'> : ra; p=<<a,b>,<a',b'>>\<rbrakk> \<Longrightarrow> R"
    and 3: "\<And>a b b'. \<lbrakk><b,b'> : rb; p = <<a,b>,<a,b'>>\<rbrakk> \<Longrightarrow> R"
  shows R
  apply (rule 1 [THEN lexXH [THEN iffD1], THEN exE])
  using 2 3
  apply blast
  done

lemma lex_pair: "\<lbrakk>p : r**s; \<And>a a' b b'. p = <<a,b>,<a',b'>> \<Longrightarrow> P\<rbrakk> \<Longrightarrow>P"
  apply (erule lexE)
   apply blast+
  done

lemma lex_wf:
  assumes 1: "Wfd(R)"
    and 2: "Wfd(S)"
  shows "Wfd(R**S)"
  apply (unfold Wfd_def)
  apply safe
  apply (wfd_strengthen "\<lambda>x. EX a b. x=<a,b>")
   apply (blast elim!: lex_pair)
  apply (subgoal_tac "ALL a b.<a,b>:P")
   apply blast
  apply (rule 1 [THEN wfd_induct, THEN allI])
  apply (rule 2 [THEN wfd_induct, THEN allI]) back
  apply (fast elim!: lexE)
  done


subsection \<open>Mapping\<close>

lemma wmapXH: "p : wmap(f,r) \<longleftrightarrow> (EX x y. p=<x,y> \<and> <f(x),f(y)> : r)"
  unfolding wmap_def by blast

lemma wmapI: "<f(a),f(b)> : r \<Longrightarrow> <a,b> : wmap(f,r)"
  by (blast intro!: wmapXH [THEN iffD2])

lemma wmapE: "\<lbrakk>p : wmap(f,r); \<And>a b. \<lbrakk><f(a),f(b)> : r; p=<a,b>\<rbrakk> \<Longrightarrow> R\<rbrakk> \<Longrightarrow> R"
  by (blast dest!: wmapXH [THEN iffD1])

lemma wmap_wf:
  assumes 1: "Wfd(r)"
  shows "Wfd(wmap(f,r))"
  apply (unfold Wfd_def)
  apply clarify
  apply (subgoal_tac "ALL b. ALL a. f (a) = b \<longrightarrow> a:P")
   apply blast
  apply (rule 1 [THEN wfd_induct, THEN allI])
  apply clarify
  apply (erule spec [THEN mp])
  apply (safe elim!: wmapE)
  apply (erule spec [THEN mp, THEN spec, THEN mp])
   apply assumption
   apply (rule refl)
  done


subsection \<open>Projections\<close>

lemma wfstI: "<xa,ya> : r \<Longrightarrow> <<xa,xb>,<ya,yb>> : wmap(fst,r)"
  apply (rule wmapI)
  apply simp
  done

lemma wsndI: "<xb,yb> : r \<Longrightarrow> <<xa,xb>,<ya,yb>> : wmap(snd,r)"
  apply (rule wmapI)
  apply simp
  done

lemma wthdI: "<xc,yc> : r \<Longrightarrow> <<xa,<xb,xc>>,<ya,<yb,yc>>> : wmap(thd,r)"
  apply (rule wmapI)
  apply simp
  done


subsection \<open>Ground well-founded relations\<close>

lemma wfI: "\<lbrakk>Wfd(r);  a : r\<rbrakk> \<Longrightarrow> a : wf(r)"
  unfolding wf_def by blast

lemma Empty_wf: "Wfd({})"
  unfolding Wfd_def by (blast elim: EmptyXH [THEN iffD1, THEN FalseE])

lemma wf_wf: "Wfd(wf(R))"
  unfolding wf_def
  apply (rule_tac Q = "Wfd(R)" in excluded_middle [THEN disjE])
   apply simp_all
  apply (rule Empty_wf)
  done

lemma NatPRXH: "p : NatPR \<longleftrightarrow> (EX x:Nat. p=<x,succ(x)>)"
  unfolding NatPR_def by blast

lemma ListPRXH: "p : ListPR(A) \<longleftrightarrow> (EX h:A. EX t:List(A).p=<t,h$t>)"
  unfolding ListPR_def by blast

lemma NatPRI: "x : Nat \<Longrightarrow> <x,succ(x)> : NatPR"
  by (auto simp: NatPRXH)

lemma ListPRI: "\<lbrakk>t : List(A); h : A\<rbrakk> \<Longrightarrow> <t,h $ t> : ListPR(A)"
  by (auto simp: ListPRXH)

lemma NatPR_wf: "Wfd(NatPR)"
  apply (unfold Wfd_def)
  apply clarify
  apply (wfd_strengthen "\<lambda>x. x:Nat")
   apply (fastforce iff: NatPRXH)
  apply (erule Nat_ind)
   apply (fastforce iff: NatPRXH)+
  done

lemma ListPR_wf: "Wfd(ListPR(A))"
  apply (unfold Wfd_def)
  apply clarify
  apply (wfd_strengthen "\<lambda>x. x:List (A)")
   apply (fastforce iff: ListPRXH)
  apply (erule List_ind)
   apply (fastforce iff: ListPRXH)+
  done


subsection \<open>General Recursive Functions\<close>

lemma letrecT:
  assumes 1: "a : A"
    and 2: "\<And>p g. \<lbrakk>p:A; ALL x:{x: A. <x,p>:wf(R)}. g(x) : D(x)\<rbrakk> \<Longrightarrow> h(p,g) : D(p)"
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
    and "\<And>p q g. \<lbrakk>p:A; q:B;
              ALL x:A. ALL y:{y: B. <<x,y>,<p,q>>:wf(R)}. g(x,y) : D(x,y)\<rbrakk> \<Longrightarrow> 
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

lemma lem: "SPLIT(<a,<b,c>>,\<lambda>x xs. SPLIT(xs,\<lambda>y z. B(x,y,z))) = B(a,b,c)"
  by (simp add: SPLITB)

lemma letrec3T:
  assumes "a : A"
    and "b : B"
    and "c : C"
    and "\<And>p q r g. \<lbrakk>p:A; q:B; r:C;
       ALL x:A. ALL y:B. ALL z:{z:C. <<x,<y,z>>,<p,<q,r>>> : wf(R)}.
                                                        g(x,y,z) : D(x,y,z) \<rbrakk> \<Longrightarrow>
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


subsection \<open>Type Checking for Recursive Calls\<close>

lemma rcallT:
  "\<lbrakk>ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x);  
    g(a) : D(a) \<Longrightarrow> g(a) : E;  a:A;  <a,p>:wf(R)\<rbrakk> \<Longrightarrow> g(a) : E"
  by blast

lemma rcall2T:
  "\<lbrakk>ALL x:A. ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y);
    g(a,b) : D(a,b) \<Longrightarrow> g(a,b) : E; a:A; b:B; <<a,b>,<p,q>>:wf(R)\<rbrakk> \<Longrightarrow> g(a,b) : E"
  by blast

lemma rcall3T:
  "\<lbrakk>ALL x:A. ALL y:B. ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}. g(x,y,z):D(x,y,z);
    g(a,b,c) : D(a,b,c) \<Longrightarrow> g(a,b,c) : E;
    a:A; b:B; c:C; <<a,<b,c>>,<p,<q,r>>> : wf(R)\<rbrakk> \<Longrightarrow> g(a,b,c) : E"
  by blast

lemmas rcallTs = rcallT rcall2T rcall3T


subsection \<open>Instantiating an induction hypothesis with an equality assumption\<close>

lemma hyprcallT:
  assumes 1: "g(a) = b"
    and 2: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x)"
    and 3: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) \<Longrightarrow> b=g(a) \<Longrightarrow> g(a) : D(a) \<Longrightarrow> P"
    and 4: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) \<Longrightarrow> a:A"
    and 5: "ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x) \<Longrightarrow> <a,p>:wf(R)"
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
    and 3: "\<lbrakk>c = g(a,b); g(a,b) : D(a,b)\<rbrakk> \<Longrightarrow> P"
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
    and 3: "\<lbrakk>d = g(a,b,c); g(a,b,c) : D(a,b,c)\<rbrakk> \<Longrightarrow> P"
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


subsection \<open>Rules to Remove Induction Hypotheses after Type Checking\<close>

lemma rmIH1: "\<lbrakk>ALL x:{x:A.<x,p>:wf(R)}.g(x):D(x); P\<rbrakk> \<Longrightarrow> P" .

lemma rmIH2: "\<lbrakk>ALL x:A. ALL y:{y:B.<<x,y>,<p,q>>:wf(R)}.g(x,y):D(x,y); P\<rbrakk> \<Longrightarrow> P" .
  
lemma rmIH3:
 "\<lbrakk>ALL x:A. ALL y:B. ALL z:{z:C.<<x,<y,z>>,<p,<q,r>>>:wf(R)}.g(x,y,z):D(x,y,z); P\<rbrakk> \<Longrightarrow> P" .

lemmas rmIHs = rmIH1 rmIH2 rmIH3


subsection \<open>Lemmas for constructors and subtypes\<close>

(* 0-ary constructors do not need additional rules as they are handled *)
(*                                      correctly by applying SubtypeI *)

lemma Subtype_canTs:
  "\<And>a b A B P. a : {x:A. b:{y:B(a).P(<x,y>)}} \<Longrightarrow> <a,b> : {x:Sigma(A,B).P(x)}"
  "\<And>a A B P. a : {x:A. P(inl(x))} \<Longrightarrow> inl(a) : {x:A+B. P(x)}"
  "\<And>b A B P. b : {x:B. P(inr(x))} \<Longrightarrow> inr(b) : {x:A+B. P(x)}"
  "\<And>a P. a : {x:Nat. P(succ(x))} \<Longrightarrow> succ(a) : {x:Nat. P(x)}"
  "\<And>h t A P. h : {x:A. t : {y:List(A).P(x$y)}} \<Longrightarrow> h$t : {x:List(A).P(x)}"
  by (assumption | rule SubtypeI canTs icanTs | erule SubtypeE)+

lemma letT: "\<lbrakk>f(t):B; \<not>t=bot\<rbrakk> \<Longrightarrow> let x be t in f(x) : B"
  apply (erule letB [THEN ssubst])
  apply assumption
  done

lemma applyT2: "\<lbrakk>a:A; f : Pi(A,B)\<rbrakk> \<Longrightarrow> f ` a  : B(a)"
  apply (erule applyT)
  apply assumption
  done

lemma rcall_lemma1: "\<lbrakk>a:A; a:A \<Longrightarrow> P(a)\<rbrakk> \<Longrightarrow> a : {x:A. P(x)}"
  by blast

lemma rcall_lemma2: "\<lbrakk>a:{x:A. Q(x)}; \<lbrakk>a:A; Q(a)\<rbrakk> \<Longrightarrow> P(a)\<rbrakk> \<Longrightarrow> a : {x:A. P(x)}"
  by blast

lemmas rcall_lemmas = asm_rl rcall_lemma1 SubtypeD1 rcall_lemma2


subsection \<open>Typechecking\<close>

ML \<open>
local

val type_rls =
  @{thms canTs} @ @{thms icanTs} @ @{thms applyT2} @ @{thms ncanTs} @ @{thms incanTs} @
  @{thms precTs} @ @{thms letrecTs} @ @{thms letT} @ @{thms Subtype_canTs};

fun bvars \<^Const_>\<open>Pure.all _ for \<open>Abs(s,_,t)\<close>\<close> l = bvars t (s::l)
  | bvars _ l = l

fun get_bno l n \<^Const_>\<open>Pure.all _ for \<open>Abs(s,_,t)\<close>\<close> = get_bno (s::l) n t
  | get_bno l n \<^Const_>\<open>Trueprop for t\<close> = get_bno l n t
  | get_bno l n \<^Const_>\<open>Ball _ for _ \<open>Abs(s,_,t)\<close>\<close> = get_bno (s::l) (n+1) t
  | get_bno l n \<^Const_>\<open>mem _ for t _\<close> = get_bno l n t
  | get_bno l n (t $ s) = get_bno l n t
  | get_bno l n (Bound m) = (m-length(l),n)

(* Not a great way of identifying induction hypothesis! *)
fun could_IH x = Term.could_unify(x,hd (Thm.prems_of @{thm rcallT})) orelse
                 Term.could_unify(x,hd (Thm.prems_of @{thm rcall2T})) orelse
                 Term.could_unify(x,hd (Thm.prems_of @{thm rcall3T}))

fun IHinst tac rls = SUBGOAL (fn (Bi,i) =>
  let val bvs = bvars Bi []
      val ihs = filter could_IH (Logic.strip_assums_hyp Bi)
      val rnames = map (fn x =>
                    let val (a,b) = get_bno [] 0 x
                    in (nth bvs a, b) end) ihs
      fun try_IHs [] = no_tac
        | try_IHs ((x,y)::xs) =
            tac [((("g", 0), Position.none), x)] (nth rls (y - 1)) i ORELSE (try_IHs xs)
  in try_IHs rnames end)

fun is_rigid_prog t =
  (case (Logic.strip_assums_concl t) of
    \<^Const_>\<open>Trueprop for \<^Const_>\<open>mem _ for a _\<close>\<close> => null (Term.add_vars a [])
  | _ => false)

in

fun rcall_tac ctxt i =
  let fun tac ps rl i = Rule_Insts.res_inst_tac ctxt ps [] rl i THEN assume_tac ctxt i
  in IHinst tac @{thms rcallTs} i end
  THEN eresolve_tac ctxt @{thms rcall_lemmas} i

fun raw_step_tac ctxt prems i =
  assume_tac ctxt i ORELSE
  resolve_tac ctxt (prems @ type_rls) i ORELSE
  rcall_tac ctxt i ORELSE
  ematch_tac ctxt @{thms SubtypeE} i ORELSE
  match_tac ctxt @{thms SubtypeI} i

fun tc_step_tac ctxt prems = SUBGOAL (fn (Bi,i) =>
    if is_rigid_prog Bi then raw_step_tac ctxt prems i else no_tac)

fun typechk_tac ctxt rls i = SELECT_GOAL (REPEAT_FIRST (tc_step_tac ctxt rls)) i


(*** Clean up Correctness Condictions ***)

fun clean_ccs_tac ctxt =
  let fun tac ps rl i = Rule_Insts.eres_inst_tac ctxt ps [] rl i THEN assume_tac ctxt i in
    TRY (REPEAT_FIRST (IHinst tac @{thms hyprcallTs} ORELSE'
      eresolve_tac ctxt ([asm_rl, @{thm SubtypeE}] @ @{thms rmIHs}) ORELSE'
      hyp_subst_tac ctxt))
  end

fun gen_ccs_tac ctxt rls i =
  SELECT_GOAL (REPEAT_FIRST (tc_step_tac ctxt rls) THEN clean_ccs_tac ctxt) i

end
\<close>

method_setup typechk = \<open>
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (typechk_tac ctxt ths))
\<close>

method_setup clean_ccs = \<open>
  Scan.succeed (SIMPLE_METHOD o clean_ccs_tac)
\<close>

method_setup gen_ccs = \<open>
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (gen_ccs_tac ctxt ths))
\<close>


subsection \<open>Evaluation\<close>

named_theorems eval "evaluation rules"

ML \<open>
fun eval_tac ths =
  Subgoal.FOCUS_PREMS (fn {context = ctxt, prems, ...} =>
    let val eval_rules = Named_Theorems.get ctxt \<^named_theorems>\<open>eval\<close>
    in DEPTH_SOLVE_1 (resolve_tac ctxt (ths @ prems @ rev eval_rules) 1) end)
\<close>

method_setup eval = \<open>
  Attrib.thms >> (fn ths => fn ctxt => SIMPLE_METHOD' (CHANGED o eval_tac ths ctxt))
\<close>


lemmas eval_rls [eval] = trueV falseV pairV lamV caseVtrue caseVfalse caseVpair caseVlam

lemma applyV [eval]:
  assumes "f \<longlongrightarrow> lam x. b(x)"
    and "b(a) \<longlongrightarrow> c"
  shows "f ` a \<longlongrightarrow> c"
  unfolding apply_def by (eval assms)

lemma letV:
  assumes 1: "t \<longlongrightarrow> a"
    and 2: "f(a) \<longlongrightarrow> c"
  shows "let x be t in f(x) \<longlongrightarrow> c"
  apply (unfold let_def)
  apply (rule 1 [THEN canonical])
  apply (tactic \<open>
    REPEAT (DEPTH_SOLVE_1 (resolve_tac \<^context> (@{thms assms} @ @{thms eval_rls}) 1 ORELSE
      eresolve_tac \<^context> @{thms substitute} 1))\<close>)
  done

lemma fixV: "f(fix(f)) \<longlongrightarrow> c \<Longrightarrow> fix(f) \<longlongrightarrow> c"
  apply (unfold fix_def)
  apply (rule applyV)
   apply (rule lamV)
  apply assumption
  done

lemma letrecV:
  "h(t,\<lambda>y. letrec g x be h(x,g) in g(y)) \<longlongrightarrow> c \<Longrightarrow>  
                 letrec g x be h(x,g) in g(t) \<longlongrightarrow> c"
  apply (unfold letrec_def)
  apply (assumption | rule fixV applyV  lamV)+
  done

lemmas [eval] = letV letrecV fixV

lemma V_rls [eval]:
  "true \<longlongrightarrow> true"
  "false \<longlongrightarrow> false"
  "\<And>b c t u. \<lbrakk>b\<longlongrightarrow>true; t\<longlongrightarrow>c\<rbrakk> \<Longrightarrow> if b then t else u \<longlongrightarrow> c"
  "\<And>b c t u. \<lbrakk>b\<longlongrightarrow>false; u\<longlongrightarrow>c\<rbrakk> \<Longrightarrow> if b then t else u \<longlongrightarrow> c"
  "\<And>a b. <a,b> \<longlongrightarrow> <a,b>"
  "\<And>a b c t h. \<lbrakk>t \<longlongrightarrow> <a,b>; h(a,b) \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> split(t,h) \<longlongrightarrow> c"
  "zero \<longlongrightarrow> zero"
  "\<And>n. succ(n) \<longlongrightarrow> succ(n)"
  "\<And>c n t u. \<lbrakk>n \<longlongrightarrow> zero; t \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> ncase(n,t,u) \<longlongrightarrow> c"
  "\<And>c n t u x. \<lbrakk>n \<longlongrightarrow> succ(x); u(x) \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> ncase(n,t,u) \<longlongrightarrow> c"
  "\<And>c n t u. \<lbrakk>n \<longlongrightarrow> zero; t \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> nrec(n,t,u) \<longlongrightarrow> c"
  "\<And>c n t u x. \<lbrakk>n\<longlongrightarrow>succ(x); u(x,nrec(x,t,u))\<longlongrightarrow>c\<rbrakk> \<Longrightarrow> nrec(n,t,u)\<longlongrightarrow>c"
  "[] \<longlongrightarrow> []"
  "\<And>h t. h$t \<longlongrightarrow> h$t"
  "\<And>c l t u. \<lbrakk>l \<longlongrightarrow> []; t \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> lcase(l,t,u) \<longlongrightarrow> c"
  "\<And>c l t u x xs. \<lbrakk>l \<longlongrightarrow> x$xs; u(x,xs) \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> lcase(l,t,u) \<longlongrightarrow> c"
  "\<And>c l t u. \<lbrakk>l \<longlongrightarrow> []; t \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> lrec(l,t,u) \<longlongrightarrow> c"
  "\<And>c l t u x xs. \<lbrakk>l\<longlongrightarrow>x$xs; u(x,xs,lrec(xs,t,u))\<longlongrightarrow>c\<rbrakk> \<Longrightarrow> lrec(l,t,u)\<longlongrightarrow>c"
  unfolding data_defs by eval+


subsection \<open>Factorial\<close>

schematic_goal
  "letrec f n be ncase(n,succ(zero),\<lambda>x. nrec(n,zero,\<lambda>y g. nrec(f(x),g,\<lambda>z h. succ(h))))  
   in f(succ(succ(zero))) \<longlongrightarrow> ?a"
  by eval

schematic_goal
  "letrec f n be ncase(n,succ(zero),\<lambda>x. nrec(n,zero,\<lambda>y g. nrec(f(x),g,\<lambda>z h. succ(h))))  
   in f(succ(succ(succ(zero)))) \<longlongrightarrow> ?a"
  by eval

subsection \<open>Less Than Or Equal\<close>

schematic_goal
  "letrec f p be split(p,\<lambda>m n. ncase(m,true,\<lambda>x. ncase(n,false,\<lambda>y. f(<x,y>))))
   in f(<succ(zero), succ(zero)>) \<longlongrightarrow> ?a"
  by eval

schematic_goal
  "letrec f p be split(p,\<lambda>m n. ncase(m,true,\<lambda>x. ncase(n,false,\<lambda>y. f(<x,y>))))
   in f(<succ(zero), succ(succ(succ(succ(zero))))>) \<longlongrightarrow> ?a"
  by eval

schematic_goal
  "letrec f p be split(p,\<lambda>m n. ncase(m,true,\<lambda>x. ncase(n,false,\<lambda>y. f(<x,y>))))
   in f(<succ(succ(succ(succ(succ(zero))))), succ(succ(succ(succ(zero))))>) \<longlongrightarrow> ?a"
  by eval


subsection \<open>Reverse\<close>

schematic_goal
  "letrec id l be lcase(l,[],\<lambda>x xs. x$id(xs))  
   in id(zero$succ(zero)$[]) \<longlongrightarrow> ?a"
  by eval

schematic_goal
  "letrec rev l be lcase(l,[],\<lambda>x xs. lrec(rev(xs),x$[],\<lambda>y ys g. y$g))  
   in rev(zero$succ(zero)$(succ((lam x. x)`succ(zero)))$([])) \<longlongrightarrow> ?a"
  by eval

end
