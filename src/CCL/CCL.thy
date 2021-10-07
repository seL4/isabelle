(*  Title:      CCL/CCL.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

section \<open>Classical Computational Logic for Untyped Lambda Calculus
  with reduction to weak head-normal form\<close>

theory CCL
imports Gfp
begin

text \<open>
  Based on FOL extended with set collection, a primitive higher-order
  logic.  HOL is too strong - descriptions prevent a type of programs
  being defined which contains only executable terms.
\<close>

class prog = "term"
default_sort prog

instance "fun" :: (prog, prog) prog ..

typedecl i
instance i :: prog ..


consts
  (*** Evaluation Judgement ***)
  Eval      ::       "[i,i]\<Rightarrow>prop"          (infixl "\<longlongrightarrow>" 20)

  (*** Bisimulations for pre-order and equality ***)
  po          ::       "['a,'a]\<Rightarrow>o"           (infixl "[=" 50)

  (*** Term Formers ***)
  true        ::       "i"
  false       ::       "i"
  pair        ::       "[i,i]\<Rightarrow>i"             ("(1<_,/_>)")
  lambda      ::       "(i\<Rightarrow>i)\<Rightarrow>i"            (binder "lam " 55)
  "case"      ::       "[i,i,i,[i,i]\<Rightarrow>i,(i\<Rightarrow>i)\<Rightarrow>i]\<Rightarrow>i"
  "apply"     ::       "[i,i]\<Rightarrow>i"             (infixl "`" 56)
  bot         ::       "i"

  (******* EVALUATION SEMANTICS *******)

  (**  This is the evaluation semantics from which the axioms below were derived.  **)
  (**  It is included here just as an evaluator for FUN and has no influence on    **)
  (**  inference in the theory CCL.                                                **)

axiomatization where
  trueV:       "true \<longlongrightarrow> true" and
  falseV:      "false \<longlongrightarrow> false" and
  pairV:       "<a,b> \<longlongrightarrow> <a,b>" and
  lamV:        "\<And>b. lam x. b(x) \<longlongrightarrow> lam x. b(x)" and

  caseVtrue:   "\<lbrakk>t \<longlongrightarrow> true; d \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> case(t,d,e,f,g) \<longlongrightarrow> c" and
  caseVfalse:  "\<lbrakk>t \<longlongrightarrow> false; e \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> case(t,d,e,f,g) \<longlongrightarrow> c" and
  caseVpair:   "\<lbrakk>t \<longlongrightarrow> <a,b>; f(a,b) \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> case(t,d,e,f,g) \<longlongrightarrow> c" and
  caseVlam:    "\<And>b. \<lbrakk>t \<longlongrightarrow> lam x. b(x); g(b) \<longlongrightarrow> c\<rbrakk> \<Longrightarrow> case(t,d,e,f,g) \<longlongrightarrow> c"

  (*** Properties of evaluation: note that "t \<longlongrightarrow> c" impies that c is canonical ***)

axiomatization where
  canonical:  "\<lbrakk>t \<longlongrightarrow> c; c==true \<Longrightarrow> u\<longlongrightarrow>v;
                          c==false \<Longrightarrow> u\<longlongrightarrow>v;
                    \<And>a b. c==<a,b> \<Longrightarrow> u\<longlongrightarrow>v;
                      \<And>f. c==lam x. f(x) \<Longrightarrow> u\<longlongrightarrow>v\<rbrakk> \<Longrightarrow>
             u\<longlongrightarrow>v"

  (* Should be derivable - but probably a bitch! *)
axiomatization where
  substitute: "\<lbrakk>a==a'; t(a)\<longlongrightarrow>c(a)\<rbrakk> \<Longrightarrow> t(a')\<longlongrightarrow>c(a')"

  (************** LOGIC ***************)

  (*** Definitions used in the following rules ***)

axiomatization where
  bot_def:         "bot == (lam x. x`x)`(lam x. x`x)" and
  apply_def:     "f ` t == case(f, bot, bot, \<lambda>x y. bot, \<lambda>u. u(t))"

definition "fix" :: "(i\<Rightarrow>i)\<Rightarrow>i"
  where "fix(f) == (lam x. f(x`x))`(lam x. f(x`x))"

  (*  The pre-order ([=) is defined as a simulation, and behavioural equivalence (=) *)
  (*  as a bisimulation.  They can both be expressed as (bi)simulations up to        *)
  (*  behavioural equivalence (ie the relations PO and EQ defined below).            *)

definition SIM :: "[i,i,i set]\<Rightarrow>o"
  where
  "SIM(t,t',R) ==  (t=true \<and> t'=true) | (t=false \<and> t'=false) |
                  (\<exists>a a' b b'. t=<a,b> \<and> t'=<a',b'> \<and> <a,a'> : R \<and> <b,b'> : R) |
                  (\<exists>f f'. t=lam x. f(x) \<and> t'=lam x. f'(x) \<and> (ALL x.<f(x),f'(x)> : R))"

definition POgen :: "i set \<Rightarrow> i set"
  where "POgen(R) == {p. \<exists>t t'. p=<t,t'> \<and> (t = bot | SIM(t,t',R))}"

definition EQgen :: "i set \<Rightarrow> i set"
  where "EQgen(R) == {p. \<exists>t t'. p=<t,t'> \<and> (t = bot \<and> t' = bot | SIM(t,t',R))}"

definition PO :: "i set"
  where "PO == gfp(POgen)"

definition EQ :: "i set"
  where "EQ == gfp(EQgen)"


  (*** Rules ***)

  (** Partial Order **)

axiomatization where
  po_refl:        "a [= a" and
  po_trans:       "\<lbrakk>a [= b;  b [= c\<rbrakk> \<Longrightarrow> a [= c" and
  po_cong:        "a [= b \<Longrightarrow> f(a) [= f(b)" and

  (* Extend definition of [= to program fragments of higher type *)
  po_abstractn:   "(\<And>x. f(x) [= g(x)) \<Longrightarrow> (\<lambda>x. f(x)) [= (\<lambda>x. g(x))"

  (** Equality - equivalence axioms inherited from FOL.thy   **)
  (**          - congruence of "=" is axiomatised implicitly **)

axiomatization where
  eq_iff:         "t = t' \<longleftrightarrow> t [= t' \<and> t' [= t"

  (** Properties of canonical values given by greatest fixed point definitions **)

axiomatization where
  PO_iff:         "t [= t' \<longleftrightarrow> <t,t'> : PO" and
  EQ_iff:         "t =  t' \<longleftrightarrow> <t,t'> : EQ"

  (** Behaviour of non-canonical terms (ie case) given by the following beta-rules **)

axiomatization where
  caseBtrue:            "case(true,d,e,f,g) = d" and
  caseBfalse:          "case(false,d,e,f,g) = e" and
  caseBpair:           "case(<a,b>,d,e,f,g) = f(a,b)" and
  caseBlam:       "\<And>b. case(lam x. b(x),d,e,f,g) = g(b)" and
  caseBbot:              "case(bot,d,e,f,g) = bot"           (* strictness *)

  (** The theory is non-trivial **)
axiomatization where
  distinctness:   "\<not> lam x. b(x) = bot"

  (*** Definitions of Termination and Divergence ***)

definition Dvg :: "i \<Rightarrow> o"
  where "Dvg(t) == t = bot"

definition Trm :: "i \<Rightarrow> o"
  where "Trm(t) == \<not> Dvg(t)"

text \<open>
Would be interesting to build a similar theory for a typed programming language:
    ie.     true :: bool,      fix :: ('a\<Rightarrow>'a)\<Rightarrow>'a  etc......

This is starting to look like LCF.
What are the advantages of this approach?
        - less axiomatic
        - wfd induction / coinduction and fixed point induction available
\<close>


lemmas ccl_data_defs = apply_def fix_def

declare po_refl [simp]


subsection \<open>Congruence Rules\<close>

(*similar to AP_THM in Gordon's HOL*)
lemma fun_cong: "(f::'a\<Rightarrow>'b) = g \<Longrightarrow> f(x)=g(x)"
  by simp

(*similar to AP_TERM in Gordon's HOL and FOL's subst_context*)
lemma arg_cong: "x=y \<Longrightarrow> f(x)=f(y)"
  by simp

lemma abstractn: "(\<And>x. f(x) = g(x)) \<Longrightarrow> f = g"
  apply (simp add: eq_iff)
  apply (blast intro: po_abstractn)
  done

lemmas caseBs = caseBtrue caseBfalse caseBpair caseBlam caseBbot


subsection \<open>Termination and Divergence\<close>

lemma Trm_iff: "Trm(t) \<longleftrightarrow> \<not> t = bot"
  by (simp add: Trm_def Dvg_def)

lemma Dvg_iff: "Dvg(t) \<longleftrightarrow> t = bot"
  by (simp add: Trm_def Dvg_def)


subsection \<open>Constructors are injective\<close>

lemma eq_lemma: "\<lbrakk>x=a; y=b; x=y\<rbrakk> \<Longrightarrow> a=b"
  by simp

ML \<open>
  fun inj_rl_tac ctxt rews i =
    let
      fun mk_inj_lemmas r = [@{thm arg_cong}] RL [r RS (r RS @{thm eq_lemma})]
      val inj_lemmas = maps mk_inj_lemmas rews
    in
      CHANGED (REPEAT (assume_tac ctxt i ORELSE
        resolve_tac ctxt @{thms iffI allI conjI} i ORELSE
        eresolve_tac ctxt inj_lemmas i ORELSE
        asm_simp_tac (ctxt addsimps rews) i))
    end;
\<close>

method_setup inj_rl = \<open>
  Attrib.thms >> (fn rews => fn ctxt => SIMPLE_METHOD' (inj_rl_tac ctxt rews))
\<close>

lemma ccl_injs:
  "<a,b> = <a',b'> \<longleftrightarrow> (a=a' \<and> b=b')"
  "\<And>b b'. (lam x. b(x) = lam x. b'(x)) \<longleftrightarrow> ((ALL z. b(z)=b'(z)))"
  by (inj_rl caseBs)


lemma pair_inject: "<a,b> = <a',b'> \<Longrightarrow> (a = a' \<Longrightarrow> b = b' \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: ccl_injs)


subsection \<open>Constructors are distinct\<close>

lemma lem: "t=t' \<Longrightarrow> case(t,b,c,d,e) = case(t',b,c,d,e)"
  by simp

ML \<open>
local
  fun pairs_of _ _ [] = []
    | pairs_of f x (y::ys) = (f x y) :: (f y x) :: (pairs_of f x ys)

  fun mk_combs _ [] = []
    | mk_combs ff (x::xs) = (pairs_of ff x xs) @ mk_combs ff xs

  (* Doesn't handle binder types correctly *)
  fun saturate thy sy name =
       let fun arg_str 0 _ s = s
         | arg_str 1 a s = "(" ^ a ^ "a" ^ s ^ ")"
         | arg_str n a s = arg_str (n-1) a ("," ^ a ^ (chr((ord "a")+n-1)) ^ s)
           val T = Sign.the_const_type thy (Sign.intern_const thy sy);
           val arity = length (binder_types T)
       in sy ^ (arg_str arity name "") end

  fun mk_thm_str thy a b = "\<not> " ^ (saturate thy a "a") ^ " = " ^ (saturate thy b "b")

  val lemma = @{thm lem};
  val eq_lemma = @{thm eq_lemma};
  val distinctness = @{thm distinctness};
  fun mk_lemma (ra,rb) =
    [lemma] RL [ra RS (rb RS eq_lemma)] RL
    [distinctness RS @{thm notE}, @{thm sym} RS (distinctness RS @{thm notE})]
in
  fun mk_lemmas rls = maps mk_lemma (mk_combs pair rls)
  fun mk_dstnct_rls thy xs = mk_combs (mk_thm_str thy) xs
end
\<close>

ML \<open>
val caseB_lemmas = mk_lemmas @{thms caseBs}

val ccl_dstncts =
  let
    fun mk_raw_dstnct_thm rls s =
      Goal.prove_global \<^theory> [] [] (Syntax.read_prop_global \<^theory> s)
        (fn {context = ctxt, ...} => resolve_tac ctxt @{thms notI} 1 THEN eresolve_tac ctxt rls 1)
  in map (mk_raw_dstnct_thm caseB_lemmas)
    (mk_dstnct_rls \<^theory> ["bot","true","false","pair","lambda"]) end

fun mk_dstnct_thms ctxt defs inj_rls xs =
  let
    val thy = Proof_Context.theory_of ctxt;
    fun mk_dstnct_thm rls s =
      Goal.prove_global thy [] [] (Syntax.read_prop ctxt s)
        (fn _ =>
          rewrite_goals_tac ctxt defs THEN
          simp_tac (ctxt addsimps (rls @ inj_rls)) 1)
  in map (mk_dstnct_thm ccl_dstncts) (mk_dstnct_rls thy xs) end

fun mkall_dstnct_thms ctxt defs i_rls xss = maps (mk_dstnct_thms ctxt defs i_rls) xss

(*** Rewriting and Proving ***)

fun XH_to_I rl = rl RS @{thm iffD2}
fun XH_to_D rl = rl RS @{thm iffD1}
val XH_to_E = make_elim o XH_to_D
val XH_to_Is = map XH_to_I
val XH_to_Ds = map XH_to_D
val XH_to_Es = map XH_to_E;

ML_Thms.bind_thms ("ccl_rews", @{thms caseBs} @ @{thms ccl_injs} @ ccl_dstncts);
ML_Thms.bind_thms ("ccl_dstnctsEs", ccl_dstncts RL [@{thm notE}]);
ML_Thms.bind_thms ("ccl_injDs", XH_to_Ds @{thms ccl_injs});
\<close>

lemmas [simp] = ccl_rews
  and [elim!] = pair_inject ccl_dstnctsEs
  and [dest!] = ccl_injDs


subsection \<open>Facts from gfp Definition of \<open>[=\<close> and \<open>=\<close>\<close>

lemma XHlemma1: "\<lbrakk>A=B; a:B \<longleftrightarrow> P\<rbrakk> \<Longrightarrow> a:A \<longleftrightarrow> P"
  by simp

lemma XHlemma2: "(P(t,t') \<longleftrightarrow> Q) \<Longrightarrow> (<t,t'> : {p. \<exists>t t'. p=<t,t'> \<and>  P(t,t')} \<longleftrightarrow> Q)"
  by blast


subsection \<open>Pre-Order\<close>

lemma POgen_mono: "mono(\<lambda>X. POgen(X))"
  apply (unfold POgen_def SIM_def)
  apply (rule monoI)
  apply blast
  done

lemma POgenXH:
  "<t,t'> : POgen(R) \<longleftrightarrow> t= bot | (t=true \<and> t'=true)  | (t=false \<and> t'=false) |
           (EX a a' b b'. t=<a,b> \<and> t'=<a',b'>  \<and> <a,a'> : R \<and> <b,b'> : R) |
           (EX f f'. t=lam x. f(x) \<and> t'=lam x. f'(x) \<and> (ALL x. <f(x),f'(x)> : R))"
  apply (unfold POgen_def SIM_def)
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma poXH:
  "t [= t' \<longleftrightarrow> t=bot | (t=true \<and> t'=true) | (t=false \<and> t'=false) |
                 (EX a a' b b'. t=<a,b> \<and> t'=<a',b'>  \<and> a [= a' \<and> b [= b') |
                 (EX f f'. t=lam x. f(x) \<and> t'=lam x. f'(x) \<and> (ALL x. f(x) [= f'(x)))"
  apply (simp add: PO_iff del: ex_simps)
  apply (rule POgen_mono
    [THEN PO_def [THEN def_gfp_Tarski], THEN XHlemma1, unfolded POgen_def SIM_def])
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma po_bot: "bot [= b"
  apply (rule poXH [THEN iffD2])
  apply simp
  done

lemma bot_poleast: "a [= bot \<Longrightarrow> a=bot"
  apply (drule poXH [THEN iffD1])
  apply simp
  done

lemma po_pair: "<a,b> [= <a',b'> \<longleftrightarrow>  a [= a' \<and> b [= b'"
  apply (rule poXH [THEN iff_trans])
  apply simp
  done

lemma po_lam: "lam x. f(x) [= lam x. f'(x) \<longleftrightarrow> (ALL x. f(x) [= f'(x))"
  apply (rule poXH [THEN iff_trans])
  apply fastforce
  done

lemmas ccl_porews = po_bot po_pair po_lam

lemma case_pocong:
  assumes 1: "t [= t'"
    and 2: "a [= a'"
    and 3: "b [= b'"
    and 4: "\<And>x y. c(x,y) [= c'(x,y)"
    and 5: "\<And>u. d(u) [= d'(u)"
  shows "case(t,a,b,c,d) [= case(t',a',b',c',d')"
  apply (rule 1 [THEN po_cong, THEN po_trans])
  apply (rule 2 [THEN po_cong, THEN po_trans])
  apply (rule 3 [THEN po_cong, THEN po_trans])
  apply (rule 4 [THEN po_abstractn, THEN po_abstractn, THEN po_cong, THEN po_trans])
  apply (rule_tac f1 = "\<lambda>d. case (t',a',b',c',d)" in
    5 [THEN po_abstractn, THEN po_cong, THEN po_trans])
  apply (rule po_refl)
  done

lemma apply_pocong: "\<lbrakk>f [= f'; a [= a'\<rbrakk> \<Longrightarrow> f ` a [= f' ` a'"
  unfolding ccl_data_defs
  apply (rule case_pocong, (rule po_refl | assumption)+)
  apply (erule po_cong)
  done

lemma npo_lam_bot: "\<not> lam x. b(x) [= bot"
  apply (rule notI)
  apply (drule bot_poleast)
  apply (erule distinctness [THEN notE])
  done

lemma po_lemma: "\<lbrakk>x=a; y=b; x[=y\<rbrakk> \<Longrightarrow> a[=b"
  by simp

lemma npo_pair_lam: "\<not> <a,b> [= lam x. f(x)"
  apply (rule notI)
  apply (rule npo_lam_bot [THEN notE])
  apply (erule case_pocong [THEN caseBlam [THEN caseBpair [THEN po_lemma]]])
  apply (rule po_refl npo_lam_bot)+
  done

lemma npo_lam_pair: "\<not> lam x. f(x) [= <a,b>"
  apply (rule notI)
  apply (rule npo_lam_bot [THEN notE])
  apply (erule case_pocong [THEN caseBpair [THEN caseBlam [THEN po_lemma]]])
  apply (rule po_refl npo_lam_bot)+
  done

lemma npo_rls1:
  "\<not> true [= false"
  "\<not> false [= true"
  "\<not> true [= <a,b>"
  "\<not> <a,b> [= true"
  "\<not> true [= lam x. f(x)"
  "\<not> lam x. f(x) [= true"
  "\<not> false [= <a,b>"
  "\<not> <a,b> [= false"
  "\<not> false [= lam x. f(x)"
  "\<not> lam x. f(x) [= false"
  by (rule notI, drule case_pocong, erule_tac [5] rev_mp, simp_all,
    (rule po_refl npo_lam_bot)+)+

lemmas npo_rls = npo_pair_lam npo_lam_pair npo_rls1


subsection \<open>Coinduction for \<open>[=\<close>\<close>

lemma po_coinduct: "\<lbrakk><t,u> : R; R <= POgen(R)\<rbrakk> \<Longrightarrow> t [= u"
  apply (rule PO_def [THEN def_coinduct, THEN PO_iff [THEN iffD2]])
   apply assumption+
  done


subsection \<open>Equality\<close>

lemma EQgen_mono: "mono(\<lambda>X. EQgen(X))"
  apply (unfold EQgen_def SIM_def)
  apply (rule monoI)
  apply blast
  done

lemma EQgenXH:
  "<t,t'> : EQgen(R) \<longleftrightarrow> (t=bot \<and> t'=bot)  | (t=true \<and> t'=true)  |
                                             (t=false \<and> t'=false) |
                 (EX a a' b b'. t=<a,b> \<and> t'=<a',b'>  \<and> <a,a'> : R \<and> <b,b'> : R) |
                 (EX f f'. t=lam x. f(x) \<and> t'=lam x. f'(x) \<and> (ALL x.<f(x),f'(x)> : R))"
  apply (unfold EQgen_def SIM_def)
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma eqXH:
  "t=t' \<longleftrightarrow> (t=bot \<and> t'=bot)  | (t=true \<and> t'=true)  | (t=false \<and> t'=false) |
                     (EX a a' b b'. t=<a,b> \<and> t'=<a',b'>  \<and> a=a' \<and> b=b') |
                     (EX f f'. t=lam x. f(x) \<and> t'=lam x. f'(x) \<and> (ALL x. f(x)=f'(x)))"
  apply (subgoal_tac "<t,t'> : EQ \<longleftrightarrow>
    (t=bot \<and> t'=bot) | (t=true \<and> t'=true) | (t=false \<and> t'=false) |
    (EX a a' b b'. t=<a,b> \<and> t'=<a',b'> \<and> <a,a'> : EQ \<and> <b,b'> : EQ) |
    (EX f f'. t=lam x. f (x) \<and> t'=lam x. f' (x) \<and> (ALL x. <f (x) ,f' (x) > : EQ))")
  apply (erule rev_mp)
  apply (simp add: EQ_iff [THEN iff_sym])
  apply (rule EQgen_mono [THEN EQ_def [THEN def_gfp_Tarski], THEN XHlemma1,
    unfolded EQgen_def SIM_def])
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma eq_coinduct: "\<lbrakk><t,u> : R; R <= EQgen(R)\<rbrakk> \<Longrightarrow> t = u"
  apply (rule EQ_def [THEN def_coinduct, THEN EQ_iff [THEN iffD2]])
   apply assumption+
  done

lemma eq_coinduct3:
  "\<lbrakk><t,u> : R;  R <= EQgen(lfp(\<lambda>x. EQgen(x) Un R Un EQ))\<rbrakk> \<Longrightarrow> t = u"
  apply (rule EQ_def [THEN def_coinduct3, THEN EQ_iff [THEN iffD2]])
  apply (rule EQgen_mono | assumption)+
  done

method_setup eq_coinduct3 = \<open>
  Scan.lift Args.embedded_inner_syntax >> (fn s => fn ctxt =>
    SIMPLE_METHOD'
      (Rule_Insts.res_inst_tac ctxt [((("R", 0), Position.none), s)] [] @{thm eq_coinduct3}))
\<close>


subsection \<open>Untyped Case Analysis and Other Facts\<close>

lemma cond_eta: "(EX f. t=lam x. f(x)) \<Longrightarrow> t = lam x.(t ` x)"
  by (auto simp: apply_def)

lemma exhaustion: "(t=bot) | (t=true) | (t=false) | (EX a b. t=<a,b>) | (EX f. t=lam x. f(x))"
  apply (cut_tac refl [THEN eqXH [THEN iffD1]])
  apply blast
  done

lemma term_case:
  "\<lbrakk>P(bot); P(true); P(false); \<And>x y. P(<x,y>); \<And>b. P(lam x. b(x))\<rbrakk> \<Longrightarrow> P(t)"
  using exhaustion [of t] by blast

end
