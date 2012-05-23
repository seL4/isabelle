(*  Title:      CCL/CCL.thy
    Author:     Martin Coen
    Copyright   1993  University of Cambridge
*)

header {* Classical Computational Logic for Untyped Lambda Calculus
  with reduction to weak head-normal form *}

theory CCL
imports Gfp
begin

text {*
  Based on FOL extended with set collection, a primitive higher-order
  logic.  HOL is too strong - descriptions prevent a type of programs
  being defined which contains only executable terms.
*}

classes prog < "term"
default_sort prog

arities "fun" :: (prog, prog) prog

typedecl i
arities i :: prog


consts
  (*** Evaluation Judgement ***)
  Eval      ::       "[i,i]=>prop"          (infixl "--->" 20)

  (*** Bisimulations for pre-order and equality ***)
  po          ::       "['a,'a]=>o"           (infixl "[=" 50)
  SIM         ::       "[i,i,i set]=>o"
  POgen       ::       "i set => i set"
  EQgen       ::       "i set => i set"
  PO          ::       "i set"
  EQ          ::       "i set"

  (*** Term Formers ***)
  true        ::       "i"
  false       ::       "i"
  pair        ::       "[i,i]=>i"             ("(1<_,/_>)")
  lambda      ::       "(i=>i)=>i"            (binder "lam " 55)
  "case"      ::       "[i,i,i,[i,i]=>i,(i=>i)=>i]=>i"
  "apply"     ::       "[i,i]=>i"             (infixl "`" 56)
  bot         ::       "i"
  "fix"       ::       "(i=>i)=>i"

  (*** Defined Predicates ***)
  Trm         ::       "i => o"
  Dvg         ::       "i => o"

axioms

  (******* EVALUATION SEMANTICS *******)

  (**  This is the evaluation semantics from which the axioms below were derived.  **)
  (**  It is included here just as an evaluator for FUN and has no influence on    **)
  (**  inference in the theory CCL.                                                **)

  trueV:       "true ---> true"
  falseV:      "false ---> false"
  pairV:       "<a,b> ---> <a,b>"
  lamV:        "lam x. b(x) ---> lam x. b(x)"
  caseVtrue:   "[| t ---> true;  d ---> c |] ==> case(t,d,e,f,g) ---> c"
  caseVfalse:  "[| t ---> false;  e ---> c |] ==> case(t,d,e,f,g) ---> c"
  caseVpair:   "[| t ---> <a,b>;  f(a,b) ---> c |] ==> case(t,d,e,f,g) ---> c"
  caseVlam:    "[| t ---> lam x. b(x);  g(b) ---> c |] ==> case(t,d,e,f,g) ---> c"

  (*** Properties of evaluation: note that "t ---> c" impies that c is canonical ***)

  canonical:  "[| t ---> c; c==true ==> u--->v;
                          c==false ==> u--->v;
                    !!a b. c==<a,b> ==> u--->v;
                      !!f. c==lam x. f(x) ==> u--->v |] ==>
             u--->v"

  (* Should be derivable - but probably a bitch! *)
  substitute: "[| a==a'; t(a)--->c(a) |] ==> t(a')--->c(a')"

  (************** LOGIC ***************)

  (*** Definitions used in the following rules ***)

  apply_def:     "f ` t == case(f,bot,bot,%x y. bot,%u. u(t))"
  bot_def:         "bot == (lam x. x`x)`(lam x. x`x)"

defs
  fix_def:      "fix(f) == (lam x. f(x`x))`(lam x. f(x`x))"

  (*  The pre-order ([=) is defined as a simulation, and behavioural equivalence (=) *)
  (*  as a bisimulation.  They can both be expressed as (bi)simulations up to        *)
  (*  behavioural equivalence (ie the relations PO and EQ defined below).            *)

  SIM_def:
  "SIM(t,t',R) ==  (t=true & t'=true) | (t=false & t'=false) |
                  (EX a a' b b'. t=<a,b> & t'=<a',b'> & <a,a'> : R & <b,b'> : R) |
                  (EX f f'. t=lam x. f(x) & t'=lam x. f'(x) & (ALL x.<f(x),f'(x)> : R))"

  POgen_def:  "POgen(R) == {p. EX t t'. p=<t,t'> & (t = bot | SIM(t,t',R))}"
  EQgen_def:  "EQgen(R) == {p. EX t t'. p=<t,t'> & (t = bot & t' = bot | SIM(t,t',R))}"

  PO_def:    "PO == gfp(POgen)"
  EQ_def:    "EQ == gfp(EQgen)"

  (*** Rules ***)

  (** Partial Order **)

axioms
  po_refl:        "a [= a"
  po_trans:       "[| a [= b;  b [= c |] ==> a [= c"
  po_cong:        "a [= b ==> f(a) [= f(b)"

  (* Extend definition of [= to program fragments of higher type *)
  po_abstractn:   "(!!x. f(x) [= g(x)) ==> (%x. f(x)) [= (%x. g(x))"

  (** Equality - equivalence axioms inherited from FOL.thy   **)
  (**          - congruence of "=" is axiomatised implicitly **)

  eq_iff:         "t = t' <-> t [= t' & t' [= t"

  (** Properties of canonical values given by greatest fixed point definitions **)

  PO_iff:         "t [= t' <-> <t,t'> : PO"
  EQ_iff:         "t =  t' <-> <t,t'> : EQ"

  (** Behaviour of non-canonical terms (ie case) given by the following beta-rules **)

  caseBtrue:            "case(true,d,e,f,g) = d"
  caseBfalse:          "case(false,d,e,f,g) = e"
  caseBpair:           "case(<a,b>,d,e,f,g) = f(a,b)"
  caseBlam:       "case(lam x. b(x),d,e,f,g) = g(b)"
  caseBbot:              "case(bot,d,e,f,g) = bot"            (* strictness *)

  (** The theory is non-trivial **)
  distinctness:   "~ lam x. b(x) = bot"

  (*** Definitions of Termination and Divergence ***)

defs
  Dvg_def:  "Dvg(t) == t = bot"
  Trm_def:  "Trm(t) == ~ Dvg(t)"

text {*
Would be interesting to build a similar theory for a typed programming language:
    ie.     true :: bool,      fix :: ('a=>'a)=>'a  etc......

This is starting to look like LCF.
What are the advantages of this approach?
        - less axiomatic
        - wfd induction / coinduction and fixed point induction available
*}


lemmas ccl_data_defs = apply_def fix_def

declare po_refl [simp]


subsection {* Congruence Rules *}

(*similar to AP_THM in Gordon's HOL*)
lemma fun_cong: "(f::'a=>'b) = g ==> f(x)=g(x)"
  by simp

(*similar to AP_TERM in Gordon's HOL and FOL's subst_context*)
lemma arg_cong: "x=y ==> f(x)=f(y)"
  by simp

lemma abstractn: "(!!x. f(x) = g(x)) ==> f = g"
  apply (simp add: eq_iff)
  apply (blast intro: po_abstractn)
  done

lemmas caseBs = caseBtrue caseBfalse caseBpair caseBlam caseBbot


subsection {* Termination and Divergence *}

lemma Trm_iff: "Trm(t) <-> ~ t = bot"
  by (simp add: Trm_def Dvg_def)

lemma Dvg_iff: "Dvg(t) <-> t = bot"
  by (simp add: Trm_def Dvg_def)


subsection {* Constructors are injective *}

lemma eq_lemma: "[| x=a;  y=b;  x=y |] ==> a=b"
  by simp

ML {*
  fun inj_rl_tac ctxt rews i =
    let
      fun mk_inj_lemmas r = [@{thm arg_cong}] RL [r RS (r RS @{thm eq_lemma})]
      val inj_lemmas = maps mk_inj_lemmas rews
    in
      CHANGED (REPEAT (ares_tac [@{thm iffI}, @{thm allI}, @{thm conjI}] i ORELSE
        eresolve_tac inj_lemmas i ORELSE
        asm_simp_tac (simpset_of ctxt addsimps rews) i))
    end;
*}

method_setup inj_rl = {*
  Attrib.thms >> (fn rews => fn ctxt => SIMPLE_METHOD' (inj_rl_tac ctxt rews))
*}

lemma ccl_injs:
  "<a,b> = <a',b'> <-> (a=a' & b=b')"
  "!!b b'. (lam x. b(x) = lam x. b'(x)) <-> ((ALL z. b(z)=b'(z)))"
  by (inj_rl caseBs)


lemma pair_inject: "<a,b> = <a',b'> \<Longrightarrow> (a = a' \<Longrightarrow> b = b' \<Longrightarrow> R) \<Longrightarrow> R"
  by (simp add: ccl_injs)


subsection {* Constructors are distinct *}

lemma lem: "t=t' ==> case(t,b,c,d,e) = case(t',b,c,d,e)"
  by simp

ML {*

local
  fun pairs_of f x [] = []
    | pairs_of f x (y::ys) = (f x y) :: (f y x) :: (pairs_of f x ys)

  fun mk_combs ff [] = []
    | mk_combs ff (x::xs) = (pairs_of ff x xs) @ mk_combs ff xs

  (* Doesn't handle binder types correctly *)
  fun saturate thy sy name =
       let fun arg_str 0 a s = s
         | arg_str 1 a s = "(" ^ a ^ "a" ^ s ^ ")"
         | arg_str n a s = arg_str (n-1) a ("," ^ a ^ (chr((ord "a")+n-1)) ^ s)
           val T = Sign.the_const_type thy (Sign.intern_const thy sy);
           val arity = length (binder_types T)
       in sy ^ (arg_str arity name "") end

  fun mk_thm_str thy a b = "~ " ^ (saturate thy a "a") ^ " = " ^ (saturate thy b "b")

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

*}

ML {*

val caseB_lemmas = mk_lemmas @{thms caseBs}

val ccl_dstncts =
  let
    fun mk_raw_dstnct_thm rls s =
      Goal.prove_global @{theory} [] [] (Syntax.read_prop_global @{theory} s)
        (fn _=> rtac @{thm notI} 1 THEN eresolve_tac rls 1)
  in map (mk_raw_dstnct_thm caseB_lemmas)
    (mk_dstnct_rls @{theory} ["bot","true","false","pair","lambda"]) end

fun mk_dstnct_thms thy defs inj_rls xs =
  let
    fun mk_dstnct_thm rls s =
      Goal.prove_global thy [] [] (Syntax.read_prop_global thy s)
        (fn _ =>
          rewrite_goals_tac defs THEN
          simp_tac (global_simpset_of thy addsimps (rls @ inj_rls)) 1)
  in map (mk_dstnct_thm ccl_dstncts) (mk_dstnct_rls thy xs) end

fun mkall_dstnct_thms thy defs i_rls xss = maps (mk_dstnct_thms thy defs i_rls) xss

(*** Rewriting and Proving ***)

fun XH_to_I rl = rl RS @{thm iffD2}
fun XH_to_D rl = rl RS @{thm iffD1}
val XH_to_E = make_elim o XH_to_D
val XH_to_Is = map XH_to_I
val XH_to_Ds = map XH_to_D
val XH_to_Es = map XH_to_E;

bind_thms ("ccl_rews", @{thms caseBs} @ @{thms ccl_injs} @ ccl_dstncts);
bind_thms ("ccl_dstnctsEs", ccl_dstncts RL [@{thm notE}]);
bind_thms ("ccl_injDs", XH_to_Ds @{thms ccl_injs});
*}

lemmas [simp] = ccl_rews
  and [elim!] = pair_inject ccl_dstnctsEs
  and [dest!] = ccl_injDs


subsection {* Facts from gfp Definition of @{text "[="} and @{text "="} *}

lemma XHlemma1: "[| A=B;  a:B <-> P |] ==> a:A <-> P"
  by simp

lemma XHlemma2: "(P(t,t') <-> Q) ==> (<t,t'> : {p. EX t t'. p=<t,t'> &  P(t,t')} <-> Q)"
  by blast


subsection {* Pre-Order *}

lemma POgen_mono: "mono(%X. POgen(X))"
  apply (unfold POgen_def SIM_def)
  apply (rule monoI)
  apply blast
  done

lemma POgenXH: 
  "<t,t'> : POgen(R) <-> t= bot | (t=true & t'=true)  | (t=false & t'=false) |  
           (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & <a,a'> : R & <b,b'> : R) |  
           (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. <f(x),f'(x)> : R))"
  apply (unfold POgen_def SIM_def)
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma poXH: 
  "t [= t' <-> t=bot | (t=true & t'=true) | (t=false & t'=false) |  
                 (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & a [= a' & b [= b') |  
                 (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. f(x) [= f'(x)))"
  apply (simp add: PO_iff del: ex_simps)
  apply (rule POgen_mono
    [THEN PO_def [THEN def_gfp_Tarski], THEN XHlemma1, unfolded POgen_def SIM_def])
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma po_bot: "bot [= b"
  apply (rule poXH [THEN iffD2])
  apply simp
  done

lemma bot_poleast: "a [= bot ==> a=bot"
  apply (drule poXH [THEN iffD1])
  apply simp
  done

lemma po_pair: "<a,b> [= <a',b'> <->  a [= a' & b [= b'"
  apply (rule poXH [THEN iff_trans])
  apply simp
  done

lemma po_lam: "lam x. f(x) [= lam x. f'(x) <-> (ALL x. f(x) [= f'(x))"
  apply (rule poXH [THEN iff_trans])
  apply fastforce
  done

lemmas ccl_porews = po_bot po_pair po_lam

lemma case_pocong:
  assumes 1: "t [= t'"
    and 2: "a [= a'"
    and 3: "b [= b'"
    and 4: "!!x y. c(x,y) [= c'(x,y)"
    and 5: "!!u. d(u) [= d'(u)"
  shows "case(t,a,b,c,d) [= case(t',a',b',c',d')"
  apply (rule 1 [THEN po_cong, THEN po_trans])
  apply (rule 2 [THEN po_cong, THEN po_trans])
  apply (rule 3 [THEN po_cong, THEN po_trans])
  apply (rule 4 [THEN po_abstractn, THEN po_abstractn, THEN po_cong, THEN po_trans])
  apply (rule_tac f1 = "%d. case (t',a',b',c',d)" in
    5 [THEN po_abstractn, THEN po_cong, THEN po_trans])
  apply (rule po_refl)
  done

lemma apply_pocong: "[| f [= f';  a [= a' |] ==> f ` a [= f' ` a'"
  unfolding ccl_data_defs
  apply (rule case_pocong, (rule po_refl | assumption)+)
  apply (erule po_cong)
  done

lemma npo_lam_bot: "~ lam x. b(x) [= bot"
  apply (rule notI)
  apply (drule bot_poleast)
  apply (erule distinctness [THEN notE])
  done

lemma po_lemma: "[| x=a;  y=b;  x[=y |] ==> a[=b"
  by simp

lemma npo_pair_lam: "~ <a,b> [= lam x. f(x)"
  apply (rule notI)
  apply (rule npo_lam_bot [THEN notE])
  apply (erule case_pocong [THEN caseBlam [THEN caseBpair [THEN po_lemma]]])
  apply (rule po_refl npo_lam_bot)+
  done

lemma npo_lam_pair: "~ lam x. f(x) [= <a,b>"
  apply (rule notI)
  apply (rule npo_lam_bot [THEN notE])
  apply (erule case_pocong [THEN caseBpair [THEN caseBlam [THEN po_lemma]]])
  apply (rule po_refl npo_lam_bot)+
  done

lemma npo_rls1:
  "~ true [= false"
  "~ false [= true"
  "~ true [= <a,b>"
  "~ <a,b> [= true"
  "~ true [= lam x. f(x)"
  "~ lam x. f(x) [= true"
  "~ false [= <a,b>"
  "~ <a,b> [= false"
  "~ false [= lam x. f(x)"
  "~ lam x. f(x) [= false"
  by (tactic {*
    REPEAT (rtac @{thm notI} 1 THEN
      dtac @{thm case_pocong} 1 THEN
      etac @{thm rev_mp} 5 THEN
      ALLGOALS (simp_tac @{simpset}) THEN
      REPEAT (resolve_tac [@{thm po_refl}, @{thm npo_lam_bot}] 1)) *})

lemmas npo_rls = npo_pair_lam npo_lam_pair npo_rls1


subsection {* Coinduction for @{text "[="} *}

lemma po_coinduct: "[|  <t,u> : R;  R <= POgen(R) |] ==> t [= u"
  apply (rule PO_def [THEN def_coinduct, THEN PO_iff [THEN iffD2]])
   apply assumption+
  done


subsection {* Equality *}

lemma EQgen_mono: "mono(%X. EQgen(X))"
  apply (unfold EQgen_def SIM_def)
  apply (rule monoI)
  apply blast
  done

lemma EQgenXH: 
  "<t,t'> : EQgen(R) <-> (t=bot & t'=bot)  | (t=true & t'=true)  |  
                                             (t=false & t'=false) |  
                 (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & <a,a'> : R & <b,b'> : R) |  
                 (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x.<f(x),f'(x)> : R))"
  apply (unfold EQgen_def SIM_def)
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma eqXH: 
  "t=t' <-> (t=bot & t'=bot)  | (t=true & t'=true)  | (t=false & t'=false) |  
                     (EX a a' b b'. t=<a,b> &  t'=<a',b'>  & a=a' & b=b') |  
                     (EX f f'. t=lam x. f(x) &  t'=lam x. f'(x) & (ALL x. f(x)=f'(x)))"
  apply (subgoal_tac "<t,t'> : EQ <-> (t=bot & t'=bot) | (t=true & t'=true) | (t=false & t'=false) | (EX a a' b b'. t=<a,b> & t'=<a',b'> & <a,a'> : EQ & <b,b'> : EQ) | (EX f f'. t=lam x. f (x) & t'=lam x. f' (x) & (ALL x. <f (x) ,f' (x) > : EQ))")
  apply (erule rev_mp)
  apply (simp add: EQ_iff [THEN iff_sym])
  apply (rule EQgen_mono [THEN EQ_def [THEN def_gfp_Tarski], THEN XHlemma1,
    unfolded EQgen_def SIM_def])
  apply (rule iff_refl [THEN XHlemma2])
  done

lemma eq_coinduct: "[|  <t,u> : R;  R <= EQgen(R) |] ==> t = u"
  apply (rule EQ_def [THEN def_coinduct, THEN EQ_iff [THEN iffD2]])
   apply assumption+
  done

lemma eq_coinduct3:
  "[|  <t,u> : R;  R <= EQgen(lfp(%x. EQgen(x) Un R Un EQ)) |] ==> t = u"
  apply (rule EQ_def [THEN def_coinduct3, THEN EQ_iff [THEN iffD2]])
  apply (rule EQgen_mono | assumption)+
  done

ML {*
  fun eq_coinduct_tac ctxt s i = res_inst_tac ctxt [(("R", 0), s)] @{thm eq_coinduct} i
  fun eq_coinduct3_tac ctxt s i = res_inst_tac ctxt [(("R", 0), s)] @{thm eq_coinduct3} i
*}


subsection {* Untyped Case Analysis and Other Facts *}

lemma cond_eta: "(EX f. t=lam x. f(x)) ==> t = lam x.(t ` x)"
  by (auto simp: apply_def)

lemma exhaustion: "(t=bot) | (t=true) | (t=false) | (EX a b. t=<a,b>) | (EX f. t=lam x. f(x))"
  apply (cut_tac refl [THEN eqXH [THEN iffD1]])
  apply blast
  done

lemma term_case:
  "[| P(bot);  P(true);  P(false);  !!x y. P(<x,y>);  !!b. P(lam x. b(x)) |] ==> P(t)"
  using exhaustion [of t] by blast

end
