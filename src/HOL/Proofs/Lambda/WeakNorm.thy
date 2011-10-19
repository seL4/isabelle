(*  Title:      HOL/Proofs/Lambda/WeakNorm.thy
    Author:     Stefan Berghofer
    Copyright   2003 TU Muenchen
*)

header {* Weak normalization for simply-typed lambda calculus *}

theory WeakNorm
imports Type NormalForm "~~/src/HOL/Library/Code_Integer"
begin

text {*
Formalization by Stefan Berghofer. Partly based on a paper proof by
Felix Joachimski and Ralph Matthes \cite{Matthes-Joachimski-AML}.
*}


subsection {* Main theorems *}

lemma norm_list:
  assumes f_compat: "\<And>t t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<Longrightarrow> f t \<rightarrow>\<^sub>\<beta>\<^sup>* f t'"
  and f_NF: "\<And>t. NF t \<Longrightarrow> NF (f t)"
  and uNF: "NF u" and uT: "e \<turnstile> u : T"
  shows "\<And>Us. e\<langle>i:T\<rangle> \<tturnstile> as : Us \<Longrightarrow>
    listall (\<lambda>t. \<forall>e T' u i. e\<langle>i:T\<rangle> \<turnstile> t : T' \<longrightarrow>
      NF u \<longrightarrow> e \<turnstile> u : T \<longrightarrow> (\<exists>t'. t[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t')) as \<Longrightarrow>
    \<exists>as'. \<forall>j. Var j \<degree>\<degree> map (\<lambda>t. f (t[u/i])) as \<rightarrow>\<^sub>\<beta>\<^sup>*
      Var j \<degree>\<degree> map f as' \<and> NF (Var j \<degree>\<degree> map f as')"
  (is "\<And>Us. _ \<Longrightarrow> listall ?R as \<Longrightarrow> \<exists>as'. ?ex Us as as'")
proof (induct as rule: rev_induct)
  case (Nil Us)
  with Var_NF have "?ex Us [] []" by simp
  thus ?case ..
next
  case (snoc b bs Us)
  have "e\<langle>i:T\<rangle> \<tturnstile> bs  @ [b] : Us" by fact
  then obtain Vs W where Us: "Us = Vs @ [W]"
    and bs: "e\<langle>i:T\<rangle> \<tturnstile> bs : Vs" and bT: "e\<langle>i:T\<rangle> \<turnstile> b : W"
    by (rule types_snocE)
  from snoc have "listall ?R bs" by simp
  with bs have "\<exists>bs'. ?ex Vs bs bs'" by (rule snoc)
  then obtain bs' where
    bsred: "\<And>j. Var j \<degree>\<degree> map (\<lambda>t. f (t[u/i])) bs \<rightarrow>\<^sub>\<beta>\<^sup>* Var j \<degree>\<degree> map f bs'"
    and bsNF: "\<And>j. NF (Var j \<degree>\<degree> map f bs')" by iprover
  from snoc have "?R b" by simp
  with bT and uNF and uT have "\<exists>b'. b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* b' \<and> NF b'"
    by iprover
  then obtain b' where bred: "b[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* b'" and bNF: "NF b'"
    by iprover
  from bsNF [of 0] have "listall NF (map f bs')"
    by (rule App_NF_D)
  moreover have "NF (f b')" using bNF by (rule f_NF)
  ultimately have "listall NF (map f (bs' @ [b']))"
    by simp
  hence "\<And>j. NF (Var j \<degree>\<degree> map f (bs' @ [b']))" by (rule NF.App)
  moreover from bred have "f (b[u/i]) \<rightarrow>\<^sub>\<beta>\<^sup>* f b'"
    by (rule f_compat)
  with bsred have
    "\<And>j. (Var j \<degree>\<degree> map (\<lambda>t. f (t[u/i])) bs) \<degree> f (b[u/i]) \<rightarrow>\<^sub>\<beta>\<^sup>*
     (Var j \<degree>\<degree> map f bs') \<degree> f b'" by (rule rtrancl_beta_App)
  ultimately have "?ex Us (bs @ [b]) (bs' @ [b'])" by simp
  thus ?case ..
qed

lemma subst_type_NF:
  "\<And>t e T u i. NF t \<Longrightarrow> e\<langle>i:U\<rangle> \<turnstile> t : T \<Longrightarrow> NF u \<Longrightarrow> e \<turnstile> u : U \<Longrightarrow> \<exists>t'. t[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'"
  (is "PROP ?P U" is "\<And>t e T u i. _ \<Longrightarrow> PROP ?Q t e T u i U")
proof (induct U)
  fix T t
  let ?R = "\<lambda>t. \<forall>e T' u i.
    e\<langle>i:T\<rangle> \<turnstile> t : T' \<longrightarrow> NF u \<longrightarrow> e \<turnstile> u : T \<longrightarrow> (\<exists>t'. t[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t')"
  assume MI1: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T1"
  assume MI2: "\<And>T1 T2. T = T1 \<Rightarrow> T2 \<Longrightarrow> PROP ?P T2"
  assume "NF t"
  thus "\<And>e T' u i. PROP ?Q t e T' u i T"
  proof induct
    fix e T' u i assume uNF: "NF u" and uT: "e \<turnstile> u : T"
    {
      case (App ts x e_ T'_ u_ i_)
      assume "e\<langle>i:T\<rangle> \<turnstile> Var x \<degree>\<degree> ts : T'"
      then obtain Us
        where varT: "e\<langle>i:T\<rangle> \<turnstile> Var x : Us \<Rrightarrow> T'"
        and argsT: "e\<langle>i:T\<rangle> \<tturnstile> ts : Us"
        by (rule var_app_typesE)
      from nat_eq_dec show "\<exists>t'. (Var x \<degree>\<degree> ts)[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'"
      proof
        assume eq: "x = i"
        show ?thesis
        proof (cases ts)
          case Nil
          with eq have "(Var x \<degree>\<degree> [])[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* u" by simp
          with Nil and uNF show ?thesis by simp iprover
        next
          case (Cons a as)
          with argsT obtain T'' Ts where Us: "Us = T'' # Ts"
            by (cases Us) (rule FalseE, simp+, erule that)
          from varT and Us have varT: "e\<langle>i:T\<rangle> \<turnstile> Var x : T'' \<Rightarrow> Ts \<Rrightarrow> T'"
            by simp
          from varT eq have T: "T = T'' \<Rightarrow> Ts \<Rrightarrow> T'" by cases auto
          with uT have uT': "e \<turnstile> u : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by simp
          from argsT Us Cons have argsT': "e\<langle>i:T\<rangle> \<tturnstile> as : Ts" by simp
          from argsT Us Cons have argT: "e\<langle>i:T\<rangle> \<turnstile> a : T''" by simp
          from argT uT refl have aT: "e \<turnstile> a[u/i] : T''" by (rule subst_lemma)
          from App and Cons have "listall ?R as" by simp (iprover dest: listall_conj2)
          with lift_preserves_beta' lift_NF uNF uT argsT'
          have "\<exists>as'. \<forall>j. Var j \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as \<rightarrow>\<^sub>\<beta>\<^sup>*
            Var j \<degree>\<degree> map (\<lambda>t. lift t 0) as' \<and>
            NF (Var j \<degree>\<degree> map (\<lambda>t. lift t 0) as')" by (rule norm_list)
          then obtain as' where
            asred: "Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as \<rightarrow>\<^sub>\<beta>\<^sup>*
              Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as'"
            and asNF: "NF (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')" by iprover
          from App and Cons have "?R a" by simp
          with argT and uNF and uT have "\<exists>a'. a[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* a' \<and> NF a'"
            by iprover
          then obtain a' where ared: "a[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* a'" and aNF: "NF a'" by iprover
          from uNF have "NF (lift u 0)" by (rule lift_NF)
          hence "\<exists>u'. lift u 0 \<degree> Var 0 \<rightarrow>\<^sub>\<beta>\<^sup>* u' \<and> NF u'" by (rule app_Var_NF)
          then obtain u' where ured: "lift u 0 \<degree> Var 0 \<rightarrow>\<^sub>\<beta>\<^sup>* u'" and u'NF: "NF u'"
            by iprover
          from T and u'NF have "\<exists>ua. u'[a'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* ua \<and> NF ua"
          proof (rule MI1)
            have "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 \<degree> Var 0 : Ts \<Rrightarrow> T'"
            proof (rule typing.App)
              from uT' show "e\<langle>0:T''\<rangle> \<turnstile> lift u 0 : T'' \<Rightarrow> Ts \<Rrightarrow> T'" by (rule lift_type)
              show "e\<langle>0:T''\<rangle> \<turnstile> Var 0 : T''" by (rule typing.Var) simp
            qed
            with ured show "e\<langle>0:T''\<rangle> \<turnstile> u' : Ts \<Rrightarrow> T'" by (rule subject_reduction')
            from ared aT show "e \<turnstile> a' : T''" by (rule subject_reduction')
            show "NF a'" by fact
          qed
          then obtain ua where uared: "u'[a'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* ua" and uaNF: "NF ua"
            by iprover
          from ared have "(lift u 0 \<degree> Var 0)[a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>* (lift u 0 \<degree> Var 0)[a'/0]"
            by (rule subst_preserves_beta2')
          also from ured have "(lift u 0 \<degree> Var 0)[a'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* u'[a'/0]"
            by (rule subst_preserves_beta')
          also note uared
          finally have "(lift u 0 \<degree> Var 0)[a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>* ua" .
          hence uared': "u \<degree> a[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* ua" by simp
          from T asNF _ uaNF have "\<exists>r. (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[ua/0] \<rightarrow>\<^sub>\<beta>\<^sup>* r \<and> NF r"
          proof (rule MI2)
            have "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as : T'"
            proof (rule list_app_typeI)
              show "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 : Ts \<Rrightarrow> T'" by (rule typing.Var) simp
              from uT argsT' have "e \<tturnstile> map (\<lambda>t. t[u/i]) as : Ts"
                by (rule substs_lemma)
              hence "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<tturnstile> map (\<lambda>t. lift t 0) (map (\<lambda>t. t[u/i]) as) : Ts"
                by (rule lift_types)
              thus "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<tturnstile> map (\<lambda>t. lift (t[u/i]) 0) as : Ts"
                by (simp_all add: o_def)
            qed
            with asred show "e\<langle>0:Ts \<Rrightarrow> T'\<rangle> \<turnstile> Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as' : T'"
              by (rule subject_reduction')
            from argT uT refl have "e \<turnstile> a[u/i] : T''" by (rule subst_lemma)
            with uT' have "e \<turnstile> u \<degree> a[u/i] : Ts \<Rrightarrow> T'" by (rule typing.App)
            with uared' show "e \<turnstile> ua : Ts \<Rrightarrow> T'" by (rule subject_reduction')
          qed
          then obtain r where rred: "(Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[ua/0] \<rightarrow>\<^sub>\<beta>\<^sup>* r"
            and rnf: "NF r" by iprover
          from asred have
            "(Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as)[u \<degree> a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>*
            (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[u \<degree> a[u/i]/0]"
            by (rule subst_preserves_beta')
          also from uared' have "(Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[u \<degree> a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>*
            (Var 0 \<degree>\<degree> map (\<lambda>t. lift t 0) as')[ua/0]" by (rule subst_preserves_beta2')
          also note rred
          finally have "(Var 0 \<degree>\<degree> map (\<lambda>t. lift (t[u/i]) 0) as)[u \<degree> a[u/i]/0] \<rightarrow>\<^sub>\<beta>\<^sup>* r" .
          with rnf Cons eq show ?thesis
            by (simp add: o_def) iprover
        qed
      next
        assume neq: "x \<noteq> i"
        from App have "listall ?R ts" by (iprover dest: listall_conj2)
        with TrueI TrueI uNF uT argsT
        have "\<exists>ts'. \<forall>j. Var j \<degree>\<degree> map (\<lambda>t. t[u/i]) ts \<rightarrow>\<^sub>\<beta>\<^sup>* Var j \<degree>\<degree> ts' \<and>
          NF (Var j \<degree>\<degree> ts')" (is "\<exists>ts'. ?ex ts'")
          by (rule norm_list [of "\<lambda>t. t", simplified])
        then obtain ts' where NF: "?ex ts'" ..
        from nat_le_dec show ?thesis
        proof
          assume "i < x"
          with NF show ?thesis by simp iprover
        next
          assume "\<not> (i < x)"
          with NF neq show ?thesis by (simp add: subst_Var) iprover
        qed
      qed
    next
      case (Abs r e_ T'_ u_ i_)
      assume absT: "e\<langle>i:T\<rangle> \<turnstile> Abs r : T'"
      then obtain R S where "e\<langle>0:R\<rangle>\<langle>Suc i:T\<rangle>  \<turnstile> r : S" by (rule abs_typeE) simp
      moreover have "NF (lift u 0)" using `NF u` by (rule lift_NF)
      moreover have "e\<langle>0:R\<rangle> \<turnstile> lift u 0 : T" using uT by (rule lift_type)
      ultimately have "\<exists>t'. r[lift u 0/Suc i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'" by (rule Abs)
      thus "\<exists>t'. Abs r[u/i] \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'"
        by simp (iprover intro: rtrancl_beta_Abs NF.Abs)
    }
  qed
qed


-- {* A computationally relevant copy of @{term "e \<turnstile> t : T"} *}
inductive rtyping :: "(nat \<Rightarrow> type) \<Rightarrow> dB \<Rightarrow> type \<Rightarrow> bool"  ("_ \<turnstile>\<^sub>R _ : _" [50, 50, 50] 50)
  where
    Var: "e x = T \<Longrightarrow> e \<turnstile>\<^sub>R Var x : T"
  | Abs: "e\<langle>0:T\<rangle> \<turnstile>\<^sub>R t : U \<Longrightarrow> e \<turnstile>\<^sub>R Abs t : (T \<Rightarrow> U)"
  | App: "e \<turnstile>\<^sub>R s : T \<Rightarrow> U \<Longrightarrow> e \<turnstile>\<^sub>R t : T \<Longrightarrow> e \<turnstile>\<^sub>R (s \<degree> t) : U"

lemma rtyping_imp_typing: "e \<turnstile>\<^sub>R t : T \<Longrightarrow> e \<turnstile> t : T"
  apply (induct set: rtyping)
  apply (erule typing.Var)
  apply (erule typing.Abs)
  apply (erule typing.App)
  apply assumption
  done


theorem type_NF:
  assumes "e \<turnstile>\<^sub>R t : T"
  shows "\<exists>t'. t \<rightarrow>\<^sub>\<beta>\<^sup>* t' \<and> NF t'" using assms
proof induct
  case Var
  show ?case by (iprover intro: Var_NF)
next
  case Abs
  thus ?case by (iprover intro: rtrancl_beta_Abs NF.Abs)
next
  case (App e s T U t)
  from App obtain s' t' where
    sred: "s \<rightarrow>\<^sub>\<beta>\<^sup>* s'" and "NF s'"
    and tred: "t \<rightarrow>\<^sub>\<beta>\<^sup>* t'" and tNF: "NF t'" by iprover
  have "\<exists>u. (Var 0 \<degree> lift t' 0)[s'/0] \<rightarrow>\<^sub>\<beta>\<^sup>* u \<and> NF u"
  proof (rule subst_type_NF)
    have "NF (lift t' 0)" using tNF by (rule lift_NF)
    hence "listall NF [lift t' 0]" by (rule listall_cons) (rule listall_nil)
    hence "NF (Var 0 \<degree>\<degree> [lift t' 0])" by (rule NF.App)
    thus "NF (Var 0 \<degree> lift t' 0)" by simp
    show "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 \<degree> lift t' 0 : U"
    proof (rule typing.App)
      show "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> Var 0 : T \<Rightarrow> U"
        by (rule typing.Var) simp
      from tred have "e \<turnstile> t' : T"
        by (rule subject_reduction') (rule rtyping_imp_typing, rule App.hyps)
      thus "e\<langle>0:T \<Rightarrow> U\<rangle> \<turnstile> lift t' 0 : T"
        by (rule lift_type)
    qed
    from sred show "e \<turnstile> s' : T \<Rightarrow> U"
      by (rule subject_reduction') (rule rtyping_imp_typing, rule App.hyps)
    show "NF s'" by fact
  qed
  then obtain u where ured: "s' \<degree> t' \<rightarrow>\<^sub>\<beta>\<^sup>* u" and unf: "NF u" by simp iprover
  from sred tred have "s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* s' \<degree> t'" by (rule rtrancl_beta_App)
  hence "s \<degree> t \<rightarrow>\<^sub>\<beta>\<^sup>* u" using ured by (rule rtranclp_trans)
  with unf show ?case by iprover
qed


subsection {* Extracting the program *}

declare NF.induct [ind_realizer]
declare rtranclp.induct [ind_realizer irrelevant]
declare rtyping.induct [ind_realizer]
lemmas [extraction_expand] = conj_assoc listall_cons_eq

extract type_NF

lemma rtranclR_rtrancl_eq: "rtranclpR r a b = r\<^sup>*\<^sup>* a b"
  apply (rule iffI)
  apply (erule rtranclpR.induct)
  apply (rule rtranclp.rtrancl_refl)
  apply (erule rtranclp.rtrancl_into_rtrancl)
  apply assumption
  apply (erule rtranclp.induct)
  apply (rule rtranclpR.rtrancl_refl)
  apply (erule rtranclpR.rtrancl_into_rtrancl)
  apply assumption
  done

lemma NFR_imp_NF: "NFR nf t \<Longrightarrow> NF t"
  apply (erule NFR.induct)
  apply (rule NF.intros)
  apply (simp add: listall_def)
  apply (erule NF.intros)
  done

text_raw {*
\begin{figure}
\renewcommand{\isastyle}{\scriptsize\it}%
@{thm [display,eta_contract=false,margin=100] subst_type_NF_def}
\renewcommand{\isastyle}{\small\it}%
\caption{Program extracted from @{text subst_type_NF}}
\label{fig:extr-subst-type-nf}
\end{figure}

\begin{figure}
\renewcommand{\isastyle}{\scriptsize\it}%
@{thm [display,margin=100] subst_Var_NF_def}
@{thm [display,margin=100] app_Var_NF_def}
@{thm [display,margin=100] lift_NF_def}
@{thm [display,eta_contract=false,margin=100] type_NF_def}
\renewcommand{\isastyle}{\small\it}%
\caption{Program extracted from lemmas and main theorem}
\label{fig:extr-type-nf}
\end{figure}
*}

text {*
The program corresponding to the proof of the central lemma, which
performs substitution and normalization, is shown in Figure
\ref{fig:extr-subst-type-nf}. The correctness
theorem corresponding to the program @{text "subst_type_NF"} is
@{thm [display,margin=100] subst_type_NF_correctness
  [simplified rtranclR_rtrancl_eq Collect_mem_eq, no_vars]}
where @{text NFR} is the realizability predicate corresponding to
the datatype @{text NFT}, which is inductively defined by the rules
\pagebreak
@{thm [display,margin=90] NFR.App [of ts nfs x] NFR.Abs [of nf t]}

The programs corresponding to the main theorem @{text "type_NF"}, as
well as to some lemmas, are shown in Figure \ref{fig:extr-type-nf}.
The correctness statement for the main function @{text "type_NF"} is
@{thm [display,margin=100] type_NF_correctness
  [simplified rtranclR_rtrancl_eq Collect_mem_eq, no_vars]}
where the realizability predicate @{text "rtypingR"} corresponding to the
computationally relevant version of the typing judgement is inductively
defined by the rules
@{thm [display,margin=100] rtypingR.Var [no_vars]
  rtypingR.Abs [of ty, no_vars] rtypingR.App [of ty e s T U ty' t]}
*}

subsection {* Generating executable code *}

instantiation NFT :: default
begin

definition "default = Dummy ()"

instance ..

end

instantiation dB :: default
begin

definition "default = dB.Var 0"

instance ..

end

instantiation prod :: (default, default) default
begin

definition "default = (default, default)"

instance ..

end

instantiation list :: (type) default
begin

definition "default = []"

instance ..

end

instantiation "fun" :: (type, default) default
begin

definition "default = (\<lambda>x. default)"

instance ..

end

definition int_of_nat :: "nat \<Rightarrow> int" where
  "int_of_nat = of_nat"

text {*
  The following functions convert between Isabelle's built-in {\tt term}
  datatype and the generated {\tt dB} datatype. This allows to
  generate example terms using Isabelle's parser and inspect
  normalized terms using Isabelle's pretty printer.
*}

ML {*
fun dBtype_of_typ (Type ("fun", [T, U])) =
      @{code Fun} (dBtype_of_typ T, dBtype_of_typ U)
  | dBtype_of_typ (TFree (s, _)) = (case raw_explode s of
        ["'", a] => @{code Atom} (@{code nat} (ord a - 97))
      | _ => error "dBtype_of_typ: variable name")
  | dBtype_of_typ _ = error "dBtype_of_typ: bad type";

fun dB_of_term (Bound i) = @{code dB.Var} (@{code nat} i)
  | dB_of_term (t $ u) = @{code dB.App} (dB_of_term t, dB_of_term u)
  | dB_of_term (Abs (_, _, t)) = @{code dB.Abs} (dB_of_term t)
  | dB_of_term _ = error "dB_of_term: bad term";

fun term_of_dB Ts (Type ("fun", [T, U])) (@{code dB.Abs} dBt) =
      Abs ("x", T, term_of_dB (T :: Ts) U dBt)
  | term_of_dB Ts _ dBt = term_of_dB' Ts dBt
and term_of_dB' Ts (@{code dB.Var} n) = Bound (@{code int_of_nat} n)
  | term_of_dB' Ts (@{code dB.App} (dBt, dBu)) =
      let val t = term_of_dB' Ts dBt
      in case fastype_of1 (Ts, t) of
          Type ("fun", [T, U]) => t $ term_of_dB Ts T dBu
        | _ => error "term_of_dB: function type expected"
      end
  | term_of_dB' _ _ = error "term_of_dB: term not in normal form";

fun typing_of_term Ts e (Bound i) =
      @{code Var} (e, @{code nat} i, dBtype_of_typ (nth Ts i))
  | typing_of_term Ts e (t $ u) = (case fastype_of1 (Ts, t) of
        Type ("fun", [T, U]) => @{code App} (e, dB_of_term t,
          dBtype_of_typ T, dBtype_of_typ U, dB_of_term u,
          typing_of_term Ts e t, typing_of_term Ts e u)
      | _ => error "typing_of_term: function type expected")
  | typing_of_term Ts e (Abs (s, T, t)) =
      let val dBT = dBtype_of_typ T
      in @{code Abs} (e, dBT, dB_of_term t,
        dBtype_of_typ (fastype_of1 (T :: Ts, t)),
        typing_of_term (T :: Ts) (@{code shift} e @{code "0::nat"} dBT) t)
      end
  | typing_of_term _ _ _ = error "typing_of_term: bad term";

fun dummyf _ = error "dummy";

val ct1 = @{cterm "%f. ((%f x. f (f (f x))) ((%f x. f (f (f (f x)))) f))"};
val (dB1, _) = @{code type_NF} (typing_of_term [] dummyf (term_of ct1));
val ct1' = cterm_of @{theory} (term_of_dB [] (#T (rep_cterm ct1)) dB1);

val ct2 = @{cterm "%f x. (%x. f x x) ((%x. f x x) ((%x. f x x) ((%x. f x x) ((%x. f x x) ((%x. f x x) x)))))"};
val (dB2, _) = @{code type_NF} (typing_of_term [] dummyf (term_of ct2));
val ct2' = cterm_of @{theory} (term_of_dB [] (#T (rep_cterm ct2)) dB2);
*}

end
