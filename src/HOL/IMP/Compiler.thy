(*  Title:      HOL/IMP/Compiler.thy
    ID:         $Id$
    Author:     Tobias Nipkow, TUM
    Copyright   1996 TUM
*)

theory Compiler = Machines:

subsection "The compiler"

consts compile :: "com \<Rightarrow> instr list"
primrec
"compile \<SKIP> = []"
"compile (x:==a) = [ASIN x a]"
"compile (c1;c2) = compile c1 @ compile c2"
"compile (\<IF> b \<THEN> c1 \<ELSE> c2) =
 [JMPF b (length(compile c1) + 1)] @ compile c1 @
 [JMPF (%x. False) (length(compile c2))] @ compile c2"
"compile (\<WHILE> b \<DO> c) = [JMPF b (length(compile c) + 1)] @ compile c @
 [JMPB (length(compile c)+1)]"

subsection "Compiler correctness"

theorem assumes A: "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
shows "\<And>p q. \<langle>compile c @ p,q,s\<rangle> -*\<rightarrow> \<langle>p,rev(compile c)@q,t\<rangle>"
  (is "\<And>p q. ?P c s t p q")
proof -
  from A show "\<And>p q. ?thesis p q"
  proof induct
    case Skip thus ?case by simp
  next
    case Assign thus ?case by force
  next
    case Semi thus ?case by simp (blast intro:rtrancl_trans)
  next
    fix b c0 c1 s0 s1 p q
    assume IH: "\<And>p q. ?P c0 s0 s1 p q"
    assume "b s0"
    thus "?P (\<IF> b \<THEN> c0 \<ELSE> c1) s0 s1 p q"
      by(simp add: IH[THEN rtrancl_trans])
  next
    case IfFalse thus ?case by(simp)
  next
    case WhileFalse thus ?case by simp
  next
    fix b c and s0::state and s1 s2 p q
    assume b: "b s0" and
      IHc: "\<And>p q. ?P c s0 s1 p q" and
      IHw: "\<And>p q. ?P (\<WHILE> b \<DO> c) s1 s2 p q"
    show "?P (\<WHILE> b \<DO> c) s0 s2 p q"
      using b  IHc[THEN rtrancl_trans] IHw by(simp)
  qed
qed

text {* The other direction! *}

inductive_cases [elim!]: "(([],p,s),next) : stepa1"

lemma [simp]: "(\<langle>[],q,s\<rangle> -n\<rightarrow> \<langle>p',q',t\<rangle>) = (n=0 \<and> p' = [] \<and> q' = q \<and> t = s)"
apply(rule iffI)
 apply(erule converse_rel_powE, simp, fast)
apply simp
done

lemma [simp]: "(\<langle>[],q,s\<rangle> -*\<rightarrow> \<langle>p',q',t\<rangle>) = (p' = [] \<and> q' = q \<and> t = s)"
by(simp add: rtrancl_is_UN_rel_pow)

constdefs
 forws :: "instr \<Rightarrow> nat set"
"forws instr == case instr of
 ASIN x a \<Rightarrow> {0} |
 JMPF b n \<Rightarrow> {0,n} |
 JMPB n \<Rightarrow> {}"
 backws :: "instr \<Rightarrow> nat set"
"backws instr == case instr of
 ASIN x a \<Rightarrow> {} |
 JMPF b n \<Rightarrow> {} |
 JMPB n \<Rightarrow> {n}"

consts closed :: "nat \<Rightarrow> nat \<Rightarrow> instr list \<Rightarrow> bool"
primrec
"closed m n [] = True"
"closed m n (instr#is) = ((\<forall>j \<in> forws instr. j \<le> size is+n) \<and>
                        (\<forall>j \<in> backws instr. j \<le> m) \<and> closed (Suc m) n is)"

lemma [simp]:
 "\<And>m n. closed m n (C1@C2) =
         (closed m (n+size C2) C1 \<and> closed (m+size C1) n C2)"
by(induct C1, simp, simp add:plus_ac0)

theorem [simp]: "\<And>m n. closed m n (compile c)"
by(induct c, simp_all add:backws_def forws_def)

lemma drop_lem: "n \<le> size(p1@p2)
 \<Longrightarrow> (p1' @ p2 = drop n p1 @ drop (n - size p1) p2) =
    (n \<le> size p1 & p1' = drop n p1)"
apply(rule iffI)
 defer apply simp
apply(subgoal_tac "n \<le> size p1")
 apply(rotate_tac -1)
 apply simp
apply(rule ccontr)
apply(rotate_tac -1)
apply(drule_tac f = length in arg_cong)
apply simp
apply arith
done

lemma reduce_exec1:
 "\<langle>i # p1 @ p2,q1 @ q2,s\<rangle> -1\<rightarrow> \<langle>p1' @ p2,q1' @ q2,s'\<rangle> \<Longrightarrow>
  \<langle>i # p1,q1,s\<rangle> -1\<rightarrow> \<langle>p1',q1',s'\<rangle>"
by(clarsimp simp add: drop_lem split:instr.split_asm split_if_asm)


lemma closed_exec1:
 "\<lbrakk> closed 0 0 (rev q1 @ instr # p1);
    \<langle>instr # p1 @ p2, q1 @ q2,r\<rangle> -1\<rightarrow> \<langle>p',q',r'\<rangle> \<rbrakk> \<Longrightarrow>
  \<exists>p1' q1'. p' = p1'@p2 \<and> q' = q1'@q2 \<and> rev q1' @ p1' = rev q1 @ instr # p1"
apply(clarsimp simp add:forws_def backws_def
               split:instr.split_asm split_if_asm)
done

theorem closed_execn_decomp: "\<And>C1 C2 r.
 \<lbrakk> closed 0 0 (rev C1 @ C2);
   \<langle>C2 @ p1 @ p2, C1 @ q,r\<rangle> -n\<rightarrow> \<langle>p2,rev p1 @ rev C2 @ C1 @ q,t\<rangle> \<rbrakk>
 \<Longrightarrow> \<exists>s n1 n2. \<langle>C2,C1,r\<rangle> -n1\<rightarrow> \<langle>[],rev C2 @ C1,s\<rangle> \<and>
     \<langle>p1@p2,rev C2 @ C1 @ q,s\<rangle> -n2\<rightarrow> \<langle>p2, rev p1 @ rev C2 @ C1 @ q,t\<rangle> \<and>
         n = n1+n2"
(is "\<And>C1 C2 r. \<lbrakk>?CL C1 C2; ?H C1 C2 r n\<rbrakk> \<Longrightarrow> ?P C1 C2 r n")
proof(induct n)
  fix C1 C2 r
  assume "?H C1 C2 r 0"
  thus "?P C1 C2 r 0" by simp
next
  fix C1 C2 r n
  assume IH: "\<And>C1 C2 r. ?CL C1 C2 \<Longrightarrow> ?H C1 C2 r n \<Longrightarrow> ?P C1 C2 r n"
  assume CL: "?CL C1 C2" and H: "?H C1 C2 r (Suc n)"
  show "?P C1 C2 r (Suc n)"
  proof (cases C2)
    assume "C2 = []" with H show ?thesis by simp
  next
    fix instr tlC2
    assume C2: "C2 = instr # tlC2"
    from H C2 obtain p' q' r'
      where 1: "\<langle>instr # tlC2 @ p1 @ p2, C1 @ q,r\<rangle> -1\<rightarrow> \<langle>p',q',r'\<rangle>"
      and n: "\<langle>p',q',r'\<rangle> -n\<rightarrow> \<langle>p2,rev p1 @ rev C2 @ C1 @ q,t\<rangle>"
      by(fastsimp simp add:R_O_Rn_commute)
    from CL closed_exec1[OF _ 1] C2
    obtain C2' C1' where pq': "p' = C2' @ p1 @ p2 \<and> q' = C1' @ q"
      and same: "rev C1' @ C2' = rev C1 @ C2"
      by fastsimp
    have rev_same: "rev C2' @ C1' = rev C2 @ C1"
    proof -
      have "rev C2' @ C1' = rev(rev C1' @ C2')" by simp
      also have "\<dots> = rev(rev C1 @ C2)" by(simp only:same)
      also have "\<dots> =  rev C2 @ C1" by simp
      finally show ?thesis .
    qed
    hence rev_same': "\<And>p. rev C2' @ C1' @ p = rev C2 @ C1 @ p" by simp
    from n have n': "\<langle>C2' @ p1 @ p2,C1' @ q,r'\<rangle> -n\<rightarrow>
                     \<langle>p2,rev p1 @ rev C2' @ C1' @ q,t\<rangle>"
      by(simp add:pq' rev_same')
    from IH[OF _ n'] CL
    obtain s n1 n2 where n1: "\<langle>C2',C1',r'\<rangle> -n1\<rightarrow> \<langle>[],rev C2 @ C1,s\<rangle>" and
      "\<langle>p1 @ p2,rev C2 @ C1 @ q,s\<rangle> -n2\<rightarrow> \<langle>p2,rev p1 @ rev C2 @ C1 @ q,t\<rangle> \<and>
       n = n1 + n2"
      by(fastsimp simp add: same rev_same rev_same')
    moreover
    from 1 n1 pq' C2 have "\<langle>C2,C1,r\<rangle> -Suc n1\<rightarrow> \<langle>[],rev C2 @ C1,s\<rangle>"
      by (simp del:relpow.simps exec_simp) (fast dest:reduce_exec1)
    ultimately show ?thesis by (fastsimp simp del:relpow.simps)
  qed
qed

lemma execn_decomp:
"\<langle>compile c @ p1 @ p2,q,r\<rangle> -n\<rightarrow> \<langle>p2,rev p1 @ rev(compile c) @ q,t\<rangle>
 \<Longrightarrow> \<exists>s n1 n2. \<langle>compile c,[],r\<rangle> -n1\<rightarrow> \<langle>[],rev(compile c),s\<rangle> \<and>
     \<langle>p1@p2,rev(compile c) @ q,s\<rangle> -n2\<rightarrow> \<langle>p2, rev p1 @ rev(compile c) @ q,t\<rangle> \<and>
         n = n1+n2"
using closed_execn_decomp[of "[]",simplified] by simp

lemma exec_star_decomp:
"\<langle>compile c @ p1 @ p2,q,r\<rangle> -*\<rightarrow> \<langle>p2,rev p1 @ rev(compile c) @ q,t\<rangle>
 \<Longrightarrow> \<exists>s. \<langle>compile c,[],r\<rangle> -*\<rightarrow> \<langle>[],rev(compile c),s\<rangle> \<and>
     \<langle>p1@p2,rev(compile c) @ q,s\<rangle> -*\<rightarrow> \<langle>p2, rev p1 @ rev(compile c) @ q,t\<rangle>"
by(simp add:rtrancl_is_UN_rel_pow)(fast dest: execn_decomp)


(* Alternative:
lemma exec_comp_n:
"\<And>p1 p2 q r t n.
 \<langle>compile c @ p1 @ p2,q,r\<rangle> -n\<rightarrow> \<langle>p2,rev p1 @ rev(compile c) @ q,t\<rangle>
 \<Longrightarrow> \<exists>s n1 n2. \<langle>compile c,[],r\<rangle> -n1\<rightarrow> \<langle>[],rev(compile c),s\<rangle> \<and>
     \<langle>p1@p2,rev(compile c) @ q,s\<rangle> -n2\<rightarrow> \<langle>p2, rev p1 @ rev(compile c) @ q,t\<rangle> \<and>
         n = n1+n2"
 (is "\<And>p1 p2 q r t n. ?H c p1 p2 q r t n \<Longrightarrow> ?P c p1 p2 q r t n")
proof (induct c)
*)

text{*Warning: 
@{prop"\<langle>compile c @ p,q,s\<rangle> -*\<rightarrow> \<langle>p,rev(compile c)@q,t\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"}
is not true! *}

theorem "\<And>s t.
 \<langle>compile c,[],s\<rangle> -*\<rightarrow> \<langle>[],rev(compile c),t\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
proof (induct c)
  fix s t
  assume "\<langle>compile SKIP,[],s\<rangle> -*\<rightarrow> \<langle>[],rev(compile SKIP),t\<rangle>"
  thus "\<langle>SKIP,s\<rangle> \<longrightarrow>\<^sub>c t" by simp
next
  fix s t v f
  assume "\<langle>compile(v :== f),[],s\<rangle> -*\<rightarrow> \<langle>[],rev(compile(v :== f)),t\<rangle>"
  thus "\<langle>v :== f,s\<rangle> \<longrightarrow>\<^sub>c t" by simp
next
  fix s1 s3 c1 c2
  let ?C1 = "compile c1" let ?C2 = "compile c2"
  assume IH1: "\<And>s t. \<langle>?C1,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C1,t\<rangle> \<Longrightarrow> \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c t"
     and IH2: "\<And>s t. \<langle>?C2,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C2,t\<rangle> \<Longrightarrow> \<langle>c2,s\<rangle> \<longrightarrow>\<^sub>c t"
  assume "\<langle>compile(c1;c2),[],s1\<rangle> -*\<rightarrow> \<langle>[],rev(compile(c1;c2)),s3\<rangle>"
  then obtain s2 where exec1: "\<langle>?C1,[],s1\<rangle> -*\<rightarrow> \<langle>[],rev ?C1,s2\<rangle>" and
             exec2: "\<langle>?C2,rev ?C1,s2\<rangle> -*\<rightarrow> \<langle>[],rev(compile(c1;c2)),s3\<rangle>"
    by(fastsimp dest:exec_star_decomp[of _ _ "[]" "[]",simplified])
  from exec2 have exec2': "\<langle>?C2,[],s2\<rangle> -*\<rightarrow> \<langle>[],rev ?C2,s3\<rangle>"
    using exec_star_decomp[of _ "[]" "[]"] by fastsimp
  have "\<langle>c1,s1\<rangle> \<longrightarrow>\<^sub>c s2" using IH1 exec1 by simp
  moreover have "\<langle>c2,s2\<rangle> \<longrightarrow>\<^sub>c s3" using IH2 exec2' by fastsimp
  ultimately show "\<langle>c1;c2,s1\<rangle> \<longrightarrow>\<^sub>c s3" ..
next
  fix s t b c1 c2
  let ?if = "IF b THEN c1 ELSE c2" let ?C = "compile ?if"
  let ?C1 = "compile c1" let ?C2 = "compile c2"
  assume IH1: "\<And>s t. \<langle>?C1,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C1,t\<rangle> \<Longrightarrow> \<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c t"
     and IH2: "\<And>s t. \<langle>?C2,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C2,t\<rangle> \<Longrightarrow> \<langle>c2,s\<rangle> \<longrightarrow>\<^sub>c t"
     and H: "\<langle>?C,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C,t\<rangle>"
  show "\<langle>?if,s\<rangle> \<longrightarrow>\<^sub>c t"
  proof cases
    assume b: "b s"
    with H have "\<langle>?C1,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C1,t\<rangle>"
      by (fastsimp dest:exec_star_decomp
            [of _ "[JMPF (\<lambda>x. False) (size ?C2)]@?C2" "[]",simplified])
    hence "\<langle>c1,s\<rangle> \<longrightarrow>\<^sub>c t" by(rule IH1)
    with b show ?thesis ..
  next
    assume b: "\<not> b s"
    with H have "\<langle>?C2,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C2,t\<rangle>"
      using exec_star_decomp[of _ "[]" "[]"] by simp
    hence "\<langle>c2,s\<rangle> \<longrightarrow>\<^sub>c t" by(rule IH2)
    with b show ?thesis ..
  qed
next
  fix b c s t
  let ?w = "WHILE b DO c" let ?W = "compile ?w" let ?C = "compile c"
  let ?j1 = "JMPF b (size ?C + 1)" let ?j2 = "JMPB (size ?C + 1)"
  assume IHc: "\<And>s t. \<langle>?C,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C,t\<rangle> \<Longrightarrow> \<langle>c,s\<rangle> \<longrightarrow>\<^sub>c t"
     and H: "\<langle>?W,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?W,t\<rangle>"
  from H obtain k where ob:"\<langle>?W,[],s\<rangle> -k\<rightarrow> \<langle>[],rev ?W,t\<rangle>"
    by(simp add:rtrancl_is_UN_rel_pow) blast
  { fix n have "\<And>s. \<langle>?W,[],s\<rangle> -n\<rightarrow> \<langle>[],rev ?W,t\<rangle> \<Longrightarrow> \<langle>?w,s\<rangle> \<longrightarrow>\<^sub>c t"
    proof (induct n rule: less_induct)
      fix n
      assume IHm: "\<And>m s. \<lbrakk>m < n; \<langle>?W,[],s\<rangle> -m\<rightarrow> \<langle>[],rev ?W,t\<rangle> \<rbrakk> \<Longrightarrow> \<langle>?w,s\<rangle> \<longrightarrow>\<^sub>c t"
      fix s
      assume H: "\<langle>?W,[],s\<rangle> -n\<rightarrow> \<langle>[],rev ?W,t\<rangle>"
      show "\<langle>?w,s\<rangle> \<longrightarrow>\<^sub>c t"
      proof cases
	assume b: "b s"
	then obtain m where m: "n = Suc m"
          and 1: "\<langle>?C @ [?j2],[?j1],s\<rangle> -m\<rightarrow> \<langle>[],rev ?W,t\<rangle>"
	  using H by fastsimp
	then obtain r n1 n2 where n1: "\<langle>?C,[],s\<rangle> -n1\<rightarrow> \<langle>[],rev ?C,r\<rangle>"
          and n2: "\<langle>[?j2],rev ?C @ [?j1],r\<rangle> -n2\<rightarrow> \<langle>[],rev ?W,t\<rangle>"
          and n12: "m = n1+n2"
	  using execn_decomp[of _ "[?j2]"]
	  by(simp del: execn_simp) fast
	have n2n: "n2 - 1 < n" using m n12 by arith
	note b
	moreover
	{ from n1 have "\<langle>?C,[],s\<rangle> -*\<rightarrow> \<langle>[],rev ?C,r\<rangle>"
	    by (simp add:rtrancl_is_UN_rel_pow) fast
	  hence "\<langle>c,s\<rangle> \<longrightarrow>\<^sub>c r" by(rule IHc)
	}
	moreover
	{ have "n2 - 1 < n" using m n12 by arith
	  moreover from n2 have "\<langle>?W,[],r\<rangle> -n2- 1\<rightarrow> \<langle>[],rev ?W,t\<rangle>" by fastsimp
	  ultimately have "\<langle>?w,r\<rangle> \<longrightarrow>\<^sub>c t" by(rule IHm)
	}
	ultimately show ?thesis ..
      next
	assume b: "\<not> b s"
	hence "t = s" using H by simp
	with b show ?thesis by simp
      qed
    qed
  }
  with ob show "\<langle>?w,s\<rangle> \<longrightarrow>\<^sub>c t" by fast
qed

(* To Do: connect with Machine 0 using M_equiv *)

end