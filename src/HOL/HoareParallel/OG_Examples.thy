
header {* \section{Examples} *}

theory OG_Examples = OG_Syntax:

subsection {* Mutual Exclusion *}

subsubsection {* Peterson's Algorithm I*}

text {* Eike Best. "Semantics of Sequential and Parallel Programs", page 217. *}

record Petersons_mutex_1 =
 pr1 :: nat
 pr2 :: nat
 in1 :: bool
 in2 :: bool 
 hold :: nat

lemma Petersons_mutex_1: 
  "\<parallel>- .{\<acute>pr1=0 \<and> \<not>\<acute>in1 \<and> \<acute>pr2=0 \<and> \<not>\<acute>in2 }.  
  COBEGIN .{\<acute>pr1=0 \<and> \<not>\<acute>in1}.  
  WHILE True INV .{\<acute>pr1=0 \<and> \<not>\<acute>in1}.  
  DO  
  .{\<acute>pr1=0 \<and> \<not>\<acute>in1}. \<langle> \<acute>in1:=True,,\<acute>pr1:=1 \<rangle>;;  
  .{\<acute>pr1=1 \<and> \<acute>in1}.  \<langle> \<acute>hold:=1,,\<acute>pr1:=2 \<rangle>;;  
  .{\<acute>pr1=2 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> \<acute>hold=2 \<and> \<acute>pr2=2)}.  
  AWAIT (\<not>\<acute>in2 \<or> \<not>(\<acute>hold=1)) THEN \<acute>pr1:=3 END;;    
  .{\<acute>pr1=3 \<and> \<acute>in1 \<and> (\<acute>hold=1 \<or> \<acute>hold=2 \<and> \<acute>pr2=2)}. 
   \<langle>\<acute>in1:=False,,\<acute>pr1:=0\<rangle> 
  OD .{\<acute>pr1=0 \<and> \<not>\<acute>in1}.  
  \<parallel>  
  .{\<acute>pr2=0 \<and> \<not>\<acute>in2}.  
  WHILE True INV .{\<acute>pr2=0 \<and> \<not>\<acute>in2}.  
  DO  
  .{\<acute>pr2=0 \<and> \<not>\<acute>in2}. \<langle> \<acute>in2:=True,,\<acute>pr2:=1 \<rangle>;;  
  .{\<acute>pr2=1 \<and> \<acute>in2}. \<langle>  \<acute>hold:=2,,\<acute>pr2:=2 \<rangle>;;  
  .{\<acute>pr2=2 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))}.  
  AWAIT (\<not>\<acute>in1 \<or> \<not>(\<acute>hold=2)) THEN \<acute>pr2:=3  END;;    
  .{\<acute>pr2=3 \<and> \<acute>in2 \<and> (\<acute>hold=2 \<or> (\<acute>hold=1 \<and> \<acute>pr1=2))}. 
    \<langle>\<acute>in2:=False,,\<acute>pr2:=0\<rangle> 
  OD .{\<acute>pr2=0 \<and> \<not>\<acute>in2}.  
  COEND  
  .{\<acute>pr1=0 \<and> \<not>\<acute>in1 \<and> \<acute>pr2=0 \<and> \<not>\<acute>in2}."
apply oghoare
--{* 104 verification conditions. *}
apply auto
done

subsubsection {*Peterson's Algorithm II: A Busy Wait Solution *}
 
text {* Apt and Olderog. "Verification of sequential and concurrent Programs", page 282. *}

record Busy_wait_mutex =
 flag1 :: bool
 flag2 :: bool
 turn  :: nat
 after1 :: bool 
 after2 :: bool

lemma Busy_wait_mutex: 
 "\<parallel>-  .{True}.  
  \<acute>flag1:=False,, \<acute>flag2:=False,,  
  COBEGIN .{\<not>\<acute>flag1}.  
        WHILE True  
        INV .{\<not>\<acute>flag1}.  
        DO .{\<not>\<acute>flag1}. \<langle> \<acute>flag1:=True,,\<acute>after1:=False \<rangle>;;  
           .{\<acute>flag1 \<and> \<not>\<acute>after1}. \<langle> \<acute>turn:=1,,\<acute>after1:=True \<rangle>;;  
           .{\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)}.  
            WHILE \<not>(\<acute>flag2 \<longrightarrow> \<acute>turn=2)  
            INV .{\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)}.  
            DO .{\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)}. SKIP OD;; 
           .{\<acute>flag1 \<and> \<acute>after1 \<and> (\<acute>flag2 \<and> \<acute>after2 \<longrightarrow> \<acute>turn=2)}.
            \<acute>flag1:=False  
        OD  
       .{False}.  
  \<parallel>  
     .{\<not>\<acute>flag2}.  
        WHILE True  
        INV .{\<not>\<acute>flag2}.  
        DO .{\<not>\<acute>flag2}. \<langle> \<acute>flag2:=True,,\<acute>after2:=False \<rangle>;;  
           .{\<acute>flag2 \<and> \<not>\<acute>after2}. \<langle> \<acute>turn:=2,,\<acute>after2:=True \<rangle>;;  
           .{\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)}.  
            WHILE \<not>(\<acute>flag1 \<longrightarrow> \<acute>turn=1)  
            INV .{\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)}.  
            DO .{\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>turn=1 \<or> \<acute>turn=2)}. SKIP OD;;  
           .{\<acute>flag2 \<and> \<acute>after2 \<and> (\<acute>flag1 \<and> \<acute>after1 \<longrightarrow> \<acute>turn=1)}. 
            \<acute>flag2:=False  
        OD  
       .{False}.  
  COEND  
  .{False}."
apply oghoare
--{* 122 vc *}
apply auto
done

subsubsection {* Peterson's Algorithm III: A Solution using Semaphores  *}

record  Semaphores_mutex =
 out :: bool
 who :: nat

lemma Semaphores_mutex: 
 "\<parallel>- .{i\<noteq>j}.  
  \<acute>out:=True ,,  
  COBEGIN .{i\<noteq>j}.  
       WHILE True INV .{i\<noteq>j}.  
       DO .{i\<noteq>j}. AWAIT \<acute>out THEN  \<acute>out:=False,, \<acute>who:=i END;;  
          .{\<not>\<acute>out \<and> \<acute>who=i \<and> i\<noteq>j}. \<acute>out:=True OD  
       .{False}.  
  \<parallel>  
       .{i\<noteq>j}.  
       WHILE True INV .{i\<noteq>j}.  
       DO .{i\<noteq>j}. AWAIT \<acute>out THEN  \<acute>out:=False,,\<acute>who:=j END;;  
          .{\<not>\<acute>out \<and> \<acute>who=j \<and> i\<noteq>j}. \<acute>out:=True OD  
       .{False}.  
  COEND  
  .{False}."
apply oghoare
--{* 38 vc *}
apply auto
done

subsubsection {* Peterson's Algorithm III: Parameterized version: *}

lemma Semaphores_parameterized_mutex: 
 "0<n \<Longrightarrow> \<parallel>- .{True}.  
  \<acute>out:=True ,,  
 COBEGIN
  SCHEME [0\<le> i< n]
    .{True}.  
     WHILE True INV .{True}.  
      DO .{True}. AWAIT \<acute>out THEN  \<acute>out:=False,, \<acute>who:=i END;;  
         .{\<not>\<acute>out \<and> \<acute>who=i}. \<acute>out:=True OD
    .{False}. 
 COEND
  .{False}." 
apply oghoare
--{* 20 vc *}
apply auto
done

subsubsection{* The Ticket Algorithm *}

record Ticket_mutex =
 num :: nat
 nextv :: nat
 turn :: "nat list"
 index :: nat 

lemma Ticket_mutex: 
 "\<lbrakk> 0<n; I=\<guillemotleft>n=length \<acute>turn \<and> 0<\<acute>nextv \<and> (\<forall>k l. k<n \<and> l<n \<and> k\<noteq>l 
    \<longrightarrow> \<acute>turn!k < \<acute>num \<and> (\<acute>turn!k =0 \<or> \<acute>turn!k\<noteq>\<acute>turn!l))\<guillemotright> \<rbrakk>
   \<Longrightarrow> \<parallel>- .{n=length \<acute>turn}.  
   \<acute>index:= 0,,
   WHILE \<acute>index < n INV .{n=length \<acute>turn \<and> (\<forall>i<\<acute>index. \<acute>turn!i=0)}. 
    DO \<acute>turn:= \<acute>turn[\<acute>index:=0],, \<acute>index:=\<acute>index +1 OD,,
  \<acute>num:=1 ,, \<acute>nextv:=1 ,, 
 COBEGIN
  SCHEME [0\<le> i< n]
    .{\<acute>I}.  
     WHILE True INV .{\<acute>I}.  
      DO .{\<acute>I}. \<langle> \<acute>turn :=\<acute>turn[i:=\<acute>num],, \<acute>num:=\<acute>num+1 \<rangle>;;  
         .{\<acute>I}. WAIT \<acute>turn!i=\<acute>nextv END;;
         .{\<acute>I \<and> \<acute>turn!i=\<acute>nextv}. \<acute>nextv:=\<acute>nextv+1
      OD
    .{False}. 
 COEND
  .{False}." 
apply oghoare
--{* 35 vc *}
apply simp_all
--{* 21 vc *}
apply(tactic {* ALLGOALS Clarify_tac *})
--{* 11 vc *}
apply simp_all
apply(tactic {* ALLGOALS Clarify_tac *})
--{* 11 subgoals left *}
apply(erule less_SucE)
 apply simp
apply simp
--{* 10 subgoals left *}
apply force
apply(case_tac "i=k")
 apply force
apply simp
apply(case_tac "i=l")
 apply force
apply force
--{* 8 subgoals left *}
prefer 8
apply force
apply force
--{* 6 subgoals left *}
prefer 6
apply(erule_tac x=i in allE)
apply fastsimp
--{* 5 subgoals left *}
prefer 5
apply(tactic {* ALLGOALS (case_tac "j=k") *})
--{* 10 subgoals left *}
apply simp_all
apply(erule_tac x=k in allE)
apply force
--{* 9 subgoals left *}
apply(case_tac "j=l")
 apply simp
 apply(erule_tac x=k in allE)
 apply(erule_tac x=k in allE)
 apply(erule_tac x=l in allE)
 apply force
apply(erule_tac x=k in allE)
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply force
--{* 8 subgoals left *}
apply force
apply(case_tac "j=l")
 apply simp
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply force
apply force
apply force
--{* 5 subgoals left *}
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply(case_tac "j=l")
 apply force
apply force
apply force
--{* 3 subgoals left *}
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply(case_tac "j=l")
 apply force
apply force
apply force
--{* 1 subgoals left *}
apply(erule_tac x=k in allE)
apply(erule_tac x=l in allE)
apply(case_tac "j=l")
 apply force
apply force
done

subsection{* Parallel Zero Search *}

text {* Synchronized Zero Search. Zero-6 *}

text {*Apt and Olderog. "Verification of sequential and concurrent Programs" page 294: *}

record Zero_search =
   turn :: nat
   found :: bool
   x :: nat
   y :: nat

lemma Zero_search: 
  "\<lbrakk>I1= \<guillemotleft> a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0)) 
      \<and> (\<not>\<acute>found \<and> a<\<acute> x \<longrightarrow> f(\<acute>x)\<noteq>0) \<guillemotright> ;  
    I2= \<guillemotleft>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0)) 
      \<and> (\<not>\<acute>found \<and> \<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0) \<guillemotright> \<rbrakk> \<Longrightarrow>  
  \<parallel>- .{\<exists> u. f(u)=0}.  
  \<acute>turn:=1,, \<acute>found:= False,,  
  \<acute>x:=a,, \<acute>y:=a+1 ,,  
  COBEGIN .{\<acute>I1}.  
       WHILE \<not>\<acute>found  
       INV .{\<acute>I1}.  
       DO .{a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)}.  
          WAIT \<acute>turn=1 END;;  
          .{a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)}.  
          \<acute>turn:=2;;  
          .{a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)}.    
          \<langle> \<acute>x:=\<acute>x+1,,  
            IF f(\<acute>x)=0 THEN \<acute>found:=True ELSE SKIP FI\<rangle>  
       OD;;  
       .{\<acute>I1  \<and> \<acute>found}.  
       \<acute>turn:=2  
       .{\<acute>I1 \<and> \<acute>found}.  
  \<parallel>  
      .{\<acute>I2}.  
       WHILE \<not>\<acute>found  
       INV .{\<acute>I2}.  
       DO .{\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)}.  
          WAIT \<acute>turn=2 END;;  
          .{\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)}.  
          \<acute>turn:=1;;  
          .{\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)}.  
          \<langle> \<acute>y:=(\<acute>y - 1),,  
            IF f(\<acute>y)=0 THEN \<acute>found:=True ELSE SKIP FI\<rangle>  
       OD;;  
       .{\<acute>I2 \<and> \<acute>found}.  
       \<acute>turn:=1  
       .{\<acute>I2 \<and> \<acute>found}.  
  COEND  
  .{f(\<acute>x)=0 \<or> f(\<acute>y)=0}."
apply oghoare
--{* 98 verification conditions *}
apply auto 
--{* auto takes about 3 minutes !! *}
apply arith+
done

text {* Easier Version: without AWAIT.  Apt and Olderog. page 256: *}

lemma Zero_Search_2: 
"\<lbrakk>I1=\<guillemotleft> a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0)) 
    \<and> (\<not>\<acute>found \<and> a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)\<guillemotright>;  
 I2= \<guillemotleft>\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> (a<\<acute>x \<and> f(\<acute>x)=0) \<or> (\<acute>y\<le>a \<and> f(\<acute>y)=0)) 
    \<and> (\<not>\<acute>found \<and> \<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)\<guillemotright>\<rbrakk> \<Longrightarrow>  
  \<parallel>- .{\<exists>u. f(u)=0}.  
  \<acute>found:= False,,  
  \<acute>x:=a,, \<acute>y:=a+1,,  
  COBEGIN .{\<acute>I1}.  
       WHILE \<not>\<acute>found  
       INV .{\<acute>I1}.  
       DO .{a\<le>\<acute>x \<and> (\<acute>found \<longrightarrow> \<acute>y\<le>a \<and> f(\<acute>y)=0) \<and> (a<\<acute>x \<longrightarrow> f(\<acute>x)\<noteq>0)}.  
          \<langle> \<acute>x:=\<acute>x+1,,IF f(\<acute>x)=0 THEN  \<acute>found:=True ELSE  SKIP FI\<rangle>  
       OD  
       .{\<acute>I1 \<and> \<acute>found}.  
  \<parallel>  
      .{\<acute>I2}.  
       WHILE \<not>\<acute>found  
       INV .{\<acute>I2}.  
       DO .{\<acute>y\<le>a+1 \<and> (\<acute>found \<longrightarrow> a<\<acute>x \<and> f(\<acute>x)=0) \<and> (\<acute>y\<le>a \<longrightarrow> f(\<acute>y)\<noteq>0)}.  
          \<langle> \<acute>y:=(\<acute>y - 1),,IF f(\<acute>y)=0 THEN  \<acute>found:=True ELSE  SKIP FI\<rangle>  
       OD  
       .{\<acute>I2 \<and> \<acute>found}.  
  COEND  
  .{f(\<acute>x)=0 \<or> f(\<acute>y)=0}."
apply oghoare
--{* 20 vc *}
apply auto
--{* auto takes aprox. 2 minutes. *}
apply arith+
done

subsection {* Producer/Consumer *}

subsubsection {* Previous lemmas *}

lemma nat_lemma2: "\<lbrakk> b = m*(n::nat) + t; a = s*n + u; t=u; b-a < n \<rbrakk> \<Longrightarrow> m \<le> s"
proof -
  assume "b = m*(n::nat) + t" "a = s*n + u" "t=u"
  hence "(m - s) * n = b - a" by (simp add: diff_mult_distrib)
  also assume "\<dots> < n"
  finally have "m - s < 1" by simp
  thus ?thesis by arith
qed

lemma mod_lemma: "\<lbrakk> (c::nat) \<le> a; a < b; b - c < n \<rbrakk> \<Longrightarrow> b mod n \<noteq> a mod n"
apply(subgoal_tac "b=b div n*n + b mod n" )
 prefer 2  apply (simp add: mod_div_equality [symmetric])
apply(subgoal_tac "a=a div n*n + a mod n")
 prefer 2
 apply(simp add: mod_div_equality [symmetric])
apply(subgoal_tac "b - a \<le> b - c")
 prefer 2 apply arith
apply(drule le_less_trans)
back
 apply assumption
apply(frule less_not_refl2)
apply(drule less_imp_le)
apply (drule_tac m = "a" and k = n in div_le_mono)
apply(safe)
apply(frule_tac b = "b" and a = "a" and n = "n" in nat_lemma2, assumption, assumption)
apply assumption
apply(drule order_antisym, assumption)
apply(rotate_tac -3)
apply(simp)
done


subsubsection {* Producer/Consumer Algorithm *}

record Producer_consumer =
  ins :: nat
  outs :: nat
  li :: nat
  lj :: nat
  vx :: nat
  vy :: nat
  buffer :: "nat list"
  b :: "nat list"

text {* The whole proof takes aprox. 4 minutes. *}

lemma Producer_consumer: 
  "\<lbrakk>INIT= \<guillemotleft>0<length a \<and> 0<length \<acute>buffer \<and> length \<acute>b=length a\<guillemotright> ;  
    I= \<guillemotleft>(\<forall>k<\<acute>ins. \<acute>outs\<le>k \<longrightarrow> (a ! k) = \<acute>buffer ! (k mod (length \<acute>buffer))) \<and>  
            \<acute>outs\<le>\<acute>ins \<and> \<acute>ins-\<acute>outs\<le>length \<acute>buffer\<guillemotright> ;  
    I1= \<guillemotleft>\<acute>I \<and> \<acute>li\<le>length a\<guillemotright> ;  
    p1= \<guillemotleft>\<acute>I1 \<and> \<acute>li=\<acute>ins\<guillemotright> ;  
    I2 = \<guillemotleft>\<acute>I \<and> (\<forall>k<\<acute>lj. (a ! k)=(\<acute>b ! k)) \<and> \<acute>lj\<le>length a\<guillemotright> ;
    p2 = \<guillemotleft>\<acute>I2 \<and> \<acute>lj=\<acute>outs\<guillemotright> \<rbrakk> \<Longrightarrow>   
  \<parallel>- .{\<acute>INIT}.  
 \<acute>ins:=0,, \<acute>outs:=0,, \<acute>li:=0,, \<acute>lj:=0,,
 COBEGIN .{\<acute>p1 \<and> \<acute>INIT}. 
   WHILE \<acute>li <length a 
     INV .{\<acute>p1 \<and> \<acute>INIT}.   
   DO .{\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a}.  
       \<acute>vx:= (a ! \<acute>li);;  
      .{\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a \<and> \<acute>vx=(a ! \<acute>li)}. 
        WAIT \<acute>ins-\<acute>outs < length \<acute>buffer END;; 
      .{\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a \<and> \<acute>vx=(a ! \<acute>li) 
         \<and> \<acute>ins-\<acute>outs < length \<acute>buffer}. 
       \<acute>buffer:=(list_update \<acute>buffer (\<acute>ins mod (length \<acute>buffer)) \<acute>vx);; 
      .{\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li<length a 
         \<and> (a ! \<acute>li)=(\<acute>buffer ! (\<acute>ins mod (length \<acute>buffer))) 
         \<and> \<acute>ins-\<acute>outs <length \<acute>buffer}.  
       \<acute>ins:=\<acute>ins+1;; 
      .{\<acute>I1 \<and> \<acute>INIT \<and> (\<acute>li+1)=\<acute>ins \<and> \<acute>li<length a}.  
       \<acute>li:=\<acute>li+1  
   OD  
  .{\<acute>p1 \<and> \<acute>INIT \<and> \<acute>li=length a}.  
  \<parallel>  
  .{\<acute>p2 \<and> \<acute>INIT}.  
   WHILE \<acute>lj < length a  
     INV .{\<acute>p2 \<and> \<acute>INIT}.  
   DO .{\<acute>p2 \<and> \<acute>lj<length a \<and> \<acute>INIT}.  
        WAIT \<acute>outs<\<acute>ins END;; 
      .{\<acute>p2 \<and> \<acute>lj<length a \<and> \<acute>outs<\<acute>ins \<and> \<acute>INIT}.  
       \<acute>vy:=(\<acute>buffer ! (\<acute>outs mod (length \<acute>buffer)));; 
      .{\<acute>p2 \<and> \<acute>lj<length a \<and> \<acute>outs<\<acute>ins \<and> \<acute>vy=(a ! \<acute>lj) \<and> \<acute>INIT}.  
       \<acute>outs:=\<acute>outs+1;;  
      .{\<acute>I2 \<and> (\<acute>lj+1)=\<acute>outs \<and> \<acute>lj<length a \<and> \<acute>vy=(a ! \<acute>lj) \<and> \<acute>INIT}.  
       \<acute>b:=(list_update \<acute>b \<acute>lj \<acute>vy);; 
      .{\<acute>I2 \<and> (\<acute>lj+1)=\<acute>outs \<and> \<acute>lj<length a \<and> (a ! \<acute>lj)=(\<acute>b ! \<acute>lj) \<and> \<acute>INIT}.  
       \<acute>lj:=\<acute>lj+1  
   OD  
  .{\<acute>p2 \<and> \<acute>lj=length a \<and> \<acute>INIT}.  
 COEND  
 .{ \<forall>k<length a. (a ! k)=(\<acute>b ! k)}."
apply oghoare
--{* 138 vc  *}
apply(tactic {* ALLGOALS Clarify_tac *})
--{* 112 subgoals left *}
apply(simp_all (no_asm))
apply(tactic {*ALLGOALS (conjI_Tac (K all_tac)) *})
--{* 930 subgoals left *}
apply(tactic {* ALLGOALS Clarify_tac *})
apply(simp_all (asm_lr) only:length_0_conv [THEN sym])
--{* 44 subgoals left *}
apply (simp_all (asm_lr) del:length_0_conv add: nth_list_update mod_less_divisor mod_lemma)
--{* 33 subgoals left *}
apply(tactic {* ALLGOALS Clarify_tac *})
apply(tactic {* TRYALL arith_tac *})
--{* 10 subgoals left *}
apply (force simp add:less_Suc_eq)
apply(drule sym)
apply (force simp add:less_Suc_eq)+
done

subsection {* Parameterized Examples *}

subsubsection {* Set Elements of an Array to Zero *}

record Example1 =
  a :: "nat \<Rightarrow> nat"

lemma Example1: 
 "\<parallel>- .{True}.
   COBEGIN SCHEME [0\<le>i<n] .{True}. \<acute>a:=\<acute>a (i:=0) .{\<acute>a i=0}. COEND 
  .{\<forall>i < n. \<acute>a i = 0}."
apply oghoare
apply simp_all
done

text {* Same example with lists as auxiliary variables. *}
record Example1_list =
  A :: "nat list"
lemma Example1_list: 
 "\<parallel>- .{n < length \<acute>A}. 
   COBEGIN 
     SCHEME [0\<le>i<n] .{n < length \<acute>A}. \<acute>A:=\<acute>A[i:=0] .{\<acute>A!i=0}. 
   COEND 
    .{\<forall>i < n. \<acute>A!i = 0}."
apply oghoare
apply force+
done

subsubsection {* Increment a Variable in Parallel *}

text {* First some lemmas about summation properties. Summation is
defined in PreList. *}

lemma Example2_lemma1: "!!b. j<n \<Longrightarrow> (\<Sum>i<n. b i) = (0::nat) \<Longrightarrow> b j = 0 "
apply(induct n)
 apply simp_all
apply(force simp add: less_Suc_eq)
done

lemma Example2_lemma2_aux: "!!b. j<n \<Longrightarrow> 
 (\<Sum>i<n. (b i::nat)) = (\<Sum>i<j. b i) + b j + (\<Sum>i<n-(Suc j) . b (Suc j + i))"
apply(induct n)
 apply simp_all
apply(simp add:less_Suc_eq)
 apply(auto)
apply(subgoal_tac "n - j = Suc(n- Suc j)")
  apply simp
apply arith
done

lemma Example2_lemma2_aux2: 
  "!!b. j\<le> s \<Longrightarrow> (\<Sum>i<j. (b (s:=t)) i) = (\<Sum>i<j. b i)"
apply(induct j)
 apply simp_all
done

lemma Example2_lemma2: 
 "!!b. \<lbrakk>j<n; b j=0\<rbrakk> \<Longrightarrow> Suc (\<Sum>i< n. b i)=(\<Sum>i< n. (b (j := Suc 0)) i)"
apply(frule_tac b="(b (j:=(Suc 0)))" in Example2_lemma2_aux)
apply(erule_tac  t="Summation (b(j := (Suc 0))) n" in ssubst)
apply(frule_tac b=b in Example2_lemma2_aux)
apply(erule_tac  t="Summation b n" in ssubst)
apply(subgoal_tac "Suc (Summation b j + b j + (\<Sum>i<n - Suc j. b (Suc j + i)))=(Summation b j + Suc (b j) + (\<Sum>i<n - Suc j. b (Suc j + i)))")
apply(rotate_tac -1)
apply(erule ssubst)
apply(subgoal_tac "j\<le>j")
 apply(drule_tac b="b" and t="(Suc 0)" in Example2_lemma2_aux2)
apply(rotate_tac -1)
apply(erule ssubst)
apply simp_all
done

lemma Example2_lemma3: "!!b. \<forall>i< n. b i = (Suc 0) \<Longrightarrow> (\<Sum>i<n. b i)= n"
apply (induct n)
apply auto
done

record Example2 = 
 c :: "nat \<Rightarrow> nat" 
 x :: nat

lemma Example_2: "0<n \<Longrightarrow> 
 \<parallel>- .{\<acute>x=0 \<and> (\<Sum>i< n. \<acute>c i)=0}.  
 COBEGIN 
   SCHEME [0\<le>i<n] 
  .{\<acute>x=(\<Sum>i< n. \<acute>c i) \<and> \<acute>c i=0}. 
   \<langle> \<acute>x:=\<acute>x+(Suc 0),, \<acute>c:=\<acute>c (i:=(Suc 0)) \<rangle>
  .{\<acute>x=(\<Sum>i< n. \<acute>c i) \<and> \<acute>c i=(Suc 0)}.
 COEND 
 .{\<acute>x=n}."
apply oghoare
apply simp_all
apply (tactic {* ALLGOALS Clarify_tac *})
apply simp_all
    apply(force elim:Example2_lemma1)
   apply(erule Example2_lemma2)
   apply simp
  apply(erule Example2_lemma2)
  apply simp
 apply(erule Example2_lemma2)
 apply simp
apply(force intro: Example2_lemma3)
done

end
