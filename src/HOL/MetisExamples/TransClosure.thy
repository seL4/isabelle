(*  Title:      HOL/MetisTest/TransClosure.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory

Testing the metis method
*)

theory TransClosure
imports Main
begin

types addr = nat

datatype val
  = Unit        -- "dummy result value of void expressions"
  | Null        -- "null reference"
  | Bool bool   -- "Boolean value"
  | Intg int    -- "integer value" 
  | Addr addr   -- "addresses of objects in the heap"

consts R::"(addr \<times> addr) set"

consts f:: "addr \<Rightarrow> val"

declare [[ atp_problem_prefix = "TransClosure__test" ]]
lemma "\<lbrakk> f c = Intg x; \<forall> y. f b = Intg y \<longrightarrow> y \<noteq> x; (a,b) \<in> R\<^sup>*; (b,c) \<in> R\<^sup>* \<rbrakk> 
   \<Longrightarrow> \<exists> c. (b,c) \<in> R \<and> (a,c) \<in> R\<^sup>*"  
by (metis Transitive_Closure.rtrancl_into_rtrancl converse_rtranclE trancl_reflcl)

lemma "\<lbrakk> f c = Intg x; \<forall> y. f b = Intg y \<longrightarrow> y \<noteq> x; (a,b) \<in> R\<^sup>*; (b,c) \<in> R\<^sup>* \<rbrakk> 
   \<Longrightarrow> \<exists> c. (b,c) \<in> R \<and> (a,c) \<in> R\<^sup>*"
proof (neg_clausify)
assume 0: "f c = Intg x"
assume 1: "(a, b) \<in> R\<^sup>*"
assume 2: "(b, c) \<in> R\<^sup>*"
assume 3: "f b \<noteq> Intg x"
assume 4: "\<And>A. (b, A) \<notin> R \<or> (a, A) \<notin> R\<^sup>*"
have 5: "b = c \<or> b \<in> Domain R"
  by (metis Not_Domain_rtrancl 2)
have 6: "\<And>X1. (a, X1) \<in> R\<^sup>* \<or> (b, X1) \<notin> R"
  by (metis Transitive_Closure.rtrancl_into_rtrancl 1)
have 7: "\<And>X1. (b, X1) \<notin> R"
  by (metis 6 4)
have 8: "b \<notin> Domain R"
  by (metis 7 DomainE)
have 9: "c = b"
  by (metis 5 8)
have 10: "f b = Intg x"
  by (metis 0 9)
show "False"
  by (metis 10 3)
qed

declare [[ atp_problem_prefix = "TransClosure__test_simpler" ]]
lemma "\<lbrakk> f c = Intg x; \<forall> y. f b = Intg y \<longrightarrow> y \<noteq> x; (a,b) \<in> R\<^sup>*; (b,c) \<in> R\<^sup>* \<rbrakk> 
   \<Longrightarrow> \<exists> c. (b,c) \<in> R \<and> (a,c) \<in> R\<^sup>*"
apply (erule_tac x="b" in converse_rtranclE)
apply (metis rel_pow_0_E rel_pow_0_I)
apply (metis DomainE Domain_iff Transitive_Closure.rtrancl_into_rtrancl)
done

end
