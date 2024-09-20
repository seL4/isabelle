(*  Title:      HOL/IOA/IOA.thy
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen
*)

section \<open>The I/O automata of Lynch and Tuttle\<close>

theory IOA
imports Asig
begin

type_synonym 'a seq = "nat => 'a"
type_synonym 'a oseq = "nat => 'a option"
type_synonym ('a, 'b) execution = "'a oseq * 'b seq"
type_synonym ('a, 's) transition = "('s * 'a * 's)"
type_synonym ('a,'s) ioa = "'a signature * 's set * ('a, 's) transition set"

(* IO automata *)

definition state_trans :: "['action signature, ('action,'state)transition set] => bool"
  where "state_trans asig R \<equiv>
     (\<forall>triple. triple \<in> R \<longrightarrow> fst(snd(triple)) \<in> actions(asig)) \<and>
     (\<forall>a. (a \<in> inputs(asig)) \<longrightarrow> (\<forall>s1. \<exists>s2. (s1,a,s2) \<in> R))"

definition asig_of :: "('action,'state)ioa => 'action signature"
  where "asig_of == fst"

definition starts_of :: "('action,'state)ioa => 'state set"
  where "starts_of == (fst o snd)"

definition trans_of :: "('action,'state)ioa => ('action,'state)transition set"
  where "trans_of == (snd o snd)"

definition IOA :: "('action,'state)ioa => bool"
  where "IOA(ioa) == (is_asig(asig_of(ioa)) &
                (~ starts_of(ioa) = {}) &
                state_trans (asig_of ioa) (trans_of ioa))"


(* Executions, schedules, and traces *)

(* An execution fragment is modelled with a pair of sequences:
   the first is the action options, the second the state sequence.
   Finite executions have None actions from some point on. *)
definition is_execution_fragment :: "[('action,'state)ioa, ('action,'state)execution] => bool"
  where "is_execution_fragment A ex \<equiv>
     let act = fst(ex); state = snd(ex)
     in \<forall>n a. (act(n)=None \<longrightarrow> state(Suc(n)) = state(n)) \<and>
              (act(n)=Some(a) \<longrightarrow> (state(n),a,state(Suc(n))) \<in> trans_of(A))"

definition executions :: "('action,'state)ioa => ('action,'state)execution set"
  where "executions(ioa) \<equiv> {e. snd e 0 \<in> starts_of(ioa) \<and> is_execution_fragment ioa e}"


definition reachable :: "[('action,'state)ioa, 'state] => bool"
  where "reachable ioa s \<equiv> (\<exists>ex\<in>executions(ioa). \<exists>n. (snd ex n) = s)"

definition invariant :: "[('action,'state)ioa, 'state=>bool] => bool"
  where "invariant A P \<equiv> (\<forall>s. reachable A s \<longrightarrow> P(s))"


(* Composition of action signatures and automata *)

consts
  compatible_asigs ::"('a \<Rightarrow> 'action signature) \<Rightarrow> bool"
  asig_composition ::"('a \<Rightarrow> 'action signature) \<Rightarrow> 'action signature"
  compatible_ioas  ::"('a \<Rightarrow> ('action,'state)ioa) \<Rightarrow> bool"
  ioa_composition  ::"('a \<Rightarrow> ('action, 'state)ioa) \<Rightarrow> ('action,'a \<Rightarrow> 'state)ioa"


(* binary composition of action signatures and automata *)

definition compat_asigs ::"['action signature, 'action signature] => bool"
  where "compat_asigs a1 a2 ==
   (((outputs(a1) Int outputs(a2)) = {}) \<and>
    ((internals(a1) Int actions(a2)) = {}) \<and>
    ((internals(a2) Int actions(a1)) = {}))"

definition compat_ioas  ::"[('action,'s)ioa, ('action,'t)ioa] \<Rightarrow> bool"
  where "compat_ioas ioa1 ioa2 \<equiv> compat_asigs (asig_of(ioa1)) (asig_of(ioa2))"

definition asig_comp :: "['action signature, 'action signature] \<Rightarrow> 'action signature"
  where "asig_comp a1 a2 \<equiv>
      (((inputs(a1) \<union> inputs(a2)) - (outputs(a1) \<union> outputs(a2)),
        (outputs(a1) \<union> outputs(a2)),
        (internals(a1) \<union> internals(a2))))"

definition par :: "[('a,'s)ioa, ('a,'t)ioa] \<Rightarrow> ('a,'s*'t)ioa"  (infixr \<open>||\<close> 10)
  where "(ioa1 || ioa2) \<equiv>
     (asig_comp (asig_of ioa1) (asig_of ioa2),
      {pr. fst(pr) \<in> starts_of(ioa1) \<and> snd(pr) \<in> starts_of(ioa2)},
      {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))
           in (a \<in> actions(asig_of(ioa1)) | a \<in> actions(asig_of(ioa2))) &
              (if a \<in> actions(asig_of(ioa1)) then
                 (fst(s),a,fst(t)) \<in> trans_of(ioa1)
               else fst(t) = fst(s))
              &
              (if a \<in> actions(asig_of(ioa2)) then
                 (snd(s),a,snd(t)) \<in> trans_of(ioa2)
               else snd(t) = snd(s))})"


(* Filtering and hiding *)

(* Restrict the trace to those members of the set s *)
definition filter_oseq :: "('a => bool) => 'a oseq => 'a oseq"
  where "filter_oseq p s \<equiv>
   (\<lambda>i. case s(i)
         of None \<Rightarrow> None
          | Some(x) \<Rightarrow> if p x then Some x else None)"

definition mk_trace :: "[('action,'state)ioa, 'action oseq] \<Rightarrow> 'action oseq"
  where "mk_trace(ioa) \<equiv> filter_oseq(\<lambda>a. a \<in> externals(asig_of(ioa)))"

(* Does an ioa have an execution with the given trace *)
definition has_trace :: "[('action,'state)ioa, 'action oseq] \<Rightarrow> bool"
  where "has_trace ioa b \<equiv> (\<exists>ex\<in>executions(ioa). b = mk_trace ioa (fst ex))"

definition NF :: "'a oseq => 'a oseq"
  where "NF(tr) \<equiv> SOME nf. \<exists>f. mono(f) \<and> (\<forall>i. nf(i)=tr(f(i))) \<and>
                    (\<forall>j. j \<notin> range(f) \<longrightarrow> nf(j)= None) &
                    (\<forall>i. nf(i)=None --> (nf (Suc i)) = None)"

(* All the traces of an ioa *)
definition traces :: "('action,'state)ioa => 'action oseq set"
  where "traces(ioa) \<equiv> {trace. \<exists>tr. trace=NF(tr) \<and> has_trace ioa tr}"


definition restrict_asig :: "['a signature, 'a set] => 'a signature"
  where "restrict_asig asig actns \<equiv>
    (inputs(asig) \<inter> actns, outputs(asig) \<inter> actns,
     internals(asig) \<union> (externals(asig) - actns))"

definition restrict :: "[('a,'s)ioa, 'a set] => ('a,'s)ioa"
  where "restrict ioa actns \<equiv>
    (restrict_asig (asig_of ioa) actns, starts_of(ioa), trans_of(ioa))"



(* Notions of correctness *)

definition ioa_implements :: "[('action,'state1)ioa, ('action,'state2)ioa] => bool"
  where "ioa_implements ioa1 ioa2 \<equiv>
  ((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) \<and>
     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2))) \<and>
      traces(ioa1) \<subseteq> traces(ioa2))"


(* Instantiation of abstract IOA by concrete actions *)

definition rename :: "('a, 'b)ioa \<Rightarrow> ('c \<Rightarrow> 'a option) \<Rightarrow> ('c,'b)ioa"
  where "rename ioa ren \<equiv>
    (({b. \<exists>x. Some(x)= ren(b) \<and> x \<in> inputs(asig_of(ioa))},
      {b. \<exists>x. Some(x)= ren(b) \<and> x \<in> outputs(asig_of(ioa))},
      {b. \<exists>x. Some(x)= ren(b) \<and> x \<in> internals(asig_of(ioa))}),
                starts_of(ioa)   ,
     {tr. let s = fst(tr); a = fst(snd(tr));  t = snd(snd(tr))
          in
          \<exists>x. Some(x) = ren(a) \<and> (s,x,t) \<in> trans_of(ioa)})"


declare Let_def [simp]

lemmas ioa_projections = asig_of_def starts_of_def trans_of_def
  and exec_rws = executions_def is_execution_fragment_def

lemma ioa_triple_proj:
    "asig_of(x,y,z) = x & starts_of(x,y,z) = y & trans_of(x,y,z) = z"
  apply (simp add: ioa_projections)
  done

lemma trans_in_actions:
  "[| IOA(A); (s1,a,s2) \<in> trans_of(A) |] ==> a \<in> actions(asig_of(A))"
  apply (unfold IOA_def state_trans_def actions_def is_asig_def)
  apply (erule conjE)+
  apply (erule allE, erule impE, assumption)
  apply simp
  done


lemma filter_oseq_idemp: "filter_oseq p (filter_oseq p s) = filter_oseq p s"
  apply (simp add: filter_oseq_def)
  apply (rule ext)
  apply (case_tac "s i")
  apply simp_all
  done

lemma mk_trace_thm:
"(mk_trace A s n = None) =
   (s(n)=None | (\<exists>a. s(n)=Some(a) \<and> a \<notin> externals(asig_of(A))))
   &
   (mk_trace A s n = Some(a)) =
    (s(n)=Some(a) \<and> a \<in> externals(asig_of(A)))"
  apply (unfold mk_trace_def filter_oseq_def)
  apply (case_tac "s n")
  apply auto
  done

lemma reachable_0: "s \<in> starts_of(A) \<Longrightarrow> reachable A s"
  apply (unfold reachable_def)
  apply (rule_tac x = "(%i. None, %i. s)" in bexI)
  apply simp
  apply (simp add: exec_rws)
  done

lemma reachable_n:
  "\<And>A. [| reachable A s; (s,a,t) \<in> trans_of(A) |] ==> reachable A t"
  apply (unfold reachable_def exec_rws)
  apply (simp del: bex_simps)
  apply (simp (no_asm_simp) only: split_tupled_all)
  apply safe
  apply (rename_tac ex1 ex2 n)
  apply (rule_tac x = "(%i. if i<n then ex1 i else (if i=n then Some a else None) , %i. if i<Suc n then ex2 i else t)" in bexI)
   apply (rule_tac x = "Suc n" in exI)
   apply (simp (no_asm))
  apply simp
  apply (metis ioa_triple_proj less_antisym)
  done


lemma invariantI:
  assumes p1: "\<And>s. s \<in> starts_of(A) \<Longrightarrow> P(s)"
    and p2: "\<And>s t a. [|reachable A s; P(s)|] ==> (s,a,t) \<in> trans_of(A) \<longrightarrow> P(t)"
  shows "invariant A P"
  apply (unfold invariant_def reachable_def Let_def exec_rws)
  apply safe
  apply (rename_tac ex1 ex2 n)
  apply (rule_tac Q = "reachable A (ex2 n) " in conjunct1)
  apply simp
  apply (induct_tac n)
   apply (fast intro: p1 reachable_0)
  apply (erule_tac x = na in allE)
  apply (case_tac "ex1 na", simp_all)
  apply safe
   apply (erule p2 [THEN mp])
    apply (fast dest: reachable_n)+
  done

lemma invariantI1:
 "[| \<And>s. s \<in> starts_of(A) \<Longrightarrow> P(s);
     \<And>s t a. reachable A s \<Longrightarrow> P(s) \<longrightarrow> (s,a,t) \<in> trans_of(A) \<longrightarrow> P(t)
  |] ==> invariant A P"
  apply (blast intro!: invariantI)
  done

lemma invariantE:
  "[| invariant A P; reachable A s |] ==> P(s)"
  apply (unfold invariant_def)
  apply blast
  done

lemma actions_asig_comp:
  "actions(asig_comp a b) = actions(a) \<union> actions(b)"
  apply (auto simp add: actions_def asig_comp_def asig_projections)
  done

lemma starts_of_par:
  "starts_of(A || B) = {p. fst(p) \<in> starts_of(A) \<and> snd(p) \<in> starts_of(B)}"
  apply (simp add: par_def ioa_projections)
  done

(* Every state in an execution is reachable *)
lemma states_of_exec_reachable:
  "ex \<in> executions(A) \<Longrightarrow> \<forall>n. reachable A (snd ex n)"
  apply (unfold reachable_def)
  apply fast
  done


lemma trans_of_par4:
"(s,a,t) \<in> trans_of(A || B || C || D) =
  ((a \<in> actions(asig_of(A)) | a \<in> actions(asig_of(B)) | a \<in> actions(asig_of(C)) |
    a \<in> actions(asig_of(D))) \<and>
   (if a \<in> actions(asig_of(A)) then (fst(s),a,fst(t)) \<in> trans_of(A)
    else fst t=fst s) \<and>
   (if a \<in> actions(asig_of(B)) then (fst(snd(s)),a,fst(snd(t))) \<in> trans_of(B)
    else fst(snd(t))=fst(snd(s))) \<and>
   (if a \<in> actions(asig_of(C)) then
      (fst(snd(snd(s))),a,fst(snd(snd(t)))) \<in> trans_of(C)
    else fst(snd(snd(t)))=fst(snd(snd(s)))) \<and>
   (if a \<in> actions(asig_of(D)) then
      (snd(snd(snd(s))),a,snd(snd(snd(t)))) \<in> trans_of(D)
    else snd(snd(snd(t)))=snd(snd(snd(s)))))"
  (*SLOW*)
  apply (simp (no_asm) add: par_def actions_asig_comp prod_eq_iff ioa_projections)
  done

lemma cancel_restrict: "starts_of(restrict ioa acts) = starts_of(ioa) &
              trans_of(restrict ioa acts) = trans_of(ioa) &
              reachable (restrict ioa acts) s = reachable ioa s"
  apply (simp add: is_execution_fragment_def executions_def
    reachable_def restrict_def ioa_projections)
  done

lemma asig_of_par: "asig_of(A || B) = asig_comp (asig_of A) (asig_of B)"
  apply (simp add: par_def ioa_projections)
  done


lemma externals_of_par: "externals(asig_of(A1||A2)) =
   (externals(asig_of(A1)) \<union> externals(asig_of(A2)))"
  apply (simp add: externals_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def Un_def set_diff_eq)
  apply blast
  done

lemma ext1_is_not_int2:
  "[| compat_ioas A1 A2; a \<in> externals(asig_of(A1))|] ==> a \<notin> internals(asig_of(A2))"
  apply (unfold externals_def actions_def compat_ioas_def compat_asigs_def)
  apply auto
  done

lemma ext2_is_not_int1:
 "[| compat_ioas A2 A1 ; a \<in> externals(asig_of(A1))|] ==> a \<notin> internals(asig_of(A2))"
  apply (unfold externals_def actions_def compat_ioas_def compat_asigs_def)
  apply auto
  done

lemmas ext1_ext2_is_not_act2 = ext1_is_not_int2 [THEN int_and_ext_is_act]
  and ext1_ext2_is_not_act1 = ext2_is_not_int1 [THEN int_and_ext_is_act]

end
