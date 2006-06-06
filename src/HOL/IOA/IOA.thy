(*  Title:      HOL/IOA/IOA.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen
*)

header {* The I/O automata of Lynch and Tuttle *}

theory IOA
imports Asig
begin

types
   'a seq            =   "nat => 'a"
   'a oseq           =   "nat => 'a option"
   ('a,'b)execution  =   "'a oseq * 'b seq"
   ('a,'s)transition =   "('s * 'a * 's)"
   ('a,'s)ioa        =   "'a signature * 's set * ('a,'s)transition set"

consts

  (* IO automata *)
  state_trans::"['action signature, ('action,'state)transition set] => bool"
  asig_of    ::"('action,'state)ioa => 'action signature"
  starts_of  ::"('action,'state)ioa => 'state set"
  trans_of   ::"('action,'state)ioa => ('action,'state)transition set"
  IOA        ::"('action,'state)ioa => bool"

  (* Executions, schedules, and traces *)

  is_execution_fragment ::"[('action,'state)ioa, ('action,'state)execution] => bool"
  has_execution ::"[('action,'state)ioa, ('action,'state)execution] => bool"
  executions    :: "('action,'state)ioa => ('action,'state)execution set"
  mk_trace  :: "[('action,'state)ioa, 'action oseq] => 'action oseq"
  reachable     :: "[('action,'state)ioa, 'state] => bool"
  invariant     :: "[('action,'state)ioa, 'state=>bool] => bool"
  has_trace :: "[('action,'state)ioa, 'action oseq] => bool"
  traces    :: "('action,'state)ioa => 'action oseq set"
  NF            :: "'a oseq => 'a oseq"

  (* Composition of action signatures and automata *)
  compatible_asigs ::"('a => 'action signature) => bool"
  asig_composition ::"('a => 'action signature) => 'action signature"
  compatible_ioas  ::"('a => ('action,'state)ioa) => bool"
  ioa_composition  ::"('a => ('action, 'state)ioa) =>('action,'a => 'state)ioa"

  (* binary composition of action signatures and automata *)
  compat_asigs ::"['action signature, 'action signature] => bool"
  asig_comp    ::"['action signature, 'action signature] => 'action signature"
  compat_ioas  ::"[('action,'s)ioa, ('action,'t)ioa] => bool"
  par         ::"[('a,'s)ioa, ('a,'t)ioa] => ('a,'s*'t)ioa"  (infixr "||" 10)

  (* Filtering and hiding *)
  filter_oseq  :: "('a => bool) => 'a oseq => 'a oseq"

  restrict_asig :: "['a signature, 'a set] => 'a signature"
  restrict      :: "[('a,'s)ioa, 'a set] => ('a,'s)ioa"

  (* Notions of correctness *)
  ioa_implements :: "[('action,'state1)ioa, ('action,'state2)ioa] => bool"

  (* Instantiation of abstract IOA by concrete actions *)
  rename:: "('a, 'b)ioa => ('c => 'a option) => ('c,'b)ioa"

defs

state_trans_def:
  "state_trans asig R ==
     (!triple. triple:R --> fst(snd(triple)):actions(asig)) &
     (!a. (a:inputs(asig)) --> (!s1. ? s2. (s1,a,s2):R))"


asig_of_def:   "asig_of == fst"
starts_of_def: "starts_of == (fst o snd)"
trans_of_def:  "trans_of == (snd o snd)"

ioa_def:
  "IOA(ioa) == (is_asig(asig_of(ioa))      &
                (~ starts_of(ioa) = {})    &
                state_trans (asig_of ioa) (trans_of ioa))"


(* An execution fragment is modelled with a pair of sequences:
 * the first is the action options, the second the state sequence.
 * Finite executions have None actions from some point on.
 *******)
is_execution_fragment_def:
  "is_execution_fragment A ex ==
     let act = fst(ex); state = snd(ex)
     in !n a. (act(n)=None --> state(Suc(n)) = state(n)) &
              (act(n)=Some(a) --> (state(n),a,state(Suc(n))):trans_of(A))"


executions_def:
  "executions(ioa) == {e. snd e 0:starts_of(ioa) &
                        is_execution_fragment ioa e}"


reachable_def:
  "reachable ioa s == (? ex:executions(ioa). ? n. (snd ex n) = s)"


invariant_def: "invariant A P == (!s. reachable A s --> P(s))"


(* Restrict the trace to those members of the set s *)
filter_oseq_def:
  "filter_oseq p s ==
   (%i. case s(i)
         of None => None
          | Some(x) => if p x then Some x else None)"


mk_trace_def:
  "mk_trace(ioa) == filter_oseq(%a. a:externals(asig_of(ioa)))"


(* Does an ioa have an execution with the given trace *)
has_trace_def:
  "has_trace ioa b ==
     (? ex:executions(ioa). b = mk_trace ioa (fst ex))"

normal_form_def:
  "NF(tr) == @nf. ? f. mono(f) & (!i. nf(i)=tr(f(i))) &
                    (!j. j ~: range(f) --> nf(j)= None) &
                    (!i. nf(i)=None --> (nf (Suc i)) = None)   "

(* All the traces of an ioa *)

  traces_def:
  "traces(ioa) == {trace. ? tr. trace=NF(tr) & has_trace ioa tr}"

(*
  traces_def:
  "traces(ioa) == {tr. has_trace ioa tr}"
*)

compat_asigs_def:
  "compat_asigs a1 a2 ==
   (((outputs(a1) Int outputs(a2)) = {}) &
    ((internals(a1) Int actions(a2)) = {}) &
    ((internals(a2) Int actions(a1)) = {}))"


compat_ioas_def:
  "compat_ioas ioa1 ioa2 == compat_asigs (asig_of(ioa1)) (asig_of(ioa2))"


asig_comp_def:
  "asig_comp a1 a2 ==
      (((inputs(a1) Un inputs(a2)) - (outputs(a1) Un outputs(a2)),
        (outputs(a1) Un outputs(a2)),
        (internals(a1) Un internals(a2))))"


par_def:
  "(ioa1 || ioa2) ==
       (asig_comp (asig_of ioa1) (asig_of ioa2),
        {pr. fst(pr):starts_of(ioa1) & snd(pr):starts_of(ioa2)},
        {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))
             in (a:actions(asig_of(ioa1)) | a:actions(asig_of(ioa2))) &
                (if a:actions(asig_of(ioa1)) then
                   (fst(s),a,fst(t)):trans_of(ioa1)
                 else fst(t) = fst(s))
                &
                (if a:actions(asig_of(ioa2)) then
                   (snd(s),a,snd(t)):trans_of(ioa2)
                 else snd(t) = snd(s))})"


restrict_asig_def:
  "restrict_asig asig actns ==
    (inputs(asig) Int actns, outputs(asig) Int actns,
     internals(asig) Un (externals(asig) - actns))"


restrict_def:
  "restrict ioa actns ==
    (restrict_asig (asig_of ioa) actns, starts_of(ioa), trans_of(ioa))"


ioa_implements_def:
  "ioa_implements ioa1 ioa2 ==
  ((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) &
     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2))) &
      traces(ioa1) <= traces(ioa2))"

rename_def:
"rename ioa ren ==
  (({b. ? x. Some(x)= ren(b) & x : inputs(asig_of(ioa))},
    {b. ? x. Some(x)= ren(b) & x : outputs(asig_of(ioa))},
    {b. ? x. Some(x)= ren(b) & x : internals(asig_of(ioa))}),
              starts_of(ioa)   ,
   {tr. let s = fst(tr); a = fst(snd(tr));  t = snd(snd(tr))
        in
        ? x. Some(x) = ren(a) & (s,x,t):trans_of(ioa)})"


declare Let_def [simp]

lemmas ioa_projections = asig_of_def starts_of_def trans_of_def
  and exec_rws = executions_def is_execution_fragment_def

lemma ioa_triple_proj:
    "asig_of(x,y,z) = x & starts_of(x,y,z) = y & trans_of(x,y,z) = z"
  apply (simp add: ioa_projections)
  done

lemma trans_in_actions:
  "[| IOA(A); (s1,a,s2):trans_of(A) |] ==> a:actions(asig_of(A))"
  apply (unfold ioa_def state_trans_def actions_def is_asig_def)
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
   (s(n)=None | (? a. s(n)=Some(a) & a ~: externals(asig_of(A))))
   &
   (mk_trace A s n = Some(a)) =
    (s(n)=Some(a) & a : externals(asig_of(A)))"
  apply (unfold mk_trace_def filter_oseq_def)
  apply (case_tac "s n")
  apply auto
  done

lemma reachable_0: "s:starts_of(A) ==> reachable A s"
  apply (unfold reachable_def)
  apply (rule_tac x = "(%i. None, %i. s)" in bexI)
  apply simp
  apply (simp add: exec_rws)
  done

lemma reachable_n:
  "!!A. [| reachable A s; (s,a,t) : trans_of(A) |] ==> reachable A t"
  apply (unfold reachable_def exec_rws)
  apply (simp del: bex_simps)
  apply (simp (no_asm_simp) only: split_tupled_all)
  apply safe
  apply (rename_tac ex1 ex2 n)
  apply (rule_tac x = "(%i. if i<n then ex1 i else (if i=n then Some a else None) , %i. if i<Suc n then ex2 i else t)" in bexI)
   apply (rule_tac x = "Suc n" in exI)
   apply (simp (no_asm))
  apply simp
  apply (rule allI)
  apply (cut_tac m = "na" and n = "n" in less_linear)
  apply auto
  done


lemma invariantI:
  assumes p1: "!!s. s:starts_of(A) ==> P(s)"
    and p2: "!!s t a. [|reachable A s; P(s)|] ==> (s,a,t): trans_of(A) --> P(t)"
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
 "[| !!s. s : starts_of(A) ==> P(s);
     !!s t a. reachable A s ==> P(s) --> (s,a,t):trans_of(A) --> P(t)
  |] ==> invariant A P"
  apply (blast intro!: invariantI)
  done

lemma invariantE:
  "[| invariant A P; reachable A s |] ==> P(s)"
  apply (unfold invariant_def)
  apply blast
  done

lemma actions_asig_comp:
  "actions(asig_comp a b) = actions(a) Un actions(b)"
  apply (auto simp add: actions_def asig_comp_def asig_projections)
  done

lemma starts_of_par:
  "starts_of(A || B) = {p. fst(p):starts_of(A) & snd(p):starts_of(B)}"
  apply (simp add: par_def ioa_projections)
  done

(* Every state in an execution is reachable *)
lemma states_of_exec_reachable:
  "ex:executions(A) ==> !n. reachable A (snd ex n)"
  apply (unfold reachable_def)
  apply fast
  done


lemma trans_of_par4:
"(s,a,t) : trans_of(A || B || C || D) =
  ((a:actions(asig_of(A)) | a:actions(asig_of(B)) | a:actions(asig_of(C)) |
    a:actions(asig_of(D))) &
   (if a:actions(asig_of(A)) then (fst(s),a,fst(t)):trans_of(A)
    else fst t=fst s) &
   (if a:actions(asig_of(B)) then (fst(snd(s)),a,fst(snd(t))):trans_of(B)
    else fst(snd(t))=fst(snd(s))) &
   (if a:actions(asig_of(C)) then
      (fst(snd(snd(s))),a,fst(snd(snd(t)))):trans_of(C)
    else fst(snd(snd(t)))=fst(snd(snd(s)))) &
   (if a:actions(asig_of(D)) then
      (snd(snd(snd(s))),a,snd(snd(snd(t)))):trans_of(D)
    else snd(snd(snd(t)))=snd(snd(snd(s)))))"
  (*SLOW*)
  apply (simp (no_asm) add: par_def actions_asig_comp Pair_fst_snd_eq ioa_projections)
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
   (externals(asig_of(A1)) Un externals(asig_of(A2)))"
  apply (simp add: externals_def asig_of_par asig_comp_def
    asig_inputs_def asig_outputs_def Un_def set_diff_def)
  apply blast
  done

lemma ext1_is_not_int2:
  "[| compat_ioas A1 A2; a:externals(asig_of(A1))|] ==> a~:internals(asig_of(A2))"
  apply (unfold externals_def actions_def compat_ioas_def compat_asigs_def)
  apply auto
  done

lemma ext2_is_not_int1:
 "[| compat_ioas A2 A1 ; a:externals(asig_of(A1))|] ==> a~:internals(asig_of(A2))"
  apply (unfold externals_def actions_def compat_ioas_def compat_asigs_def)
  apply auto
  done

lemmas ext1_ext2_is_not_act2 = ext1_is_not_int2 [THEN int_and_ext_is_act]
  and ext1_ext2_is_not_act1 = ext2_is_not_int1 [THEN int_and_ext_is_act]

end
