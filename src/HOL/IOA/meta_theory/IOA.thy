(*  Title:      HOL/IOA/meta_theory/IOA.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

The I/O automata of Lynch and Tuttle.
*)

IOA = Asig +

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
  IOA	     ::"('action,'state)ioa => bool"

  (* Executions, schedules, and traces *)

  is_execution_fragment,
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
  "||"         ::"[('a,'s)ioa, ('a,'t)ioa] => ('a,'s*'t)ioa"  (infixr 10)

  (* Filtering and hiding *)
  filter_oseq  :: "('a => bool) => 'a oseq => 'a oseq"

  restrict_asig :: "['a signature, 'a set] => 'a signature"
  restrict      :: "[('a,'s)ioa, 'a set] => ('a,'s)ioa"

  (* Notions of correctness *)
  ioa_implements :: "[('action,'state1)ioa, ('action,'state2)ioa] => bool"

  (* Instantiation of abstract IOA by concrete actions *)
  rename:: "('a, 'b)ioa => ('c => 'a option) => ('c,'b)ioa"

defs

state_trans_def
  "state_trans asig R == \
  \  (!triple. triple:R --> fst(snd(triple)):actions(asig)) & \
  \  (!a. (a:inputs(asig)) --> (!s1. ? s2. (s1,a,s2):R))"


asig_of_def   "asig_of == fst"
starts_of_def "starts_of == (fst o snd)"
trans_of_def  "trans_of == (snd o snd)"

ioa_def
  "IOA(ioa) == (is_asig(asig_of(ioa))      &                            \
  \             (~ starts_of(ioa) = {})    &                            \
  \             state_trans (asig_of ioa) (trans_of ioa))"


(* An execution fragment is modelled with a pair of sequences:
 * the first is the action options, the second the state sequence.
 * Finite executions have None actions from some point on.
 *******)
is_execution_fragment_def
  "is_execution_fragment A ex ==                                        \
  \  let act = fst(ex); state = snd(ex)                                 \
  \  in !n a. (act(n)=None --> state(Suc(n)) = state(n)) &              \
  \           (act(n)=Some(a) --> (state(n),a,state(Suc(n))):trans_of(A))"


executions_def
  "executions(ioa) == {e. snd e 0:starts_of(ioa) &                      \
\                        is_execution_fragment ioa e}"

  
reachable_def
  "reachable ioa s == (? ex:executions(ioa). ? n. (snd ex n) = s)"


invariant_def "invariant A P == (!s. reachable A s --> P(s))"


(* Restrict the trace to those members of the set s *)
filter_oseq_def
  "filter_oseq p s ==                                                   \
\   (%i.case s(i)                                                       \
\         of None => None                                               \
\          | Some(x) => if p x then Some x else None)"


mk_trace_def
  "mk_trace(ioa) == filter_oseq(%a.a:externals(asig_of(ioa)))"


(* Does an ioa have an execution with the given trace *)
has_trace_def
  "has_trace ioa b ==                                               \
\     (? ex:executions(ioa). b = mk_trace ioa (fst ex))"

normal_form_def
  "NF(tr) == @nf. ? f. mono(f) & (!i. nf(i)=tr(f(i))) &   \
\                    (!j. j ~: range(f) --> nf(j)= None) &   \
\                    (!i. nf(i)=None --> (nf (Suc i)) = None)   "
  
(* All the traces of an ioa *)

  traces_def
  "traces(ioa) == {trace. ? tr. trace=NF(tr) & has_trace ioa tr}"

(*
  traces_def
  "traces(ioa) == {tr. has_trace ioa tr}"
*)
  
compat_asigs_def
  "compat_asigs a1 a2 ==                                                \
 \ (((outputs(a1) Int outputs(a2)) = {}) &                              \
 \  ((internals(a1) Int actions(a2)) = {}) &                            \
 \  ((internals(a2) Int actions(a1)) = {}))"


compat_ioas_def
  "compat_ioas ioa1 ioa2 == compat_asigs (asig_of(ioa1)) (asig_of(ioa2))"


asig_comp_def
  "asig_comp a1 a2 ==                                                   \
  \   (((inputs(a1) Un inputs(a2)) - (outputs(a1) Un outputs(a2)),      \
  \     (outputs(a1) Un outputs(a2)),                                   \
  \     (internals(a1) Un internals(a2))))"


par_def
  "(ioa1 || ioa2) ==                                                    \
  \    (asig_comp (asig_of ioa1) (asig_of ioa2),                        \
  \     {pr. fst(pr):starts_of(ioa1) & snd(pr):starts_of(ioa2)},        \
  \     {tr. let s = fst(tr); a = fst(snd(tr)); t = snd(snd(tr))        \
  \          in (a:actions(asig_of(ioa1)) | a:actions(asig_of(ioa2))) & \
  \             (if a:actions(asig_of(ioa1)) then                       \
  \                (fst(s),a,fst(t)):trans_of(ioa1)                     \
  \              else fst(t) = fst(s))                                  \
  \             &                                                       \
  \             (if a:actions(asig_of(ioa2)) then                       \
  \                (snd(s),a,snd(t)):trans_of(ioa2)                     \
  \              else snd(t) = snd(s))})"


restrict_asig_def
  "restrict_asig asig actns ==                                          \
\    (inputs(asig) Int actns, outputs(asig) Int actns,                  \
\     internals(asig) Un (externals(asig) - actns))"


restrict_def
  "restrict ioa actns ==                                               \
\    (restrict_asig (asig_of ioa) actns, starts_of(ioa), trans_of(ioa))"


ioa_implements_def
  "ioa_implements ioa1 ioa2 ==   \
\  ((inputs(asig_of(ioa1)) = inputs(asig_of(ioa2))) &   \
\     (outputs(asig_of(ioa1)) = outputs(asig_of(ioa2))) &   \
\      traces(ioa1) <= traces(ioa2))"
 
rename_def 
"rename ioa ren ==  \
\  (({b. ? x. Some(x)= ren(b) & x : inputs(asig_of(ioa))},         \
\    {b. ? x. Some(x)= ren(b) & x : outputs(asig_of(ioa))},        \
\    {b. ? x. Some(x)= ren(b) & x : internals(asig_of(ioa))}),     \
\              starts_of(ioa)   ,                                            \
\   {tr. let s = fst(tr); a = fst(snd(tr));  t = snd(snd(tr))    \
\        in                                                      \
\        ? x. Some(x) = ren(a) & (s,x,t):trans_of(ioa)})"

end 
