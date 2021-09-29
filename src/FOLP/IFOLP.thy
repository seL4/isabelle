(*  Title:      FOLP/IFOLP.thy
    Author:     Martin D Coen, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge
*)

section \<open>Intuitionistic First-Order Logic with Proofs\<close>

theory IFOLP
imports Pure
begin

ML_file \<open>~~/src/Tools/misc_legacy.ML\<close>

setup Pure_Thy.old_appl_syntax_setup
setup \<open>Proofterm.set_preproc (Proof_Rewrite_Rules.standard_preproc [])\<close>

class "term"
default_sort "term"

typedecl p
typedecl o

consts
      (*** Judgements ***)
 Proof          ::   "[o,p]=>prop"
 EqProof        ::   "[p,p,o]=>prop"    ("(3_ /= _ :/ _)" [10,10,10] 5)

      (*** Logical Connectives -- Type Formers ***)
 eq             ::      "['a,'a] => o"  (infixl "=" 50)
 True           ::      "o"
 False          ::      "o"
 conj           ::      "[o,o] => o"    (infixr "&" 35)
 disj           ::      "[o,o] => o"    (infixr "|" 30)
 imp            ::      "[o,o] => o"    (infixr "-->" 25)
      (*Quantifiers*)
 All            ::      "('a => o) => o"        (binder "ALL " 10)
 Ex             ::      "('a => o) => o"        (binder "EX " 10)
      (*Rewriting gadgets*)
 NORM           ::      "o => o"
 norm           ::      "'a => 'a"

      (*** Proof Term Formers: precedence must exceed 50 ***)
 tt             :: "p"
 contr          :: "p=>p"
 fst            :: "p=>p"
 snd            :: "p=>p"
 pair           :: "[p,p]=>p"           ("(1<_,/_>)")
 split          :: "[p, [p,p]=>p] =>p"
 inl            :: "p=>p"
 inr            :: "p=>p"
 "when"         :: "[p, p=>p, p=>p]=>p"
 lambda         :: "(p => p) => p"      (binder "lam " 55)
 App            :: "[p,p]=>p"           (infixl "`" 60)
 alll           :: "['a=>p]=>p"         (binder "all " 55)
 app            :: "[p,'a]=>p"          (infixl "^" 55)
 exists         :: "['a,p]=>p"          ("(1[_,/_])")
 xsplit         :: "[p,['a,p]=>p]=>p"
 ideq           :: "'a=>p"
 idpeel         :: "[p,'a=>p]=>p"
 nrm            :: p
 NRM            :: p

syntax "_Proof" :: "[p,o]=>prop"    ("(_ /: _)" [51, 10] 5)

parse_translation \<open>
  let fun proof_tr [p, P] = Syntax.const \<^const_syntax>\<open>Proof\<close> $ P $ p
  in [(\<^syntax_const>\<open>_Proof\<close>, K proof_tr)] end
\<close>

(*show_proofs = true displays the proof terms -- they are ENORMOUS*)
ML \<open>val show_proofs = Attrib.setup_config_bool \<^binding>\<open>show_proofs\<close> (K false)\<close>

print_translation \<open>
  let
    fun proof_tr' ctxt [P, p] =
      if Config.get ctxt show_proofs then Syntax.const \<^syntax_const>\<open>_Proof\<close> $ p $ P
      else P
  in [(\<^const_syntax>\<open>Proof\<close>, proof_tr')] end
\<close>


(**** Propositional logic ****)

(*Equality*)
(* Like Intensional Equality in MLTT - but proofs distinct from terms *)

axiomatization where
ieqI:      "ideq(a) : a=a" and
ieqE:      "[| p : a=b;  !!x. f(x) : P(x,x) |] ==> idpeel(p,f) : P(a,b)"

(* Truth and Falsity *)

axiomatization where
TrueI:     "tt : True" and
FalseE:    "a:False ==> contr(a):P"

(* Conjunction *)

axiomatization where
conjI:     "[| a:P;  b:Q |] ==> <a,b> : P&Q" and
conjunct1: "p:P&Q ==> fst(p):P" and
conjunct2: "p:P&Q ==> snd(p):Q"

(* Disjunction *)

axiomatization where
disjI1:    "a:P ==> inl(a):P|Q" and
disjI2:    "b:Q ==> inr(b):P|Q" and
disjE:     "[| a:P|Q;  !!x. x:P ==> f(x):R;  !!x. x:Q ==> g(x):R
           |] ==> when(a,f,g):R"

(* Implication *)

axiomatization where
impI:      "\<And>P Q f. (!!x. x:P ==> f(x):Q) ==> lam x. f(x):P-->Q" and
mp:        "\<And>P Q f. [| f:P-->Q;  a:P |] ==> f`a:Q"

(*Quantifiers*)

axiomatization where
allI:      "\<And>P. (!!x. f(x) : P(x)) ==> all x. f(x) : ALL x. P(x)" and
spec:      "\<And>P f. (f:ALL x. P(x)) ==> f^x : P(x)"

axiomatization where
exI:       "p : P(x) ==> [x,p] : EX x. P(x)" and
exE:       "[| p: EX x. P(x);  !!x u. u:P(x) ==> f(x,u) : R |] ==> xsplit(p,f):R"

(**** Equality between proofs ****)

axiomatization where
prefl:     "a : P ==> a = a : P" and
psym:      "a = b : P ==> b = a : P" and
ptrans:    "[| a = b : P;  b = c : P |] ==> a = c : P"

axiomatization where
idpeelB:   "[| !!x. f(x) : P(x,x) |] ==> idpeel(ideq(a),f) = f(a) : P(a,a)"

axiomatization where
fstB:      "a:P ==> fst(<a,b>) = a : P" and
sndB:      "b:Q ==> snd(<a,b>) = b : Q" and
pairEC:    "p:P&Q ==> p = <fst(p),snd(p)> : P&Q"

axiomatization where
whenBinl:  "[| a:P;  !!x. x:P ==> f(x) : Q |] ==> when(inl(a),f,g) = f(a) : Q" and
whenBinr:  "[| b:P;  !!x. x:P ==> g(x) : Q |] ==> when(inr(b),f,g) = g(b) : Q" and
plusEC:    "a:P|Q ==> when(a,%x. inl(x),%y. inr(y)) = a : P|Q"

axiomatization where
applyB:     "[| a:P;  !!x. x:P ==> b(x) : Q |] ==> (lam x. b(x)) ` a = b(a) : Q" and
funEC:      "f:P ==> f = lam x. f`x : P"

axiomatization where
specB:      "[| !!x. f(x) : P(x) |] ==> (all x. f(x)) ^ a = f(a) : P(a)"


(**** Definitions ****)

definition Not :: "o => o"  ("~ _" [40] 40)
  where not_def: "~P == P-->False"

definition iff :: "[o,o] => o"  (infixr "<->" 25)
  where "P<->Q == (P-->Q) & (Q-->P)"

(*Unique existence*)
definition Ex1 :: "('a => o) => o"  (binder "EX! " 10)
  where ex1_def: "EX! x. P(x) == EX x. P(x) & (ALL y. P(y) --> y=x)"

(*Rewriting -- special constants to flag normalized terms and formulae*)
axiomatization where
norm_eq: "nrm : norm(x) = x" and
NORM_iff:        "NRM : NORM(P) <-> P"

(*** Sequent-style elimination rules for & --> and ALL ***)

schematic_goal conjE:
  assumes "p:P&Q"
    and "!!x y.[| x:P; y:Q |] ==> f(x,y):R"
  shows "?a:R"
  apply (rule assms(2))
   apply (rule conjunct1 [OF assms(1)])
  apply (rule conjunct2 [OF assms(1)])
  done

schematic_goal impE:
  assumes "p:P-->Q"
    and "q:P"
    and "!!x. x:Q ==> r(x):R"
  shows "?p:R"
  apply (rule assms mp)+
  done

schematic_goal allE:
  assumes "p:ALL x. P(x)"
    and "!!y. y:P(x) ==> q(y):R"
  shows "?p:R"
  apply (rule assms spec)+
  done

(*Duplicates the quantifier; for use with eresolve_tac*)
schematic_goal all_dupE:
  assumes "p:ALL x. P(x)"
    and "!!y z.[| y:P(x); z:ALL x. P(x) |] ==> q(y,z):R"
  shows "?p:R"
  apply (rule assms spec)+
  done


(*** Negation rules, which translate between ~P and P-->False ***)

schematic_goal notI:
  assumes "!!x. x:P ==> q(x):False"
  shows "?p:~P"
  unfolding not_def
  apply (assumption | rule assms impI)+
  done

schematic_goal notE: "p:~P \<Longrightarrow> q:P \<Longrightarrow> ?p:R"
  unfolding not_def
  apply (drule (1) mp)
  apply (erule FalseE)
  done

(*This is useful with the special implication rules for each kind of P. *)
schematic_goal not_to_imp:
  assumes "p:~P"
    and "!!x. x:(P-->False) ==> q(x):Q"
  shows "?p:Q"
  apply (assumption | rule assms impI notE)+
  done

(* For substitution int an assumption P, reduce Q to P-->Q, substitute into
   this implication, then apply impI to move P back into the assumptions.*)
schematic_goal rev_mp: "[| p:P;  q:P --> Q |] ==> ?p:Q"
  apply (assumption | rule mp)+
  done


(*Contrapositive of an inference rule*)
schematic_goal contrapos:
  assumes major: "p:~Q"
    and minor: "!!y. y:P==>q(y):Q"
  shows "?a:~P"
  apply (rule major [THEN notE, THEN notI])
  apply (erule minor)
  done

(** Unique assumption tactic.
    Ignores proof objects.
    Fails unless one assumption is equal and exactly one is unifiable
**)

ML \<open>
local
  fun discard_proof \<^Const_>\<open>Proof for P _\<close> = P;
in
fun uniq_assume_tac ctxt =
  SUBGOAL
    (fn (prem,i) =>
      let val hyps = map discard_proof (Logic.strip_assums_hyp prem)
          and concl = discard_proof (Logic.strip_assums_concl prem)
      in
          if exists (fn hyp => hyp aconv concl) hyps
          then case distinct (op =) (filter (fn hyp => Term.could_unify (hyp, concl)) hyps) of
                   [_] => assume_tac ctxt i
                 |  _  => no_tac
          else no_tac
      end);
end;
\<close>


(*** Modus Ponens Tactics ***)

(*Finds P-->Q and P in the assumptions, replaces implication by Q *)
ML \<open>
  fun mp_tac ctxt i =
    eresolve_tac ctxt [@{thm notE}, make_elim @{thm mp}] i  THEN  assume_tac ctxt i
\<close>
method_setup mp = \<open>Scan.succeed (SIMPLE_METHOD' o mp_tac)\<close>

(*Like mp_tac but instantiates no variables*)
ML \<open>
  fun int_uniq_mp_tac ctxt i =
    eresolve_tac ctxt [@{thm notE}, @{thm impE}] i  THEN  uniq_assume_tac ctxt i
\<close>


(*** If-and-only-if ***)

schematic_goal iffI:
  assumes "!!x. x:P ==> q(x):Q"
    and "!!x. x:Q ==> r(x):P"
  shows "?p:P<->Q"
  unfolding iff_def
  apply (assumption | rule assms conjI impI)+
  done


schematic_goal iffE:
  assumes "p:P <-> Q"
    and "!!x y.[| x:P-->Q; y:Q-->P |] ==> q(x,y):R"
  shows "?p:R"
  apply (rule conjE)
   apply (rule assms(1) [unfolded iff_def])
  apply (rule assms(2))
   apply assumption+
  done

(* Destruct rules for <-> similar to Modus Ponens *)

schematic_goal iffD1: "[| p:P <-> Q; q:P |] ==> ?p:Q"
  unfolding iff_def
  apply (rule conjunct1 [THEN mp], assumption+)
  done

schematic_goal iffD2: "[| p:P <-> Q; q:Q |] ==> ?p:P"
  unfolding iff_def
  apply (rule conjunct2 [THEN mp], assumption+)
  done

schematic_goal iff_refl: "?p:P <-> P"
  apply (rule iffI)
   apply assumption+
  done

schematic_goal iff_sym: "p:Q <-> P ==> ?p:P <-> Q"
  apply (erule iffE)
  apply (rule iffI)
   apply (erule (1) mp)+
  done

schematic_goal iff_trans: "[| p:P <-> Q; q:Q<-> R |] ==> ?p:P <-> R"
  apply (rule iffI)
   apply (assumption | erule iffE | erule (1) impE)+
  done

(*** Unique existence.  NOTE THAT the following 2 quantifications
   EX!x such that [EX!y such that P(x,y)]     (sequential)
   EX!x,y such that P(x,y)                    (simultaneous)
 do NOT mean the same thing.  The parser treats EX!x y.P(x,y) as sequential.
***)

schematic_goal ex1I:
  assumes "p:P(a)"
    and "!!x u. u:P(x) ==> f(u) : x=a"
  shows "?p:EX! x. P(x)"
  unfolding ex1_def
  apply (assumption | rule assms exI conjI allI impI)+
  done

schematic_goal ex1E:
  assumes "p:EX! x. P(x)"
    and "!!x u v. [| u:P(x);  v:ALL y. P(y) --> y=x |] ==> f(x,u,v):R"
  shows "?a : R"
  apply (insert assms(1) [unfolded ex1_def])
  apply (erule exE conjE | assumption | rule assms(1))+
  apply (erule assms(2), assumption)
  done


(*** <-> congruence rules for simplification ***)

(*Use iffE on a premise.  For conj_cong, imp_cong, all_cong, ex_cong*)
ML \<open>
fun iff_tac ctxt prems i =
    resolve_tac ctxt (prems RL [@{thm iffE}]) i THEN
    REPEAT1 (eresolve_tac ctxt [asm_rl, @{thm mp}] i)
\<close>

method_setup iff =
  \<open>Attrib.thms >> (fn prems => fn ctxt => SIMPLE_METHOD' (iff_tac ctxt prems))\<close>

schematic_goal conj_cong:
  assumes "p:P <-> P'"
    and "!!x. x:P' ==> q(x):Q <-> Q'"
  shows "?p:(P&Q) <-> (P'&Q')"
  apply (insert assms(1))
  apply (assumption | rule iffI conjI | erule iffE conjE mp | iff assms)+
  done

schematic_goal disj_cong:
  "[| p:P <-> P'; q:Q <-> Q' |] ==> ?p:(P|Q) <-> (P'|Q')"
  apply (erule iffE disjE disjI1 disjI2 | assumption | rule iffI | mp)+
  done

schematic_goal imp_cong:
  assumes "p:P <-> P'"
    and "!!x. x:P' ==> q(x):Q <-> Q'"
  shows "?p:(P-->Q) <-> (P'-->Q')"
  apply (insert assms(1))
  apply (assumption | rule iffI impI | erule iffE | mp | iff assms)+
  done

schematic_goal iff_cong:
  "[| p:P <-> P'; q:Q <-> Q' |] ==> ?p:(P<->Q) <-> (P'<->Q')"
  apply (erule iffE | assumption | rule iffI | mp)+
  done

schematic_goal not_cong:
  "p:P <-> P' ==> ?p:~P <-> ~P'"
  apply (assumption | rule iffI notI | mp | erule iffE notE)+
  done

schematic_goal all_cong:
  assumes "!!x. f(x):P(x) <-> Q(x)"
  shows "?p:(ALL x. P(x)) <-> (ALL x. Q(x))"
  apply (assumption | rule iffI allI | mp | erule allE | iff assms)+
  done

schematic_goal ex_cong:
  assumes "!!x. f(x):P(x) <-> Q(x)"
  shows "?p:(EX x. P(x)) <-> (EX x. Q(x))"
  apply (erule exE | assumption | rule iffI exI | mp | iff assms)+
  done

(*NOT PROVED
ML_Thms.bind_thm ("ex1_cong", prove_goal (the_context ())
    "(!!x.f(x):P(x) <-> Q(x)) ==> ?p:(EX! x.P(x)) <-> (EX! x.Q(x))"
 (fn prems =>
  [ (REPEAT   (eresolve_tac [ex1E, spec RS mp] 1 ORELSE ares_tac [iffI,ex1I] 1
      ORELSE   mp_tac 1
      ORELSE   iff_tac prems 1)) ]))
*)

(*** Equality rules ***)

lemmas refl = ieqI

schematic_goal subst:
  assumes prem1: "p:a=b"
    and prem2: "q:P(a)"
  shows "?p : P(b)"
  apply (rule prem2 [THEN rev_mp])
  apply (rule prem1 [THEN ieqE])
  apply (rule impI)
  apply assumption
  done

schematic_goal sym: "q:a=b ==> ?c:b=a"
  apply (erule subst)
  apply (rule refl)
  done

schematic_goal trans: "[| p:a=b;  q:b=c |] ==> ?d:a=c"
  apply (erule (1) subst)
  done

(** ~ b=a ==> ~ a=b **)
schematic_goal not_sym: "p:~ b=a ==> ?q:~ a=b"
  apply (erule contrapos)
  apply (erule sym)
  done

schematic_goal ssubst: "p:b=a \<Longrightarrow> q:P(a) \<Longrightarrow> ?p:P(b)"
  apply (drule sym)
  apply (erule subst)
  apply assumption
  done

(*A special case of ex1E that would otherwise need quantifier expansion*)
schematic_goal ex1_equalsE: "[| p:EX! x. P(x);  q:P(a);  r:P(b) |] ==> ?d:a=b"
  apply (erule ex1E)
  apply (rule trans)
   apply (rule_tac [2] sym)
   apply (assumption | erule spec [THEN mp])+
  done

(** Polymorphic congruence rules **)

schematic_goal subst_context: "[| p:a=b |]  ==>  ?d:t(a)=t(b)"
  apply (erule ssubst)
  apply (rule refl)
  done

schematic_goal subst_context2: "[| p:a=b;  q:c=d |]  ==>  ?p:t(a,c)=t(b,d)"
  apply (erule ssubst)+
  apply (rule refl)
  done

schematic_goal subst_context3: "[| p:a=b;  q:c=d;  r:e=f |]  ==>  ?p:t(a,c,e)=t(b,d,f)"
  apply (erule ssubst)+
  apply (rule refl)
  done

(*Useful with eresolve_tac for proving equalties from known equalities.
        a = b
        |   |
        c = d   *)
schematic_goal box_equals: "[| p:a=b;  q:a=c;  r:b=d |] ==> ?p:c=d"
  apply (rule trans)
   apply (rule trans)
    apply (rule sym)
    apply assumption+
  done

(*Dual of box_equals: for proving equalities backwards*)
schematic_goal simp_equals: "[| p:a=c;  q:b=d;  r:c=d |] ==> ?p:a=b"
  apply (rule trans)
   apply (rule trans)
    apply (assumption | rule sym)+
  done

(** Congruence rules for predicate letters **)

schematic_goal pred1_cong: "p:a=a' ==> ?p:P(a) <-> P(a')"
  apply (rule iffI)
   apply (tactic \<open>
     DEPTH_SOLVE (assume_tac \<^context> 1 ORELSE eresolve_tac \<^context> [@{thm subst}, @{thm ssubst}] 1)\<close>)
  done

schematic_goal pred2_cong: "[| p:a=a';  q:b=b' |] ==> ?p:P(a,b) <-> P(a',b')"
  apply (rule iffI)
   apply (tactic \<open>
     DEPTH_SOLVE (assume_tac \<^context> 1 ORELSE eresolve_tac \<^context> [@{thm subst}, @{thm ssubst}] 1)\<close>)
  done

schematic_goal pred3_cong: "[| p:a=a';  q:b=b';  r:c=c' |] ==> ?p:P(a,b,c) <-> P(a',b',c')"
  apply (rule iffI)
   apply (tactic \<open>
     DEPTH_SOLVE (assume_tac \<^context> 1 ORELSE eresolve_tac \<^context> [@{thm subst}, @{thm ssubst}] 1)\<close>)
  done

lemmas pred_congs = pred1_cong pred2_cong pred3_cong

(*special case for the equality predicate!*)
lemmas eq_cong = pred2_cong [where P = "(=)"]


(*** Simplifications of assumed implications.
     Roy Dyckhoff has proved that conj_impE, disj_impE, and imp_impE
     used with mp_tac (restricted to atomic formulae) is COMPLETE for
     intuitionistic propositional logic.  See
   R. Dyckhoff, Contraction-free sequent calculi for intuitionistic logic
    (preprint, University of St Andrews, 1991)  ***)

schematic_goal conj_impE:
  assumes major: "p:(P&Q)-->S"
    and minor: "!!x. x:P-->(Q-->S) ==> q(x):R"
  shows "?p:R"
  apply (assumption | rule conjI impI major [THEN mp] minor)+
  done

schematic_goal disj_impE:
  assumes major: "p:(P|Q)-->S"
    and minor: "!!x y.[| x:P-->S; y:Q-->S |] ==> q(x,y):R"
  shows "?p:R"
  apply (tactic \<open>DEPTH_SOLVE (assume_tac \<^context> 1 ORELSE
      resolve_tac \<^context> [@{thm disjI1}, @{thm disjI2}, @{thm impI},
        @{thm major} RS @{thm mp}, @{thm minor}] 1)\<close>)
  done

(*Simplifies the implication.  Classical version is stronger.
  Still UNSAFE since Q must be provable -- backtracking needed.  *)
schematic_goal imp_impE:
  assumes major: "p:(P-->Q)-->S"
    and r1: "!!x y.[| x:P; y:Q-->S |] ==> q(x,y):Q"
    and r2: "!!x. x:S ==> r(x):R"
  shows "?p:R"
  apply (assumption | rule impI major [THEN mp] r1 r2)+
  done

(*Simplifies the implication.  Classical version is stronger.
  Still UNSAFE since ~P must be provable -- backtracking needed.  *)
schematic_goal not_impE:
  assumes major: "p:~P --> S"
    and r1: "!!y. y:P ==> q(y):False"
    and r2: "!!y. y:S ==> r(y):R"
  shows "?p:R"
  apply (assumption | rule notI impI major [THEN mp] r1 r2)+
  done

(*Simplifies the implication.   UNSAFE.  *)
schematic_goal iff_impE:
  assumes major: "p:(P<->Q)-->S"
    and r1: "!!x y.[| x:P; y:Q-->S |] ==> q(x,y):Q"
    and r2: "!!x y.[| x:Q; y:P-->S |] ==> r(x,y):P"
    and r3: "!!x. x:S ==> s(x):R"
  shows "?p:R"
  apply (assumption | rule iffI impI major [THEN mp] r1 r2 r3)+
  done

(*What if (ALL x.~~P(x)) --> ~~(ALL x.P(x)) is an assumption? UNSAFE*)
schematic_goal all_impE:
  assumes major: "p:(ALL x. P(x))-->S"
    and r1: "!!x. q:P(x)"
    and r2: "!!y. y:S ==> r(y):R"
  shows "?p:R"
  apply (assumption | rule allI impI major [THEN mp] r1 r2)+
  done

(*Unsafe: (EX x.P(x))-->S  is equivalent to  ALL x.P(x)-->S.  *)
schematic_goal ex_impE:
  assumes major: "p:(EX x. P(x))-->S"
    and r: "!!y. y:P(a)-->S ==> q(y):R"
  shows "?p:R"
  apply (assumption | rule exI impI major [THEN mp] r)+
  done


schematic_goal rev_cut_eq:
  assumes "p:a=b"
    and "!!x. x:a=b ==> f(x):R"
  shows "?p:R"
  apply (rule assms)+
  done

lemma thin_refl: "!!X. [|p:x=x; PROP W|] ==> PROP W" .

ML_file \<open>hypsubst.ML\<close>

ML \<open>
structure Hypsubst = Hypsubst
(
  (*Take apart an equality judgement; otherwise raise Match!*)
  fun dest_eq \<^Const_>\<open>Proof for \<^Const_>\<open>eq _ for t u\<close> _\<close> = (t, u);

  val imp_intr = @{thm impI}

  (*etac rev_cut_eq moves an equality to be the last premise. *)
  val rev_cut_eq = @{thm rev_cut_eq}

  val rev_mp = @{thm rev_mp}
  val subst = @{thm subst}
  val sym = @{thm sym}
  val thin_refl = @{thm thin_refl}
);
open Hypsubst;
\<close>

ML_file \<open>intprover.ML\<close>


(*** Rewrite rules ***)

schematic_goal conj_rews:
  "?p1 : P & True <-> P"
  "?p2 : True & P <-> P"
  "?p3 : P & False <-> False"
  "?p4 : False & P <-> False"
  "?p5 : P & P <-> P"
  "?p6 : P & ~P <-> False"
  "?p7 : ~P & P <-> False"
  "?p8 : (P & Q) & R <-> P & (Q & R)"
  apply (tactic \<open>fn st => IntPr.fast_tac \<^context> 1 st\<close>)+
  done

schematic_goal disj_rews:
  "?p1 : P | True <-> True"
  "?p2 : True | P <-> True"
  "?p3 : P | False <-> P"
  "?p4 : False | P <-> P"
  "?p5 : P | P <-> P"
  "?p6 : (P | Q) | R <-> P | (Q | R)"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

schematic_goal not_rews:
  "?p1 : ~ False <-> True"
  "?p2 : ~ True <-> False"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

schematic_goal imp_rews:
  "?p1 : (P --> False) <-> ~P"
  "?p2 : (P --> True) <-> True"
  "?p3 : (False --> P) <-> True"
  "?p4 : (True --> P) <-> P"
  "?p5 : (P --> P) <-> True"
  "?p6 : (P --> ~P) <-> ~P"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

schematic_goal iff_rews:
  "?p1 : (True <-> P) <-> P"
  "?p2 : (P <-> True) <-> P"
  "?p3 : (P <-> P) <-> True"
  "?p4 : (False <-> P) <-> ~P"
  "?p5 : (P <-> False) <-> ~P"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

schematic_goal quant_rews:
  "?p1 : (ALL x. P) <-> P"
  "?p2 : (EX x. P) <-> P"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

(*These are NOT supplied by default!*)
schematic_goal distrib_rews1:
  "?p1 : ~(P|Q) <-> ~P & ~Q"
  "?p2 : P & (Q | R) <-> P&Q | P&R"
  "?p3 : (Q | R) & P <-> Q&P | R&P"
  "?p4 : (P | Q --> R) <-> (P --> R) & (Q --> R)"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

schematic_goal distrib_rews2:
  "?p1 : ~(EX x. NORM(P(x))) <-> (ALL x. ~NORM(P(x)))"
  "?p2 : ((EX x. NORM(P(x))) --> Q) <-> (ALL x. NORM(P(x)) --> Q)"
  "?p3 : (EX x. NORM(P(x))) & NORM(Q) <-> (EX x. NORM(P(x)) & NORM(Q))"
  "?p4 : NORM(Q) & (EX x. NORM(P(x))) <-> (EX x. NORM(Q) & NORM(P(x)))"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)+
  done

lemmas distrib_rews = distrib_rews1 distrib_rews2

schematic_goal P_Imp_P_iff_T: "p:P ==> ?p:(P <-> True)"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)
  done

schematic_goal not_P_imp_P_iff_F: "p:~P ==> ?p:(P <-> False)"
  apply (tactic \<open>IntPr.fast_tac \<^context> 1\<close>)
  done

end
