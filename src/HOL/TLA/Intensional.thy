(*  Title:      HOL/TLA/Intensional.thy
    Author:     Stephan Merz
    Copyright:  1998 University of Munich
*)

section \<open>A framework for "intensional" (possible-world based) logics
  on top of HOL, with lifting of constants and functions\<close>

theory Intensional
imports Main
begin

class world

(** abstract syntax **)

type_synonym ('w,'a) expr = "'w \<Rightarrow> 'a"   (* intention: 'w::world, 'a::type *)
type_synonym 'w form = "('w, bool) expr"

definition Valid :: "('w::world) form \<Rightarrow> bool"
  where "Valid A \<equiv> \<forall>w. A w"

definition const :: "'a \<Rightarrow> ('w::world, 'a) expr"
  where unl_con: "const c w \<equiv> c"

definition lift :: "['a \<Rightarrow> 'b, ('w::world, 'a) expr] \<Rightarrow> ('w,'b) expr"
  where unl_lift: "lift f x w \<equiv> f (x w)"

definition lift2 :: "['a \<Rightarrow> 'b \<Rightarrow> 'c, ('w::world,'a) expr, ('w,'b) expr] \<Rightarrow> ('w,'c) expr"
  where unl_lift2: "lift2 f x y w \<equiv> f (x w) (y w)"

definition lift3 :: "['a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd, ('w::world,'a) expr, ('w,'b) expr, ('w,'c) expr] \<Rightarrow> ('w,'d) expr"
  where unl_lift3: "lift3 f x y z w \<equiv> f (x w) (y w) (z w)"

(* "Rigid" quantification (logic level) *)
definition RAll :: "('a \<Rightarrow> ('w::world) form) \<Rightarrow> 'w form"  (binder \<open>Rall \<close> 10)
  where unl_Rall: "(Rall x. A x) w \<equiv> \<forall>x. A x w"
definition REx :: "('a \<Rightarrow> ('w::world) form) \<Rightarrow> 'w form"  (binder \<open>Rex \<close> 10)
  where unl_Rex: "(Rex x. A x) w \<equiv> \<exists>x. A x w"
definition REx1 :: "('a \<Rightarrow> ('w::world) form) \<Rightarrow> 'w form"  (binder \<open>Rex! \<close> 10)
  where unl_Rex1: "(Rex! x. A x) w \<equiv> \<exists>!x. A x w"


(** concrete syntax **)

nonterminal lift and liftargs

syntax
  ""            :: "id \<Rightarrow> lift"                          (\<open>_\<close>)
  ""            :: "longid \<Rightarrow> lift"                      (\<open>_\<close>)
  ""            :: "var \<Rightarrow> lift"                         (\<open>_\<close>)
  "_applC"      :: "[lift, cargs] \<Rightarrow> lift"               (\<open>(1_/ _)\<close> [1000, 1000] 999)
  ""            :: "lift \<Rightarrow> lift"                        (\<open>'(_')\<close>)
  "_lambda"     :: "[idts, 'a] \<Rightarrow> lift"                  (\<open>(3\<lambda>_./ _)\<close> [0, 3] 3)
  "_constrain"  :: "[lift, type] \<Rightarrow> lift"                (\<open>(_::_)\<close> [4, 0] 3)
  ""            :: "lift \<Rightarrow> liftargs"                    (\<open>_\<close>)
  "_liftargs"   :: "[lift, liftargs] \<Rightarrow> liftargs"        (\<open>_,/ _\<close>)
  "_Valid"      :: "lift \<Rightarrow> bool"                        (\<open>(\<turnstile> _)\<close> 5)
  "_holdsAt"    :: "['a, lift] \<Rightarrow> bool"                  (\<open>(_ \<Turnstile> _)\<close> [100,10] 10)

  (* Syntax for lifted expressions outside the scope of \<turnstile> or |= *)
  "_LIFT"       :: "lift \<Rightarrow> 'a"                          (\<open>LIFT _\<close>)

  (* generic syntax for lifted constants and functions *)
  "_const"      :: "'a \<Rightarrow> lift"                          (\<open>(#_)\<close> [1000] 999)
  "_lift"       :: "['a, lift] \<Rightarrow> lift"                  (\<open>(_<_>)\<close> [1000] 999)
  "_lift2"      :: "['a, lift, lift] \<Rightarrow> lift"            (\<open>(_<_,/ _>)\<close> [1000] 999)
  "_lift3"      :: "['a, lift, lift, lift] \<Rightarrow> lift"      (\<open>(_<_,/ _,/ _>)\<close> [1000] 999)

  (* concrete syntax for common infix functions: reuse same symbol *)
  "_liftEqu"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ =/ _)\<close> [50,51] 50)
  "_liftNeq"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ \<noteq>/ _)\<close> [50,51] 50)
  "_liftNot"    :: "lift \<Rightarrow> lift"                        (\<open>(\<not> _)\<close> [40] 40)
  "_liftAnd"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ \<and>/ _)\<close> [36,35] 35)
  "_liftOr"     :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ \<or>/ _)\<close> [31,30] 30)
  "_liftImp"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ \<longrightarrow>/ _)\<close> [26,25] 25)
  "_liftIf"     :: "[lift, lift, lift] \<Rightarrow> lift"          (\<open>(if (_)/ then (_)/ else (_))\<close> 10)
  "_liftPlus"   :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ +/ _)\<close> [66,65] 65)
  "_liftMinus"  :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ -/ _)\<close> [66,65] 65)
  "_liftTimes"  :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ */ _)\<close> [71,70] 70)
  "_liftDiv"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ div _)\<close> [71,70] 70)
  "_liftMod"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_ mod _)\<close> [71,70] 70)
  "_liftLess"   :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_/ < _)\<close>  [50, 51] 50)
  "_liftLeq"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_/ \<le> _)\<close> [50, 51] 50)
  "_liftMem"    :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_/ \<in> _)\<close> [50, 51] 50)
  "_liftNotMem" :: "[lift, lift] \<Rightarrow> lift"                (\<open>(_/ \<notin> _)\<close> [50, 51] 50)
  "_liftFinset" :: "liftargs \<Rightarrow> lift"                    (\<open>{(_)}\<close>)
  (** TODO: syntax for lifted collection / comprehension **)
  "_liftPair"   :: "[lift,liftargs] \<Rightarrow> lift"                   (\<open>(1'(_,/ _'))\<close>)
  (* infix syntax for list operations *)
  "_liftCons" :: "[lift, lift] \<Rightarrow> lift"                  (\<open>(_ #/ _)\<close> [65,66] 65)
  "_liftApp"  :: "[lift, lift] \<Rightarrow> lift"                  (\<open>(_ @/ _)\<close> [65,66] 65)
  "_liftList" :: "liftargs \<Rightarrow> lift"                      (\<open>[(_)]\<close>)

  (* Rigid quantification (syntax level) *)
  "_RAll" :: "[idts, lift] \<Rightarrow> lift"                      (\<open>(3\<forall>_./ _)\<close> [0, 10] 10)
  "_REx"  :: "[idts, lift] \<Rightarrow> lift"                      (\<open>(3\<exists>_./ _)\<close> [0, 10] 10)
  "_REx1" :: "[idts, lift] \<Rightarrow> lift"                      (\<open>(3\<exists>!_./ _)\<close> [0, 10] 10)

translations
  "_const"        == "CONST const"
  "_lift"         == "CONST lift"
  "_lift2"        == "CONST lift2"
  "_lift3"        == "CONST lift3"
  "_Valid"        == "CONST Valid"
  "_RAll x A"     == "Rall x. A"
  "_REx x  A"     == "Rex x. A"
  "_REx1 x  A"    == "Rex! x. A"

  "w \<Turnstile> A"        => "A w"
  "LIFT A"        => "A::_\<Rightarrow>_"

  "_liftEqu"      == "_lift2 (=)"
  "_liftNeq u v"  == "_liftNot (_liftEqu u v)"
  "_liftNot"      == "_lift (CONST Not)"
  "_liftAnd"      == "_lift2 (\<and>)"
  "_liftOr"       == "_lift2 (\<or>)"
  "_liftImp"      == "_lift2 (\<longrightarrow>)"
  "_liftIf"       == "_lift3 (CONST If)"
  "_liftPlus"     == "_lift2 (+)"
  "_liftMinus"    == "_lift2 (-)"
  "_liftTimes"    == "_lift2 ((*))"
  "_liftDiv"      == "_lift2 (div)"
  "_liftMod"      == "_lift2 (mod)"
  "_liftLess"     == "_lift2 (<)"
  "_liftLeq"      == "_lift2 (\<le>)"
  "_liftMem"      == "_lift2 (\<in>)"
  "_liftNotMem x xs"   == "_liftNot (_liftMem x xs)"
  "_liftFinset (_liftargs x xs)"  == "_lift2 (CONST insert) x (_liftFinset xs)"
  "_liftFinset x" == "_lift2 (CONST insert) x (_const {})"
  "_liftPair x (_liftargs y z)"       == "_liftPair x (_liftPair y z)"
  "_liftPair"     == "_lift2 (CONST Pair)"
  "_liftCons"     == "CONST lift2 (CONST Cons)"
  "_liftApp"      == "CONST lift2 (@)"
  "_liftList (_liftargs x xs)"  == "_liftCons x (_liftList xs)"
  "_liftList x"   == "_liftCons x (_const [])"

  "w \<Turnstile> \<not>A"       <= "_liftNot A w"
  "w \<Turnstile> A \<and> B"    <= "_liftAnd A B w"
  "w \<Turnstile> A \<or> B"    <= "_liftOr A B w"
  "w \<Turnstile> A \<longrightarrow> B"  <= "_liftImp A B w"
  "w \<Turnstile> u = v"    <= "_liftEqu u v w"
  "w \<Turnstile> \<forall>x. A"   <= "_RAll x A w"
  "w \<Turnstile> \<exists>x. A"   <= "_REx x A w"
  "w \<Turnstile> \<exists>!x. A"  <= "_REx1 x A w"


subsection \<open>Lemmas and tactics for "intensional" logics.\<close>

lemmas intensional_rews [simp] =
  unl_con unl_lift unl_lift2 unl_lift3 unl_Rall unl_Rex unl_Rex1

lemma inteq_reflection: "\<turnstile> x=y  \<Longrightarrow>  (x==y)"
  apply (unfold Valid_def unl_lift2)
  apply (rule eq_reflection)
  apply (rule ext)
  apply (erule spec)
  done

lemma intI [intro!]: "(\<And>w. w \<Turnstile> A) \<Longrightarrow> \<turnstile> A"
  apply (unfold Valid_def)
  apply (rule allI)
  apply (erule meta_spec)
  done

lemma intD [dest]: "\<turnstile> A \<Longrightarrow> w \<Turnstile> A"
  apply (unfold Valid_def)
  apply (erule spec)
  done

(** Lift usual HOL simplifications to "intensional" level. **)

lemma int_simps:
  "\<turnstile> (x=x) = #True"
  "\<turnstile> (\<not>#True) = #False"  "\<turnstile> (\<not>#False) = #True"  "\<turnstile> (\<not>\<not> P) = P"
  "\<turnstile> ((\<not>P) = P) = #False"  "\<turnstile> (P = (\<not>P)) = #False"
  "\<turnstile> (P \<noteq> Q) = (P = (\<not>Q))"
  "\<turnstile> (#True=P) = P"  "\<turnstile> (P=#True) = P"
  "\<turnstile> (#True \<longrightarrow> P) = P"  "\<turnstile> (#False \<longrightarrow> P) = #True"
  "\<turnstile> (P \<longrightarrow> #True) = #True"  "\<turnstile> (P \<longrightarrow> P) = #True"
  "\<turnstile> (P \<longrightarrow> #False) = (\<not>P)"  "\<turnstile> (P \<longrightarrow> \<not>P) = (\<not>P)"
  "\<turnstile> (P \<and> #True) = P"  "\<turnstile> (#True \<and> P) = P"
  "\<turnstile> (P \<and> #False) = #False"  "\<turnstile> (#False \<and> P) = #False"
  "\<turnstile> (P \<and> P) = P"  "\<turnstile> (P \<and> \<not>P) = #False"  "\<turnstile> (\<not>P \<and> P) = #False"
  "\<turnstile> (P \<or> #True) = #True"  "\<turnstile> (#True \<or> P) = #True"
  "\<turnstile> (P \<or> #False) = P"  "\<turnstile> (#False \<or> P) = P"
  "\<turnstile> (P \<or> P) = P"  "\<turnstile> (P \<or> \<not>P) = #True"  "\<turnstile> (\<not>P \<or> P) = #True"
  "\<turnstile> (\<forall>x. P) = P"  "\<turnstile> (\<exists>x. P) = P"
  "\<turnstile> (\<not>Q \<longrightarrow> \<not>P) = (P \<longrightarrow> Q)"
  "\<turnstile> (P\<or>Q \<longrightarrow> R) = ((P\<longrightarrow>R)\<and>(Q\<longrightarrow>R))"
  apply (unfold Valid_def intensional_rews)
  apply blast+
  done

declare int_simps [THEN inteq_reflection, simp]

lemma TrueW [simp]: "\<turnstile> #True"
  by (simp add: Valid_def unl_con)



(* ======== Functions to "unlift" intensional implications into HOL rules ====== *)

ML \<open>
(* Basic unlifting introduces a parameter "w" and applies basic rewrites, e.g.
   \<turnstile> F = G    becomes   F w = G w
   \<turnstile> F \<longrightarrow> G  becomes   F w \<longrightarrow> G w
*)

fun int_unlift ctxt th =
  rewrite_rule ctxt @{thms intensional_rews} (th RS @{thm intD} handle THM _ => th);

(* Turn  \<turnstile> F = G  into meta-level rewrite rule  F == G *)
fun int_rewrite ctxt th =
  zero_var_indexes (rewrite_rule ctxt @{thms intensional_rews} (th RS @{thm inteq_reflection}))

(* flattening turns "\<longrightarrow>" into "\<Longrightarrow>" and eliminates conjunctions in the
   antecedent. For example,

         P & Q \<longrightarrow> (R | S \<longrightarrow> T)    becomes   \<lbrakk> P; Q; R | S \<rbrakk> \<Longrightarrow> T

   Flattening can be useful with "intensional" lemmas (after unlifting).
   Naive resolution with mp and conjI may run away because of higher-order
   unification, therefore the code is a little awkward.
*)
fun flatten t =
  let
    (* analogous to RS, but using matching instead of resolution *)
    fun matchres tha i thb =
      case Seq.chop 2 (Thm.biresolution NONE true [(false,tha)] i thb) of
          ([th],_) => th
        | ([],_)   => raise THM("matchres: no match", i, [tha,thb])
        |      _   => raise THM("matchres: multiple unifiers", i, [tha,thb])

    (* match tha with some premise of thb *)
    fun matchsome tha thb =
      let fun hmatch 0 = raise THM("matchsome: no match", 0, [tha,thb])
            | hmatch n = matchres tha n thb handle THM _ => hmatch (n-1)
      in hmatch (Thm.nprems_of thb) end

    fun hflatten t =
      case Thm.concl_of t of
        Const _ $ (Const (\<^const_name>\<open>HOL.implies\<close>, _) $ _ $ _) => hflatten (t RS mp)
      | _ => (hflatten (matchsome conjI t)) handle THM _ => zero_var_indexes t
  in
    hflatten t
  end

fun int_use ctxt th =
    case Thm.concl_of th of
      Const _ $ (Const (\<^const_name>\<open>Valid\<close>, _) $ _) =>
              (flatten (int_unlift ctxt th) handle THM _ => th)
    | _ => th
\<close>

attribute_setup int_unlift =
  \<open>Scan.succeed (Thm.rule_attribute [] (int_unlift o Context.proof_of))\<close>
attribute_setup int_rewrite =
  \<open>Scan.succeed (Thm.rule_attribute [] (int_rewrite o Context.proof_of))\<close>
attribute_setup flatten =
  \<open>Scan.succeed (Thm.rule_attribute [] (K flatten))\<close>
attribute_setup int_use =
  \<open>Scan.succeed (Thm.rule_attribute [] (int_use o Context.proof_of))\<close>

lemma Not_Rall: "\<turnstile> (\<not>(\<forall>x. F x)) = (\<exists>x. \<not>F x)"
  by (simp add: Valid_def)

lemma Not_Rex: "\<turnstile> (\<not> (\<exists>x. F x)) = (\<forall>x. \<not> F x)"
  by (simp add: Valid_def)

end
