(*  Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel *)

header {* Set theory for higher-order logic *}

theory Set
imports Lattices
begin

subsection {* Sets as predicates *}

type_synonym 'a set = "'a \<Rightarrow> bool"

definition Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a set" where -- "comprehension"
  "Collect P = P"

definition member :: "'a \<Rightarrow> 'a set \<Rightarrow> bool" where -- "membership"
  mem_def: "member x A = A x"

notation
  member  ("op :") and
  member  ("(_/ : _)" [50, 51] 50)

abbreviation not_member where
  "not_member x A \<equiv> ~ (x : A)" -- "non-membership"

notation
  not_member  ("op ~:") and
  not_member  ("(_/ ~: _)" [50, 51] 50)

notation (xsymbols)
  member      ("op \<in>") and
  member      ("(_/ \<in> _)" [50, 51] 50) and
  not_member  ("op \<notin>") and
  not_member  ("(_/ \<notin> _)" [50, 51] 50)

notation (HTML output)
  member      ("op \<in>") and
  member      ("(_/ \<in> _)" [50, 51] 50) and
  not_member  ("op \<notin>") and
  not_member  ("(_/ \<notin> _)" [50, 51] 50)



text {* Set comprehensions *}

syntax
  "_Coll" :: "pttrn => bool => 'a set"    ("(1{_./ _})")
translations
  "{x. P}" == "CONST Collect (%x. P)"

syntax
  "_Collect" :: "idt => 'a set => bool => 'a set"    ("(1{_ :/ _./ _})")
syntax (xsymbols)
  "_Collect" :: "idt => 'a set => bool => 'a set"    ("(1{_ \<in>/ _./ _})")
translations
  "{x:A. P}" => "{x. x:A & P}"

lemma mem_Collect_eq [iff]: "a \<in> {x. P x} = P a"
  by (simp add: Collect_def mem_def)

lemma Collect_mem_eq [simp]: "{x. x \<in> A} = A"
  by (simp add: Collect_def mem_def)

lemma CollectI: "P a \<Longrightarrow> a \<in> {x. P x}"
  by simp

lemma CollectD: "a \<in> {x. P x} \<Longrightarrow> P a"
  by simp

lemma Collect_cong: "(\<And>x. P x = Q x) ==> {x. P x} = {x. Q x}"
  by simp

text {*
Simproc for pulling @{text "x=t"} in @{text "{x. \<dots> & x=t & \<dots>}"}
to the front (and similarly for @{text "t=x"}):
*}

simproc_setup defined_Collect ("{x. P x & Q x}") = {*
  fn _ =>
    Quantifier1.rearrange_Collect
     (rtac @{thm Collect_cong} 1 THEN
      rtac @{thm iffI} 1 THEN
      ALLGOALS
        (EVERY' [REPEAT_DETERM o etac @{thm conjE}, DEPTH_SOLVE_1 o ares_tac @{thms conjI}]))
*}

lemmas CollectE = CollectD [elim_format]

lemma set_eqI:
  assumes "\<And>x. x \<in> A \<longleftrightarrow> x \<in> B"
  shows "A = B"
proof -
  from assms have "{x. x \<in> A} = {x. x \<in> B}" by simp
  then show ?thesis by simp
qed

lemma set_eq_iff [no_atp]:
  "A = B \<longleftrightarrow> (\<forall>x. x \<in> A \<longleftrightarrow> x \<in> B)"
  by (auto intro:set_eqI)

text {* Set enumerations *}

abbreviation empty :: "'a set" ("{}") where
  "{} \<equiv> bot"

definition insert :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  insert_compr: "insert a B = {x. x = a \<or> x \<in> B}"

syntax
  "_Finset" :: "args => 'a set"    ("{(_)}")
translations
  "{x, xs}" == "CONST insert x {xs}"
  "{x}" == "CONST insert x {}"


subsection {* Subsets and bounded quantifiers *}

abbreviation
  subset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subset \<equiv> less"

abbreviation
  subset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "subset_eq \<equiv> less_eq"

notation (output)
  subset  ("op <") and
  subset  ("(_/ < _)" [50, 51] 50) and
  subset_eq  ("op <=") and
  subset_eq  ("(_/ <= _)" [50, 51] 50)

notation (xsymbols)
  subset  ("op \<subset>") and
  subset  ("(_/ \<subset> _)" [50, 51] 50) and
  subset_eq  ("op \<subseteq>") and
  subset_eq  ("(_/ \<subseteq> _)" [50, 51] 50)

notation (HTML output)
  subset  ("op \<subset>") and
  subset  ("(_/ \<subset> _)" [50, 51] 50) and
  subset_eq  ("op \<subseteq>") and
  subset_eq  ("(_/ \<subseteq> _)" [50, 51] 50)

abbreviation (input)
  supset :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "supset \<equiv> greater"

abbreviation (input)
  supset_eq :: "'a set \<Rightarrow> 'a set \<Rightarrow> bool" where
  "supset_eq \<equiv> greater_eq"

notation (xsymbols)
  supset  ("op \<supset>") and
  supset  ("(_/ \<supset> _)" [50, 51] 50) and
  supset_eq  ("op \<supseteq>") and
  supset_eq  ("(_/ \<supseteq> _)" [50, 51] 50)

definition Ball :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Ball A P \<longleftrightarrow> (\<forall>x. x \<in> A \<longrightarrow> P x)"   -- "bounded universal quantifiers"

definition Bex :: "'a set \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "Bex A P \<longleftrightarrow> (\<exists>x. x \<in> A \<and> P x)"   -- "bounded existential quantifiers"

syntax
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3ALL _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3EX _:_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3EX! _:_./ _)" [0, 0, 10] 10)
  "_Bleast"     :: "id => 'a set => bool => 'a"           ("(3LEAST _:_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3! _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3? _:_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3?! _:_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3\<exists>!_\<in>_./ _)" [0, 0, 10] 10)
  "_Bleast"     :: "id => 'a set => bool => 'a"           ("(3LEAST_\<in>_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex1"       :: "pttrn => 'a set => bool => bool"      ("(3\<exists>!_\<in>_./ _)" [0, 0, 10] 10)

translations
  "ALL x:A. P" == "CONST Ball A (%x. P)"
  "EX x:A. P" == "CONST Bex A (%x. P)"
  "EX! x:A. P" => "EX! x. x:A & P"
  "LEAST x:A. P" => "LEAST x. x:A & P"

syntax (output)
  "_setlessAll" :: "[idt, 'a, bool] => bool"  ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"  ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"  ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"  ("(3EX _<=_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"  ("(3EX! _<=_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_setlessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subset>_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subset>_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"   ("(3\<exists>!_\<subseteq>_./ _)" [0, 0, 10] 10)

syntax (HOL output)
  "_setlessAll" :: "[idt, 'a, bool] => bool"   ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"   ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"   ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"   ("(3? _<=_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"   ("(3?! _<=_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_setlessAll" :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subset>_./ _)"  [0, 0, 10] 10)
  "_setlessEx"  :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subset>_./ _)"  [0, 0, 10] 10)
  "_setleAll"   :: "[idt, 'a, bool] => bool"   ("(3\<forall>_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setleEx"    :: "[idt, 'a, bool] => bool"   ("(3\<exists>_\<subseteq>_./ _)" [0, 0, 10] 10)
  "_setleEx1"   :: "[idt, 'a, bool] => bool"   ("(3\<exists>!_\<subseteq>_./ _)" [0, 0, 10] 10)

translations
 "\<forall>A\<subset>B. P"   =>  "ALL A. A \<subset> B --> P"
 "\<exists>A\<subset>B. P"   =>  "EX A. A \<subset> B & P"
 "\<forall>A\<subseteq>B. P"   =>  "ALL A. A \<subseteq> B --> P"
 "\<exists>A\<subseteq>B. P"   =>  "EX A. A \<subseteq> B & P"
 "\<exists>!A\<subseteq>B. P"  =>  "EX! A. A \<subseteq> B & P"

print_translation {*
let
  val Type (set_type, _) = @{typ "'a set"};   (* FIXME 'a => bool (!?!) *)
  val All_binder = Mixfix.binder_name @{const_syntax All};
  val Ex_binder = Mixfix.binder_name @{const_syntax Ex};
  val impl = @{const_syntax HOL.implies};
  val conj = @{const_syntax HOL.conj};
  val sbset = @{const_syntax subset};
  val sbset_eq = @{const_syntax subset_eq};

  val trans =
   [((All_binder, impl, sbset), @{syntax_const "_setlessAll"}),
    ((All_binder, impl, sbset_eq), @{syntax_const "_setleAll"}),
    ((Ex_binder, conj, sbset), @{syntax_const "_setlessEx"}),
    ((Ex_binder, conj, sbset_eq), @{syntax_const "_setleEx"})];

  fun mk v v' c n P =
    if v = v' andalso not (Term.exists_subterm (fn Free (x, _) => x = v | _ => false) n)
    then Syntax.const c $ Syntax_Trans.mark_bound v' $ n $ P else raise Match;

  fun tr' q = (q,
        fn [Const (@{syntax_const "_bound"}, _) $ Free (v, Type (T, _)),
            Const (c, _) $
              (Const (d, _) $ (Const (@{syntax_const "_bound"}, _) $ Free (v', _)) $ n) $ P] =>
            if T = set_type then
              (case AList.lookup (op =) trans (q, c, d) of
                NONE => raise Match
              | SOME l => mk v v' l n P)
            else raise Match
         | _ => raise Match);
in
  [tr' All_binder, tr' Ex_binder]
end
*}


text {*
  \medskip Translate between @{text "{e | x1...xn. P}"} and @{text
  "{u. EX x1..xn. u = e & P}"}; @{text "{y. EX x1..xn. y = e & P}"} is
  only translated if @{text "[0..n] subset bvs(e)"}.
*}

syntax
  "_Setcompr" :: "'a => idts => bool => 'a set"    ("(1{_ |/_./ _})")

parse_translation {*
  let
    val ex_tr = snd (Syntax_Trans.mk_binder_tr ("EX ", @{const_syntax Ex}));

    fun nvars (Const (@{syntax_const "_idts"}, _) $ _ $ idts) = nvars idts + 1
      | nvars _ = 1;

    fun setcompr_tr [e, idts, b] =
      let
        val eq = Syntax.const @{const_syntax HOL.eq} $ Bound (nvars idts) $ e;
        val P = Syntax.const @{const_syntax HOL.conj} $ eq $ b;
        val exP = ex_tr [idts, P];
      in Syntax.const @{const_syntax Collect} $ absdummy dummyT exP end;

  in [(@{syntax_const "_Setcompr"}, setcompr_tr)] end;
*}

print_translation {*
 [Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax Ball} @{syntax_const "_Ball"},
  Syntax_Trans.preserve_binder_abs2_tr' @{const_syntax Bex} @{syntax_const "_Bex"}]
*} -- {* to avoid eta-contraction of body *}

print_translation {*
let
  val ex_tr' = snd (Syntax_Trans.mk_binder_tr' (@{const_syntax Ex}, "DUMMY"));

  fun setcompr_tr' [Abs (abs as (_, _, P))] =
    let
      fun check (Const (@{const_syntax Ex}, _) $ Abs (_, _, P), n) = check (P, n + 1)
        | check (Const (@{const_syntax HOL.conj}, _) $
              (Const (@{const_syntax HOL.eq}, _) $ Bound m $ e) $ P, n) =
            n > 0 andalso m = n andalso not (loose_bvar1 (P, n)) andalso
            subset (op =) (0 upto (n - 1), add_loose_bnos (e, 0, []))
        | check _ = false;

        fun tr' (_ $ abs) =
          let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr' [abs]
          in Syntax.const @{syntax_const "_Setcompr"} $ e $ idts $ Q end;
    in
      if check (P, 0) then tr' P
      else
        let
          val (x as _ $ Free(xN, _), t) = Syntax_Trans.atomic_abs_tr' abs;
          val M = Syntax.const @{syntax_const "_Coll"} $ x $ t;
        in
          case t of
            Const (@{const_syntax HOL.conj}, _) $
              (Const (@{const_syntax Set.member}, _) $
                (Const (@{syntax_const "_bound"}, _) $ Free (yN, _)) $ A) $ P =>
            if xN = yN then Syntax.const @{syntax_const "_Collect"} $ x $ A $ P else M
          | _ => M
        end
    end;
  in [(@{const_syntax Collect}, setcompr_tr')] end;
*}

simproc_setup defined_Bex ("EX x:A. P x & Q x") = {*
  let
    val unfold_bex_tac = unfold_tac @{thms Bex_def};
    fun prove_bex_tac ss = unfold_bex_tac ss THEN Quantifier1.prove_one_point_ex_tac;
  in fn _ => fn ss => Quantifier1.rearrange_bex (prove_bex_tac ss) ss end
*}

simproc_setup defined_All ("ALL x:A. P x --> Q x") = {*
  let
    val unfold_ball_tac = unfold_tac @{thms Ball_def};
    fun prove_ball_tac ss = unfold_ball_tac ss THEN Quantifier1.prove_one_point_all_tac;
  in fn _ => fn ss => Quantifier1.rearrange_ball (prove_ball_tac ss) ss end
*}

lemma ballI [intro!]: "(!!x. x:A ==> P x) ==> ALL x:A. P x"
  by (simp add: Ball_def)

lemmas strip = impI allI ballI

lemma bspec [dest?]: "ALL x:A. P x ==> x:A ==> P x"
  by (simp add: Ball_def)

text {*
  Gives better instantiation for bound:
*}

declaration {* fn _ =>
  Classical.map_cs (fn cs => cs addbefore ("bspec", datac @{thm bspec} 1))
*}

ML {*
structure Simpdata =
struct

open Simpdata;

val mksimps_pairs = [(@{const_name Ball}, @{thms bspec})] @ mksimps_pairs;

end;

open Simpdata;
*}

declaration {* fn _ =>
  Simplifier.map_ss (Simplifier.set_mksimps (mksimps mksimps_pairs))
*}

lemma ballE [elim]: "ALL x:A. P x ==> (P x ==> Q) ==> (x ~: A ==> Q) ==> Q"
  by (unfold Ball_def) blast

lemma bexI [intro]: "P x ==> x:A ==> EX x:A. P x"
  -- {* Normally the best argument order: @{prop "P x"} constrains the
    choice of @{prop "x:A"}. *}
  by (unfold Bex_def) blast

lemma rev_bexI [intro?]: "x:A ==> P x ==> EX x:A. P x"
  -- {* The best argument order when there is only one @{prop "x:A"}. *}
  by (unfold Bex_def) blast

lemma bexCI: "(ALL x:A. ~P x ==> P a) ==> a:A ==> EX x:A. P x"
  by (unfold Bex_def) blast

lemma bexE [elim!]: "EX x:A. P x ==> (!!x. x:A ==> P x ==> Q) ==> Q"
  by (unfold Bex_def) blast

lemma ball_triv [simp]: "(ALL x:A. P) = ((EX x. x:A) --> P)"
  -- {* Trival rewrite rule. *}
  by (simp add: Ball_def)

lemma bex_triv [simp]: "(EX x:A. P) = ((EX x. x:A) & P)"
  -- {* Dual form for existentials. *}
  by (simp add: Bex_def)

lemma bex_triv_one_point1 [simp]: "(EX x:A. x = a) = (a:A)"
  by blast

lemma bex_triv_one_point2 [simp]: "(EX x:A. a = x) = (a:A)"
  by blast

lemma bex_one_point1 [simp]: "(EX x:A. x = a & P x) = (a:A & P a)"
  by blast

lemma bex_one_point2 [simp]: "(EX x:A. a = x & P x) = (a:A & P a)"
  by blast

lemma ball_one_point1 [simp]: "(ALL x:A. x = a --> P x) = (a:A --> P a)"
  by blast

lemma ball_one_point2 [simp]: "(ALL x:A. a = x --> P x) = (a:A --> P a)"
  by blast

lemma ball_conj_distrib:
  "(\<forall>x\<in>A. P x \<and> Q x) \<longleftrightarrow> ((\<forall>x\<in>A. P x) \<and> (\<forall>x\<in>A. Q x))"
  by blast

lemma bex_disj_distrib:
  "(\<exists>x\<in>A. P x \<or> Q x) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<or> (\<exists>x\<in>A. Q x))"
  by blast


text {* Congruence rules *}

lemma ball_cong:
  "A = B ==> (!!x. x:B ==> P x = Q x) ==>
    (ALL x:A. P x) = (ALL x:B. Q x)"
  by (simp add: Ball_def)

lemma strong_ball_cong [cong]:
  "A = B ==> (!!x. x:B =simp=> P x = Q x) ==>
    (ALL x:A. P x) = (ALL x:B. Q x)"
  by (simp add: simp_implies_def Ball_def)

lemma bex_cong:
  "A = B ==> (!!x. x:B ==> P x = Q x) ==>
    (EX x:A. P x) = (EX x:B. Q x)"
  by (simp add: Bex_def cong: conj_cong)

lemma strong_bex_cong [cong]:
  "A = B ==> (!!x. x:B =simp=> P x = Q x) ==>
    (EX x:A. P x) = (EX x:B. Q x)"
  by (simp add: simp_implies_def Bex_def cong: conj_cong)


subsection {* Basic operations *}

subsubsection {* Subsets *}

lemma subsetI [intro!]: "(\<And>x. x \<in> A \<Longrightarrow> x \<in> B) \<Longrightarrow> A \<subseteq> B"
  unfolding mem_def by (rule le_funI, rule le_boolI)

text {*
  \medskip Map the type @{text "'a set => anything"} to just @{typ
  'a}; for overloading constants whose first argument has type @{typ
  "'a set"}.
*}

lemma subsetD [elim, intro?]: "A \<subseteq> B ==> c \<in> A ==> c \<in> B"
  unfolding mem_def by (erule le_funE, erule le_boolE)
  -- {* Rule in Modus Ponens style. *}

lemma rev_subsetD [no_atp,intro?]: "c \<in> A ==> A \<subseteq> B ==> c \<in> B"
  -- {* The same, with reversed premises for use with @{text erule} --
      cf @{text rev_mp}. *}
  by (rule subsetD)

text {*
  \medskip Converts @{prop "A \<subseteq> B"} to @{prop "x \<in> A ==> x \<in> B"}.
*}

lemma subsetCE [no_atp,elim]: "A \<subseteq> B ==> (c \<notin> A ==> P) ==> (c \<in> B ==> P) ==> P"
  -- {* Classical elimination rule. *}
  unfolding mem_def by (blast dest: le_funE le_boolE)

lemma subset_eq [no_atp]: "A \<le> B = (\<forall>x\<in>A. x \<in> B)" by blast

lemma contra_subsetD [no_atp]: "A \<subseteq> B ==> c \<notin> B ==> c \<notin> A"
  by blast

lemma subset_refl: "A \<subseteq> A"
  by (fact order_refl) (* already [iff] *)

lemma subset_trans: "A \<subseteq> B ==> B \<subseteq> C ==> A \<subseteq> C"
  by (fact order_trans)

lemma set_rev_mp: "x:A ==> A \<subseteq> B ==> x:B"
  by (rule subsetD)

lemma set_mp: "A \<subseteq> B ==> x:A ==> x:B"
  by (rule subsetD)

lemma eq_mem_trans: "a=b ==> b \<in> A ==> a \<in> A"
  by simp

lemmas basic_trans_rules [trans] =
  order_trans_rules set_rev_mp set_mp eq_mem_trans


subsubsection {* Equality *}

lemma subset_antisym [intro!]: "A \<subseteq> B ==> B \<subseteq> A ==> A = B"
  -- {* Anti-symmetry of the subset relation. *}
  by (iprover intro: set_eqI subsetD)

text {*
  \medskip Equality rules from ZF set theory -- are they appropriate
  here?
*}

lemma equalityD1: "A = B ==> A \<subseteq> B"
  by simp

lemma equalityD2: "A = B ==> B \<subseteq> A"
  by simp

text {*
  \medskip Be careful when adding this to the claset as @{text
  subset_empty} is in the simpset: @{prop "A = {}"} goes to @{prop "{}
  \<subseteq> A"} and @{prop "A \<subseteq> {}"} and then back to @{prop "A = {}"}!
*}

lemma equalityE: "A = B ==> (A \<subseteq> B ==> B \<subseteq> A ==> P) ==> P"
  by simp

lemma equalityCE [elim]:
    "A = B ==> (c \<in> A ==> c \<in> B ==> P) ==> (c \<notin> A ==> c \<notin> B ==> P) ==> P"
  by blast

lemma eqset_imp_iff: "A = B ==> (x : A) = (x : B)"
  by simp

lemma eqelem_imp_iff: "x = y ==> (x : A) = (y : A)"
  by simp


subsubsection {* The empty set *}

lemma empty_def:
  "{} = {x. False}"
  by (simp add: bot_fun_def Collect_def)

lemma empty_iff [simp]: "(c : {}) = False"
  by (simp add: empty_def)

lemma emptyE [elim!]: "a : {} ==> P"
  by simp

lemma empty_subsetI [iff]: "{} \<subseteq> A"
    -- {* One effect is to delete the ASSUMPTION @{prop "{} <= A"} *}
  by blast

lemma equals0I: "(!!y. y \<in> A ==> False) ==> A = {}"
  by blast

lemma equals0D: "A = {} ==> a \<notin> A"
    -- {* Use for reasoning about disjointness: @{text "A Int B = {}"} *}
  by blast

lemma ball_empty [simp]: "Ball {} P = True"
  by (simp add: Ball_def)

lemma bex_empty [simp]: "Bex {} P = False"
  by (simp add: Bex_def)


subsubsection {* The universal set -- UNIV *}

abbreviation UNIV :: "'a set" where
  "UNIV \<equiv> top"

lemma UNIV_def:
  "UNIV = {x. True}"
  by (simp add: top_fun_def Collect_def)

lemma UNIV_I [simp]: "x : UNIV"
  by (simp add: UNIV_def)

declare UNIV_I [intro]  -- {* unsafe makes it less likely to cause problems *}

lemma UNIV_witness [intro?]: "EX x. x : UNIV"
  by simp

lemma subset_UNIV: "A \<subseteq> UNIV"
  by (fact top_greatest) (* already simp *)

text {*
  \medskip Eta-contracting these two rules (to remove @{text P})
  causes them to be ignored because of their interaction with
  congruence rules.
*}

lemma ball_UNIV [simp]: "Ball UNIV P = All P"
  by (simp add: Ball_def)

lemma bex_UNIV [simp]: "Bex UNIV P = Ex P"
  by (simp add: Bex_def)

lemma UNIV_eq_I: "(\<And>x. x \<in> A) \<Longrightarrow> UNIV = A"
  by auto

lemma UNIV_not_empty [iff]: "UNIV ~= {}"
  by (blast elim: equalityE)


subsubsection {* The Powerset operator -- Pow *}

definition Pow :: "'a set => 'a set set" where
  Pow_def: "Pow A = {B. B \<le> A}"

lemma Pow_iff [iff]: "(A \<in> Pow B) = (A \<subseteq> B)"
  by (simp add: Pow_def)

lemma PowI: "A \<subseteq> B ==> A \<in> Pow B"
  by (simp add: Pow_def)

lemma PowD: "A \<in> Pow B ==> A \<subseteq> B"
  by (simp add: Pow_def)

lemma Pow_bottom: "{} \<in> Pow B"
  by simp

lemma Pow_top: "A \<in> Pow A"
  by simp

lemma Pow_not_empty: "Pow A \<noteq> {}"
  using Pow_top by blast


subsubsection {* Set complement *}

lemma Compl_iff [simp]: "(c \<in> -A) = (c \<notin> A)"
  by (simp add: mem_def fun_Compl_def)

lemma ComplI [intro!]: "(c \<in> A ==> False) ==> c \<in> -A"
  by (unfold mem_def fun_Compl_def bool_Compl_def) blast

text {*
  \medskip This form, with negated conclusion, works well with the
  Classical prover.  Negated assumptions behave like formulae on the
  right side of the notional turnstile ... *}

lemma ComplD [dest!]: "c : -A ==> c~:A"
  by (simp add: mem_def fun_Compl_def)

lemmas ComplE = ComplD [elim_format]

lemma Compl_eq: "- A = {x. ~ x : A}" by blast


subsubsection {* Binary intersection *}

abbreviation inter :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "Int" 70) where
  "op Int \<equiv> inf"

notation (xsymbols)
  inter  (infixl "\<inter>" 70)

notation (HTML output)
  inter  (infixl "\<inter>" 70)

lemma Int_def:
  "A \<inter> B = {x. x \<in> A \<and> x \<in> B}"
  by (simp add: inf_fun_def Collect_def mem_def)

lemma Int_iff [simp]: "(c : A Int B) = (c:A & c:B)"
  by (unfold Int_def) blast

lemma IntI [intro!]: "c:A ==> c:B ==> c : A Int B"
  by simp

lemma IntD1: "c : A Int B ==> c:A"
  by simp

lemma IntD2: "c : A Int B ==> c:B"
  by simp

lemma IntE [elim!]: "c : A Int B ==> (c:A ==> c:B ==> P) ==> P"
  by simp

lemma mono_Int: "mono f \<Longrightarrow> f (A \<inter> B) \<subseteq> f A \<inter> f B"
  by (fact mono_inf)


subsubsection {* Binary union *}

abbreviation union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "Un" 65) where
  "union \<equiv> sup"

notation (xsymbols)
  union  (infixl "\<union>" 65)

notation (HTML output)
  union  (infixl "\<union>" 65)

lemma Un_def:
  "A \<union> B = {x. x \<in> A \<or> x \<in> B}"
  by (simp add: sup_fun_def Collect_def mem_def)

lemma Un_iff [simp]: "(c : A Un B) = (c:A | c:B)"
  by (unfold Un_def) blast

lemma UnI1 [elim?]: "c:A ==> c : A Un B"
  by simp

lemma UnI2 [elim?]: "c:B ==> c : A Un B"
  by simp

text {*
  \medskip Classical introduction rule: no commitment to @{prop A} vs
  @{prop B}.
*}

lemma UnCI [intro!]: "(c~:B ==> c:A) ==> c : A Un B"
  by auto

lemma UnE [elim!]: "c : A Un B ==> (c:A ==> P) ==> (c:B ==> P) ==> P"
  by (unfold Un_def) blast

lemma insert_def: "insert a B = {x. x = a} \<union> B"
  by (simp add: Collect_def mem_def insert_compr Un_def)

lemma mono_Un: "mono f \<Longrightarrow> f A \<union> f B \<subseteq> f (A \<union> B)"
  by (fact mono_sup)


subsubsection {* Set difference *}

lemma Diff_iff [simp]: "(c : A - B) = (c:A & c~:B)"
  by (simp add: mem_def fun_diff_def)

lemma DiffI [intro!]: "c : A ==> c ~: B ==> c : A - B"
  by simp

lemma DiffD1: "c : A - B ==> c : A"
  by simp

lemma DiffD2: "c : A - B ==> c : B ==> P"
  by simp

lemma DiffE [elim!]: "c : A - B ==> (c:A ==> c~:B ==> P) ==> P"
  by simp

lemma set_diff_eq: "A - B = {x. x : A & ~ x : B}" by blast

lemma Compl_eq_Diff_UNIV: "-A = (UNIV - A)"
by blast


subsubsection {* Augmenting a set -- @{const insert} *}

lemma insert_iff [simp]: "(a : insert b A) = (a = b | a:A)"
  by (unfold insert_def) blast

lemma insertI1: "a : insert a B"
  by simp

lemma insertI2: "a : B ==> a : insert b B"
  by simp

lemma insertE [elim!]: "a : insert b A ==> (a = b ==> P) ==> (a:A ==> P) ==> P"
  by (unfold insert_def) blast

lemma insertCI [intro!]: "(a~:B ==> a = b) ==> a: insert b B"
  -- {* Classical introduction rule. *}
  by auto

lemma subset_insert_iff: "(A \<subseteq> insert x B) = (if x:A then A - {x} \<subseteq> B else A \<subseteq> B)"
  by auto

lemma set_insert:
  assumes "x \<in> A"
  obtains B where "A = insert x B" and "x \<notin> B"
proof
  from assms show "A = insert x (A - {x})" by blast
next
  show "x \<notin> A - {x}" by blast
qed

lemma insert_ident: "x ~: A ==> x ~: B ==> (insert x A = insert x B) = (A = B)"
by auto

lemma insert_eq_iff: assumes "a \<notin> A" "b \<notin> B"
shows "insert a A = insert b B \<longleftrightarrow>
  (if a=b then A=B else \<exists>C. A = insert b C \<and> b \<notin> C \<and> B = insert a C \<and> a \<notin> C)"
  (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L
  show ?R
  proof cases
    assume "a=b" with assms `?L` show ?R by (simp add: insert_ident)
  next
    assume "a\<noteq>b"
    let ?C = "A - {b}"
    have "A = insert b ?C \<and> b \<notin> ?C \<and> B = insert a ?C \<and> a \<notin> ?C"
      using assms `?L` `a\<noteq>b` by auto
    thus ?R using `a\<noteq>b` by auto
  qed
next
  assume ?R thus ?L by(auto split: if_splits)
qed

subsubsection {* Singletons, using insert *}

lemma singletonI [intro!,no_atp]: "a : {a}"
    -- {* Redundant? But unlike @{text insertCI}, it proves the subgoal immediately! *}
  by (rule insertI1)

lemma singletonD [dest!,no_atp]: "b : {a} ==> b = a"
  by blast

lemmas singletonE = singletonD [elim_format]

lemma singleton_iff: "(b : {a}) = (b = a)"
  by blast

lemma singleton_inject [dest!]: "{a} = {b} ==> a = b"
  by blast

lemma singleton_insert_inj_eq [iff,no_atp]:
     "({b} = insert a A) = (a = b & A \<subseteq> {b})"
  by blast

lemma singleton_insert_inj_eq' [iff,no_atp]:
     "(insert a A = {b}) = (a = b & A \<subseteq> {b})"
  by blast

lemma subset_singletonD: "A \<subseteq> {x} ==> A = {} | A = {x}"
  by fast

lemma singleton_conv [simp]: "{x. x = a} = {a}"
  by blast

lemma singleton_conv2 [simp]: "{x. a = x} = {a}"
  by blast

lemma diff_single_insert: "A - {x} \<subseteq> B ==> x \<in> A ==> A \<subseteq> insert x B"
  by blast

lemma doubleton_eq_iff: "({a,b} = {c,d}) = (a=c & b=d | a=d & b=c)"
  by (blast elim: equalityE)


subsubsection {* Image of a set under a function *}

text {*
  Frequently @{term b} does not have the syntactic form of @{term "f x"}.
*}

definition image :: "('a => 'b) => 'a set => 'b set" (infixr "`" 90) where
  image_def [no_atp]: "f ` A = {y. EX x:A. y = f(x)}"

abbreviation
  range :: "('a => 'b) => 'b set" where -- "of function"
  "range f == f ` UNIV"

lemma image_eqI [simp, intro]: "b = f x ==> x:A ==> b : f`A"
  by (unfold image_def) blast

lemma imageI: "x : A ==> f x : f ` A"
  by (rule image_eqI) (rule refl)

lemma rev_image_eqI: "x:A ==> b = f x ==> b : f`A"
  -- {* This version's more effective when we already have the
    required @{term x}. *}
  by (unfold image_def) blast

lemma imageE [elim!]:
  "b : (%x. f x)`A ==> (!!x. b = f x ==> x:A ==> P) ==> P"
  -- {* The eta-expansion gives variable-name preservation. *}
  by (unfold image_def) blast

lemma image_Un: "f`(A Un B) = f`A Un f`B"
  by blast

lemma image_iff: "(z : f`A) = (EX x:A. z = f x)"
  by blast

lemma image_subset_iff [no_atp]: "(f`A \<subseteq> B) = (\<forall>x\<in>A. f x \<in> B)"
  -- {* This rewrite rule would confuse users if made default. *}
  by blast

lemma subset_image_iff: "(B \<subseteq> f`A) = (EX AA. AA \<subseteq> A & B = f`AA)"
  apply safe
   prefer 2 apply fast
  apply (rule_tac x = "{a. a : A & f a : B}" in exI, fast)
  done

lemma image_subsetI: "(!!x. x \<in> A ==> f x \<in> B) ==> f`A \<subseteq> B"
  -- {* Replaces the three steps @{text subsetI}, @{text imageE},
    @{text hypsubst}, but breaks too many existing proofs. *}
  by blast

text {*
  \medskip Range of a function -- just a translation for image!
*}

lemma image_ident [simp]: "(%x. x) ` Y = Y"
  by blast

lemma range_eqI: "b = f x ==> b \<in> range f"
  by simp

lemma rangeI: "f x \<in> range f"
  by simp

lemma rangeE [elim?]: "b \<in> range (\<lambda>x. f x) ==> (!!x. b = f x ==> P) ==> P"
  by blast

subsubsection {* Some rules with @{text "if"} *}

text{* Elimination of @{text"{x. \<dots> & x=t & \<dots>}"}. *}

lemma Collect_conv_if: "{x. x=a & P x} = (if P a then {a} else {})"
  by auto

lemma Collect_conv_if2: "{x. a=x & P x} = (if P a then {a} else {})"
  by auto

text {*
  Rewrite rules for boolean case-splitting: faster than @{text
  "split_if [split]"}.
*}

lemma split_if_eq1: "((if Q then x else y) = b) = ((Q --> x = b) & (~ Q --> y = b))"
  by (rule split_if)

lemma split_if_eq2: "(a = (if Q then x else y)) = ((Q --> a = x) & (~ Q --> a = y))"
  by (rule split_if)

text {*
  Split ifs on either side of the membership relation.  Not for @{text
  "[simp]"} -- can cause goals to blow up!
*}

lemma split_if_mem1: "((if Q then x else y) : b) = ((Q --> x : b) & (~ Q --> y : b))"
  by (rule split_if)

lemma split_if_mem2: "(a : (if Q then x else y)) = ((Q --> a : x) & (~ Q --> a : y))"
  by (rule split_if [where P="%S. a : S"])

lemmas split_ifs = if_bool_eq_conj split_if_eq1 split_if_eq2 split_if_mem1 split_if_mem2

(*Would like to add these, but the existing code only searches for the
  outer-level constant, which in this case is just Set.member; we instead need
  to use term-nets to associate patterns with rules.  Also, if a rule fails to
  apply, then the formula should be kept.
  [("uminus", Compl_iff RS iffD1), ("minus", [Diff_iff RS iffD1]),
   ("Int", [IntD1,IntD2]),
   ("Collect", [CollectD]), ("Inter", [InterD]), ("INTER", [INT_D])]
 *)


subsection {* Further operations and lemmas *}

subsubsection {* The ``proper subset'' relation *}

lemma psubsetI [intro!,no_atp]: "A \<subseteq> B ==> A \<noteq> B ==> A \<subset> B"
  by (unfold less_le) blast

lemma psubsetE [elim!,no_atp]: 
    "[|A \<subset> B;  [|A \<subseteq> B; ~ (B\<subseteq>A)|] ==> R|] ==> R"
  by (unfold less_le) blast

lemma psubset_insert_iff:
  "(A \<subset> insert x B) = (if x \<in> B then A \<subset> B else if x \<in> A then A - {x} \<subset> B else A \<subseteq> B)"
  by (auto simp add: less_le subset_insert_iff)

lemma psubset_eq: "(A \<subset> B) = (A \<subseteq> B & A \<noteq> B)"
  by (simp only: less_le)

lemma psubset_imp_subset: "A \<subset> B ==> A \<subseteq> B"
  by (simp add: psubset_eq)

lemma psubset_trans: "[| A \<subset> B; B \<subset> C |] ==> A \<subset> C"
apply (unfold less_le)
apply (auto dest: subset_antisym)
done

lemma psubsetD: "[| A \<subset> B; c \<in> A |] ==> c \<in> B"
apply (unfold less_le)
apply (auto dest: subsetD)
done

lemma psubset_subset_trans: "A \<subset> B ==> B \<subseteq> C ==> A \<subset> C"
  by (auto simp add: psubset_eq)

lemma subset_psubset_trans: "A \<subseteq> B ==> B \<subset> C ==> A \<subset> C"
  by (auto simp add: psubset_eq)

lemma psubset_imp_ex_mem: "A \<subset> B ==> \<exists>b. b \<in> (B - A)"
  by (unfold less_le) blast

lemma atomize_ball:
    "(!!x. x \<in> A ==> P x) == Trueprop (\<forall>x\<in>A. P x)"
  by (simp only: Ball_def atomize_all atomize_imp)

lemmas [symmetric, rulify] = atomize_ball
  and [symmetric, defn] = atomize_ball

lemma image_Pow_mono:
  assumes "f ` A \<le> B"
  shows "(image f) ` (Pow A) \<le> Pow B"
using assms by blast

lemma image_Pow_surj:
  assumes "f ` A = B"
  shows "(image f) ` (Pow A) = Pow B"
using assms unfolding Pow_def proof(auto)
  fix Y assume *: "Y \<le> f ` A"
  obtain X where X_def: "X = {x \<in> A. f x \<in> Y}" by blast
  have "f ` X = Y \<and> X \<le> A" unfolding X_def using * by auto
  thus "Y \<in> (image f) ` {X. X \<le> A}" by blast
qed

subsubsection {* Derived rules involving subsets. *}

text {* @{text insert}. *}

lemma subset_insertI: "B \<subseteq> insert a B"
  by (rule subsetI) (erule insertI2)

lemma subset_insertI2: "A \<subseteq> B \<Longrightarrow> A \<subseteq> insert b B"
  by blast

lemma subset_insert: "x \<notin> A ==> (A \<subseteq> insert x B) = (A \<subseteq> B)"
  by blast


text {* \medskip Finite Union -- the least upper bound of two sets. *}

lemma Un_upper1: "A \<subseteq> A \<union> B"
  by (fact sup_ge1)

lemma Un_upper2: "B \<subseteq> A \<union> B"
  by (fact sup_ge2)

lemma Un_least: "A \<subseteq> C ==> B \<subseteq> C ==> A \<union> B \<subseteq> C"
  by (fact sup_least)


text {* \medskip Finite Intersection -- the greatest lower bound of two sets. *}

lemma Int_lower1: "A \<inter> B \<subseteq> A"
  by (fact inf_le1)

lemma Int_lower2: "A \<inter> B \<subseteq> B"
  by (fact inf_le2)

lemma Int_greatest: "C \<subseteq> A ==> C \<subseteq> B ==> C \<subseteq> A \<inter> B"
  by (fact inf_greatest)


text {* \medskip Set difference. *}

lemma Diff_subset: "A - B \<subseteq> A"
  by blast

lemma Diff_subset_conv: "(A - B \<subseteq> C) = (A \<subseteq> B \<union> C)"
by blast


subsubsection {* Equalities involving union, intersection, inclusion, etc. *}

text {* @{text "{}"}. *}

lemma Collect_const [simp]: "{s. P} = (if P then UNIV else {})"
  -- {* supersedes @{text "Collect_False_empty"} *}
  by auto

lemma subset_empty [simp]: "(A \<subseteq> {}) = (A = {})"
  by (fact bot_unique)

lemma not_psubset_empty [iff]: "\<not> (A < {})"
  by (fact not_less_bot) (* FIXME: already simp *)

lemma Collect_empty_eq [simp]: "(Collect P = {}) = (\<forall>x. \<not> P x)"
by blast

lemma empty_Collect_eq [simp]: "({} = Collect P) = (\<forall>x. \<not> P x)"
by blast

lemma Collect_neg_eq: "{x. \<not> P x} = - {x. P x}"
  by blast

lemma Collect_disj_eq: "{x. P x | Q x} = {x. P x} \<union> {x. Q x}"
  by blast

lemma Collect_imp_eq: "{x. P x --> Q x} = -{x. P x} \<union> {x. Q x}"
  by blast

lemma Collect_conj_eq: "{x. P x & Q x} = {x. P x} \<inter> {x. Q x}"
  by blast


text {* \medskip @{text insert}. *}

lemma insert_is_Un: "insert a A = {a} Un A"
  -- {* NOT SUITABLE FOR REWRITING since @{text "{a} == insert a {}"} *}
  by blast

lemma insert_not_empty [simp]: "insert a A \<noteq> {}"
  by blast

lemmas empty_not_insert = insert_not_empty [symmetric]
declare empty_not_insert [simp]

lemma insert_absorb: "a \<in> A ==> insert a A = A"
  -- {* @{text "[simp]"} causes recursive calls when there are nested inserts *}
  -- {* with \emph{quadratic} running time *}
  by blast

lemma insert_absorb2 [simp]: "insert x (insert x A) = insert x A"
  by blast

lemma insert_commute: "insert x (insert y A) = insert y (insert x A)"
  by blast

lemma insert_subset [simp]: "(insert x A \<subseteq> B) = (x \<in> B & A \<subseteq> B)"
  by blast

lemma mk_disjoint_insert: "a \<in> A ==> \<exists>B. A = insert a B & a \<notin> B"
  -- {* use new @{text B} rather than @{text "A - {a}"} to avoid infinite unfolding *}
  apply (rule_tac x = "A - {a}" in exI, blast)
  done

lemma insert_Collect: "insert a (Collect P) = {u. u \<noteq> a --> P u}"
  by auto

lemma insert_inter_insert[simp]: "insert a A \<inter> insert a B = insert a (A \<inter> B)"
  by blast

lemma insert_disjoint [simp,no_atp]:
 "(insert a A \<inter> B = {}) = (a \<notin> B \<and> A \<inter> B = {})"
 "({} = insert a A \<inter> B) = (a \<notin> B \<and> {} = A \<inter> B)"
  by auto

lemma disjoint_insert [simp,no_atp]:
 "(B \<inter> insert a A = {}) = (a \<notin> B \<and> B \<inter> A = {})"
 "({} = A \<inter> insert b B) = (b \<notin> A \<and> {} = A \<inter> B)"
  by auto

text {* \medskip @{text image}. *}

lemma image_empty [simp]: "f`{} = {}"
  by blast

lemma image_insert [simp]: "f ` insert a B = insert (f a) (f`B)"
  by blast

lemma image_constant: "x \<in> A ==> (\<lambda>x. c) ` A = {c}"
  by auto

lemma image_constant_conv: "(%x. c) ` A = (if A = {} then {} else {c})"
by auto

lemma image_image: "f ` (g ` A) = (\<lambda>x. f (g x)) ` A"
by blast

lemma insert_image [simp]: "x \<in> A ==> insert (f x) (f`A) = f`A"
by blast

lemma image_is_empty [iff]: "(f`A = {}) = (A = {})"
by blast

lemma empty_is_image[iff]: "({} = f ` A) = (A = {})"
by blast


lemma image_Collect [no_atp]: "f ` {x. P x} = {f x | x. P x}"
  -- {* NOT suitable as a default simprule: the RHS isn't simpler than the LHS,
      with its implicit quantifier and conjunction.  Also image enjoys better
      equational properties than does the RHS. *}
  by blast

lemma if_image_distrib [simp]:
  "(\<lambda>x. if P x then f x else g x) ` S
    = (f ` (S \<inter> {x. P x})) \<union> (g ` (S \<inter> {x. \<not> P x}))"
  by (auto simp add: image_def)

lemma image_cong: "M = N ==> (!!x. x \<in> N ==> f x = g x) ==> f`M = g`N"
  by (simp add: image_def)

lemma image_Int_subset: "f`(A Int B) <= f`A Int f`B"
by blast

lemma image_diff_subset: "f`A - f`B <= f`(A - B)"
by blast


text {* \medskip @{text range}. *}

lemma full_SetCompr_eq [no_atp]: "{u. \<exists>x. u = f x} = range f"
  by auto

lemma range_composition: "range (\<lambda>x. f (g x)) = f`range g"
by (subst image_image, simp)


text {* \medskip @{text Int} *}

lemma Int_absorb: "A \<inter> A = A"
  by (fact inf_idem) (* already simp *)

lemma Int_left_absorb: "A \<inter> (A \<inter> B) = A \<inter> B"
  by (fact inf_left_idem)

lemma Int_commute: "A \<inter> B = B \<inter> A"
  by (fact inf_commute)

lemma Int_left_commute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
  by (fact inf_left_commute)

lemma Int_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
  by (fact inf_assoc)

lemmas Int_ac = Int_assoc Int_left_absorb Int_commute Int_left_commute
  -- {* Intersection is an AC-operator *}

lemma Int_absorb1: "B \<subseteq> A ==> A \<inter> B = B"
  by (fact inf_absorb2)

lemma Int_absorb2: "A \<subseteq> B ==> A \<inter> B = A"
  by (fact inf_absorb1)

lemma Int_empty_left: "{} \<inter> B = {}"
  by (fact inf_bot_left) (* already simp *)

lemma Int_empty_right: "A \<inter> {} = {}"
  by (fact inf_bot_right) (* already simp *)

lemma disjoint_eq_subset_Compl: "(A \<inter> B = {}) = (A \<subseteq> -B)"
  by blast

lemma disjoint_iff_not_equal: "(A \<inter> B = {}) = (\<forall>x\<in>A. \<forall>y\<in>B. x \<noteq> y)"
  by blast

lemma Int_UNIV_left: "UNIV \<inter> B = B"
  by (fact inf_top_left) (* already simp *)

lemma Int_UNIV_right: "A \<inter> UNIV = A"
  by (fact inf_top_right) (* already simp *)

lemma Int_Un_distrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by (fact inf_sup_distrib1)

lemma Int_Un_distrib2: "(B \<union> C) \<inter> A = (B \<inter> A) \<union> (C \<inter> A)"
  by (fact inf_sup_distrib2)

lemma Int_UNIV [simp,no_atp]: "(A \<inter> B = UNIV) = (A = UNIV & B = UNIV)"
  by (fact inf_eq_top_iff) (* already simp *)

lemma Int_subset_iff [no_atp, simp]: "(C \<subseteq> A \<inter> B) = (C \<subseteq> A & C \<subseteq> B)"
  by (fact le_inf_iff)

lemma Int_Collect: "(x \<in> A \<inter> {x. P x}) = (x \<in> A & P x)"
  by blast


text {* \medskip @{text Un}. *}

lemma Un_absorb: "A \<union> A = A"
  by (fact sup_idem) (* already simp *)

lemma Un_left_absorb: "A \<union> (A \<union> B) = A \<union> B"
  by (fact sup_left_idem)

lemma Un_commute: "A \<union> B = B \<union> A"
  by (fact sup_commute)

lemma Un_left_commute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
  by (fact sup_left_commute)

lemma Un_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
  by (fact sup_assoc)

lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute
  -- {* Union is an AC-operator *}

lemma Un_absorb1: "A \<subseteq> B ==> A \<union> B = B"
  by (fact sup_absorb2)

lemma Un_absorb2: "B \<subseteq> A ==> A \<union> B = A"
  by (fact sup_absorb1)

lemma Un_empty_left: "{} \<union> B = B"
  by (fact sup_bot_left) (* already simp *)

lemma Un_empty_right: "A \<union> {} = A"
  by (fact sup_bot_right) (* already simp *)

lemma Un_UNIV_left: "UNIV \<union> B = UNIV"
  by (fact sup_top_left) (* already simp *)

lemma Un_UNIV_right: "A \<union> UNIV = UNIV"
  by (fact sup_top_right) (* already simp *)

lemma Un_insert_left [simp]: "(insert a B) \<union> C = insert a (B \<union> C)"
  by blast

lemma Un_insert_right [simp]: "A \<union> (insert a B) = insert a (A \<union> B)"
  by blast

lemma Int_insert_left:
    "(insert a B) Int C = (if a \<in> C then insert a (B \<inter> C) else B \<inter> C)"
  by auto

lemma Int_insert_left_if0[simp]:
    "a \<notin> C \<Longrightarrow> (insert a B) Int C = B \<inter> C"
  by auto

lemma Int_insert_left_if1[simp]:
    "a \<in> C \<Longrightarrow> (insert a B) Int C = insert a (B Int C)"
  by auto

lemma Int_insert_right:
    "A \<inter> (insert a B) = (if a \<in> A then insert a (A \<inter> B) else A \<inter> B)"
  by auto

lemma Int_insert_right_if0[simp]:
    "a \<notin> A \<Longrightarrow> A Int (insert a B) = A Int B"
  by auto

lemma Int_insert_right_if1[simp]:
    "a \<in> A \<Longrightarrow> A Int (insert a B) = insert a (A Int B)"
  by auto

lemma Un_Int_distrib: "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
  by (fact sup_inf_distrib1)

lemma Un_Int_distrib2: "(B \<inter> C) \<union> A = (B \<union> A) \<inter> (C \<union> A)"
  by (fact sup_inf_distrib2)

lemma Un_Int_crazy:
    "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
  by blast

lemma subset_Un_eq: "(A \<subseteq> B) = (A \<union> B = B)"
  by (fact le_iff_sup)

lemma Un_empty [iff]: "(A \<union> B = {}) = (A = {} & B = {})"
  by (fact sup_eq_bot_iff) (* FIXME: already simp *)

lemma Un_subset_iff [no_atp, simp]: "(A \<union> B \<subseteq> C) = (A \<subseteq> C & B \<subseteq> C)"
  by (fact le_sup_iff)

lemma Un_Diff_Int: "(A - B) \<union> (A \<inter> B) = A"
  by blast

lemma Diff_Int2: "A \<inter> C - B \<inter> C = A \<inter> C - B"
  by blast


text {* \medskip Set complement *}

lemma Compl_disjoint [simp]: "A \<inter> -A = {}"
  by (fact inf_compl_bot)

lemma Compl_disjoint2 [simp]: "-A \<inter> A = {}"
  by (fact compl_inf_bot)

lemma Compl_partition: "A \<union> -A = UNIV"
  by (fact sup_compl_top)

lemma Compl_partition2: "-A \<union> A = UNIV"
  by (fact compl_sup_top)

lemma double_complement: "- (-A) = (A::'a set)"
  by (fact double_compl) (* already simp *)

lemma Compl_Un: "-(A \<union> B) = (-A) \<inter> (-B)"
  by (fact compl_sup) (* already simp *)

lemma Compl_Int: "-(A \<inter> B) = (-A) \<union> (-B)"
  by (fact compl_inf) (* already simp *)

lemma subset_Compl_self_eq: "(A \<subseteq> -A) = (A = {})"
  by blast

lemma Un_Int_assoc_eq: "((A \<inter> B) \<union> C = A \<inter> (B \<union> C)) = (C \<subseteq> A)"
  -- {* Halmos, Naive Set Theory, page 16. *}
  by blast

lemma Compl_UNIV_eq: "-UNIV = {}"
  by (fact compl_top_eq) (* already simp *)

lemma Compl_empty_eq: "-{} = UNIV"
  by (fact compl_bot_eq) (* already simp *)

lemma Compl_subset_Compl_iff [iff]: "(-A \<subseteq> -B) = (B \<subseteq> A)"
  by (fact compl_le_compl_iff) (* FIXME: already simp *)

lemma Compl_eq_Compl_iff [iff]: "(-A = -B) = (A = (B::'a set))"
  by (fact compl_eq_compl_iff) (* FIXME: already simp *)

lemma Compl_insert: "- insert x A = (-A) - {x}"
  by blast

text {* \medskip Bounded quantifiers.

  The following are not added to the default simpset because
  (a) they duplicate the body and (b) there are no similar rules for @{text Int}. *}

lemma ball_Un: "(\<forall>x \<in> A \<union> B. P x) = ((\<forall>x\<in>A. P x) & (\<forall>x\<in>B. P x))"
  by blast

lemma bex_Un: "(\<exists>x \<in> A \<union> B. P x) = ((\<exists>x\<in>A. P x) | (\<exists>x\<in>B. P x))"
  by blast


text {* \medskip Set difference. *}

lemma Diff_eq: "A - B = A \<inter> (-B)"
  by blast

lemma Diff_eq_empty_iff [simp,no_atp]: "(A - B = {}) = (A \<subseteq> B)"
  by blast

lemma Diff_cancel [simp]: "A - A = {}"
  by blast

lemma Diff_idemp [simp]: "(A - B) - B = A - (B::'a set)"
by blast

lemma Diff_triv: "A \<inter> B = {} ==> A - B = A"
  by (blast elim: equalityE)

lemma empty_Diff [simp]: "{} - A = {}"
  by blast

lemma Diff_empty [simp]: "A - {} = A"
  by blast

lemma Diff_UNIV [simp]: "A - UNIV = {}"
  by blast

lemma Diff_insert0 [simp,no_atp]: "x \<notin> A ==> A - insert x B = A - B"
  by blast

lemma Diff_insert: "A - insert a B = A - B - {a}"
  -- {* NOT SUITABLE FOR REWRITING since @{text "{a} == insert a 0"} *}
  by blast

lemma Diff_insert2: "A - insert a B = A - {a} - B"
  -- {* NOT SUITABLE FOR REWRITING since @{text "{a} == insert a 0"} *}
  by blast

lemma insert_Diff_if: "insert x A - B = (if x \<in> B then A - B else insert x (A - B))"
  by auto

lemma insert_Diff1 [simp]: "x \<in> B ==> insert x A - B = A - B"
  by blast

lemma insert_Diff_single[simp]: "insert a (A - {a}) = insert a A"
by blast

lemma insert_Diff: "a \<in> A ==> insert a (A - {a}) = A"
  by blast

lemma Diff_insert_absorb: "x \<notin> A ==> (insert x A) - {x} = A"
  by auto

lemma Diff_disjoint [simp]: "A \<inter> (B - A) = {}"
  by blast

lemma Diff_partition: "A \<subseteq> B ==> A \<union> (B - A) = B"
  by blast

lemma double_diff: "A \<subseteq> B ==> B \<subseteq> C ==> B - (C - A) = A"
  by blast

lemma Un_Diff_cancel [simp]: "A \<union> (B - A) = A \<union> B"
  by blast

lemma Un_Diff_cancel2 [simp]: "(B - A) \<union> A = B \<union> A"
  by blast

lemma Diff_Un: "A - (B \<union> C) = (A - B) \<inter> (A - C)"
  by blast

lemma Diff_Int: "A - (B \<inter> C) = (A - B) \<union> (A - C)"
  by blast

lemma Un_Diff: "(A \<union> B) - C = (A - C) \<union> (B - C)"
  by blast

lemma Int_Diff: "(A \<inter> B) - C = A \<inter> (B - C)"
  by blast

lemma Diff_Int_distrib: "C \<inter> (A - B) = (C \<inter> A) - (C \<inter> B)"
  by blast

lemma Diff_Int_distrib2: "(A - B) \<inter> C = (A \<inter> C) - (B \<inter> C)"
  by blast

lemma Diff_Compl [simp]: "A - (- B) = A \<inter> B"
  by auto

lemma Compl_Diff_eq [simp]: "- (A - B) = -A \<union> B"
  by blast


text {* \medskip Quantification over type @{typ bool}. *}

lemma bool_induct: "P True \<Longrightarrow> P False \<Longrightarrow> P x"
  by (cases x) auto

lemma all_bool_eq: "(\<forall>b. P b) \<longleftrightarrow> P True \<and> P False"
  by (auto intro: bool_induct)

lemma bool_contrapos: "P x \<Longrightarrow> \<not> P False \<Longrightarrow> P True"
  by (cases x) auto

lemma ex_bool_eq: "(\<exists>b. P b) \<longleftrightarrow> P True \<or> P False"
  by (auto intro: bool_contrapos)

lemma UNIV_bool [no_atp]: "UNIV = {False, True}"
  by (auto intro: bool_induct)

text {* \medskip @{text Pow} *}

lemma Pow_empty [simp]: "Pow {} = {{}}"
  by (auto simp add: Pow_def)

lemma Pow_insert: "Pow (insert a A) = Pow A \<union> (insert a ` Pow A)"
  by (blast intro: image_eqI [where ?x = "u - {a}", standard])

lemma Pow_Compl: "Pow (- A) = {-B | B. A \<in> Pow B}"
  by (blast intro: exI [where ?x = "- u", standard])

lemma Pow_UNIV [simp]: "Pow UNIV = UNIV"
  by blast

lemma Un_Pow_subset: "Pow A \<union> Pow B \<subseteq> Pow (A \<union> B)"
  by blast

lemma Pow_Int_eq [simp]: "Pow (A \<inter> B) = Pow A \<inter> Pow B"
  by blast


text {* \medskip Miscellany. *}

lemma set_eq_subset: "(A = B) = (A \<subseteq> B & B \<subseteq> A)"
  by blast

lemma subset_iff [no_atp]: "(A \<subseteq> B) = (\<forall>t. t \<in> A --> t \<in> B)"
  by blast

lemma subset_iff_psubset_eq: "(A \<subseteq> B) = ((A \<subset> B) | (A = B))"
  by (unfold less_le) blast

lemma all_not_in_conv [simp]: "(\<forall>x. x \<notin> A) = (A = {})"
  by blast

lemma ex_in_conv: "(\<exists>x. x \<in> A) = (A \<noteq> {})"
  by blast

lemma distinct_lemma: "f x \<noteq> f y ==> x \<noteq> y"
  by iprover

lemma ball_simps [simp, no_atp]:
  "\<And>A P Q. (\<forall>x\<in>A. P x \<or> Q) \<longleftrightarrow> ((\<forall>x\<in>A. P x) \<or> Q)"
  "\<And>A P Q. (\<forall>x\<in>A. P \<or> Q x) \<longleftrightarrow> (P \<or> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P \<longrightarrow> Q x) \<longleftrightarrow> (P \<longrightarrow> (\<forall>x\<in>A. Q x))"
  "\<And>A P Q. (\<forall>x\<in>A. P x \<longrightarrow> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<longrightarrow> Q)"
  "\<And>P. (\<forall>x\<in>{}. P x) \<longleftrightarrow> True"
  "\<And>P. (\<forall>x\<in>UNIV. P x) \<longleftrightarrow> (\<forall>x. P x)"
  "\<And>a B P. (\<forall>x\<in>insert a B. P x) \<longleftrightarrow> (P a \<and> (\<forall>x\<in>B. P x))"
  "\<And>P Q. (\<forall>x\<in>Collect Q. P x) \<longleftrightarrow> (\<forall>x. Q x \<longrightarrow> P x)"
  "\<And>A P f. (\<forall>x\<in>f`A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P (f x))"
  "\<And>A P. (\<not> (\<forall>x\<in>A. P x)) \<longleftrightarrow> (\<exists>x\<in>A. \<not> P x)"
  by auto

lemma bex_simps [simp, no_atp]:
  "\<And>A P Q. (\<exists>x\<in>A. P x \<and> Q) \<longleftrightarrow> ((\<exists>x\<in>A. P x) \<and> Q)"
  "\<And>A P Q. (\<exists>x\<in>A. P \<and> Q x) \<longleftrightarrow> (P \<and> (\<exists>x\<in>A. Q x))"
  "\<And>P. (\<exists>x\<in>{}. P x) \<longleftrightarrow> False"
  "\<And>P. (\<exists>x\<in>UNIV. P x) \<longleftrightarrow> (\<exists>x. P x)"
  "\<And>a B P. (\<exists>x\<in>insert a B. P x) \<longleftrightarrow> (P a | (\<exists>x\<in>B. P x))"
  "\<And>P Q. (\<exists>x\<in>Collect Q. P x) \<longleftrightarrow> (\<exists>x. Q x \<and> P x)"
  "\<And>A P f. (\<exists>x\<in>f`A. P x) \<longleftrightarrow> (\<exists>x\<in>A. P (f x))"
  "\<And>A P. (\<not>(\<exists>x\<in>A. P x)) \<longleftrightarrow> (\<forall>x\<in>A. \<not> P x)"
  by auto


subsubsection {* Monotonicity of various operations *}

lemma image_mono: "A \<subseteq> B ==> f`A \<subseteq> f`B"
  by blast

lemma Pow_mono: "A \<subseteq> B ==> Pow A \<subseteq> Pow B"
  by blast

lemma insert_mono: "C \<subseteq> D ==> insert a C \<subseteq> insert a D"
  by blast

lemma Un_mono: "A \<subseteq> C ==> B \<subseteq> D ==> A \<union> B \<subseteq> C \<union> D"
  by (fact sup_mono)

lemma Int_mono: "A \<subseteq> C ==> B \<subseteq> D ==> A \<inter> B \<subseteq> C \<inter> D"
  by (fact inf_mono)

lemma Diff_mono: "A \<subseteq> C ==> D \<subseteq> B ==> A - B \<subseteq> C - D"
  by blast

lemma Compl_anti_mono: "A \<subseteq> B ==> -B \<subseteq> -A"
  by (fact compl_mono)

text {* \medskip Monotonicity of implications. *}

lemma in_mono: "A \<subseteq> B ==> x \<in> A --> x \<in> B"
  apply (rule impI)
  apply (erule subsetD, assumption)
  done

lemma conj_mono: "P1 --> Q1 ==> P2 --> Q2 ==> (P1 & P2) --> (Q1 & Q2)"
  by iprover

lemma disj_mono: "P1 --> Q1 ==> P2 --> Q2 ==> (P1 | P2) --> (Q1 | Q2)"
  by iprover

lemma imp_mono: "Q1 --> P1 ==> P2 --> Q2 ==> (P1 --> P2) --> (Q1 --> Q2)"
  by iprover

lemma imp_refl: "P --> P" ..

lemma not_mono: "Q --> P ==> ~ P --> ~ Q"
  by iprover

lemma ex_mono: "(!!x. P x --> Q x) ==> (EX x. P x) --> (EX x. Q x)"
  by iprover

lemma all_mono: "(!!x. P x --> Q x) ==> (ALL x. P x) --> (ALL x. Q x)"
  by iprover

lemma Collect_mono: "(!!x. P x --> Q x) ==> Collect P \<subseteq> Collect Q"
  by blast

lemma Int_Collect_mono:
    "A \<subseteq> B ==> (!!x. x \<in> A ==> P x --> Q x) ==> A \<inter> Collect P \<subseteq> B \<inter> Collect Q"
  by blast

lemmas basic_monos =
  subset_refl imp_refl disj_mono conj_mono
  ex_mono Collect_mono in_mono

lemma eq_to_mono: "a = b ==> c = d ==> b --> d ==> a --> c"
  by iprover


subsubsection {* Inverse image of a function *}

definition vimage :: "('a => 'b) => 'b set => 'a set" (infixr "-`" 90) where
  "f -` B == {x. f x : B}"

lemma vimage_eq [simp]: "(a : f -` B) = (f a : B)"
  by (unfold vimage_def) blast

lemma vimage_singleton_eq: "(a : f -` {b}) = (f a = b)"
  by simp

lemma vimageI [intro]: "f a = b ==> b:B ==> a : f -` B"
  by (unfold vimage_def) blast

lemma vimageI2: "f a : A ==> a : f -` A"
  by (unfold vimage_def) fast

lemma vimageE [elim!]: "a: f -` B ==> (!!x. f a = x ==> x:B ==> P) ==> P"
  by (unfold vimage_def) blast

lemma vimageD: "a : f -` A ==> f a : A"
  by (unfold vimage_def) fast

lemma vimage_empty [simp]: "f -` {} = {}"
  by blast

lemma vimage_Compl: "f -` (-A) = -(f -` A)"
  by blast

lemma vimage_Un [simp]: "f -` (A Un B) = (f -` A) Un (f -` B)"
  by blast

lemma vimage_Int [simp]: "f -` (A Int B) = (f -` A) Int (f -` B)"
  by fast

lemma vimage_Collect_eq [simp]: "f -` Collect P = {y. P (f y)}"
  by blast

lemma vimage_Collect: "(!!x. P (f x) = Q x) ==> f -` (Collect P) = Collect Q"
  by blast

lemma vimage_insert: "f-`(insert a B) = (f-`{a}) Un (f-`B)"
  -- {* NOT suitable for rewriting because of the recurrence of @{term "{a}"}. *}
  by blast

lemma vimage_Diff: "f -` (A - B) = (f -` A) - (f -` B)"
  by blast

lemma vimage_UNIV [simp]: "f -` UNIV = UNIV"
  by blast

lemma vimage_mono: "A \<subseteq> B ==> f -` A \<subseteq> f -` B"
  -- {* monotonicity *}
  by blast

lemma vimage_image_eq [no_atp]: "f -` (f ` A) = {y. EX x:A. f x = f y}"
by (blast intro: sym)

lemma image_vimage_subset: "f ` (f -` A) <= A"
by blast

lemma image_vimage_eq [simp]: "f ` (f -` A) = A Int range f"
by blast

lemma vimage_const [simp]: "((\<lambda>x. c) -` A) = (if c \<in> A then UNIV else {})"
  by auto

lemma vimage_if [simp]: "((\<lambda>x. if x \<in> B then c else d) -` A) = 
   (if c \<in> A then (if d \<in> A then UNIV else B)
    else if d \<in> A then -B else {})"  
  by (auto simp add: vimage_def) 

lemma vimage_inter_cong:
  "(\<And> w. w \<in> S \<Longrightarrow> f w = g w) \<Longrightarrow> f -` y \<inter> S = g -` y \<inter> S"
  by auto

lemma vimage_ident [simp]: "(%x. x) -` Y = Y"
  by blast


subsubsection {* Getting the Contents of a Singleton Set *}

definition the_elem :: "'a set \<Rightarrow> 'a" where
  "the_elem X = (THE x. X = {x})"

lemma the_elem_eq [simp]: "the_elem {x} = x"
  by (simp add: the_elem_def)


subsubsection {* Least value operator *}

lemma Least_mono:
  "mono (f::'a::order => 'b::order) ==> EX x:S. ALL y:S. x <= y
    ==> (LEAST y. y : f ` S) = f (LEAST x. x : S)"
    -- {* Courtesy of Stephan Merz *}
  apply clarify
  apply (erule_tac P = "%x. x : S" in LeastI2_order, fast)
  apply (rule LeastI2_order)
  apply (auto elim: monoD intro!: order_antisym)
  done

subsection {* Misc *}

text {* Rudimentary code generation *}

lemma insert_code [code]: "insert y A x \<longleftrightarrow> y = x \<or> A x"
  by (auto simp add: insert_compr Collect_def mem_def)

lemma vimage_code [code]: "(f -` A) x = A (f x)"
  by (simp add: vimage_def Collect_def mem_def)

hide_const (open) member not_member

text {* Misc theorem and ML bindings *}

lemmas equalityI = subset_antisym

ML {*
val Ball_def = @{thm Ball_def}
val Bex_def = @{thm Bex_def}
val CollectD = @{thm CollectD}
val CollectE = @{thm CollectE}
val CollectI = @{thm CollectI}
val Collect_conj_eq = @{thm Collect_conj_eq}
val Collect_mem_eq = @{thm Collect_mem_eq}
val IntD1 = @{thm IntD1}
val IntD2 = @{thm IntD2}
val IntE = @{thm IntE}
val IntI = @{thm IntI}
val Int_Collect = @{thm Int_Collect}
val UNIV_I = @{thm UNIV_I}
val UNIV_witness = @{thm UNIV_witness}
val UnE = @{thm UnE}
val UnI1 = @{thm UnI1}
val UnI2 = @{thm UnI2}
val ballE = @{thm ballE}
val ballI = @{thm ballI}
val bexCI = @{thm bexCI}
val bexE = @{thm bexE}
val bexI = @{thm bexI}
val bex_triv = @{thm bex_triv}
val bspec = @{thm bspec}
val contra_subsetD = @{thm contra_subsetD}
val distinct_lemma = @{thm distinct_lemma}
val equalityCE = @{thm equalityCE}
val equalityD1 = @{thm equalityD1}
val equalityD2 = @{thm equalityD2}
val equalityE = @{thm equalityE}
val equalityI = @{thm equalityI}
val imageE = @{thm imageE}
val imageI = @{thm imageI}
val image_Un = @{thm image_Un}
val image_insert = @{thm image_insert}
val insert_commute = @{thm insert_commute}
val insert_iff = @{thm insert_iff}
val mem_Collect_eq = @{thm mem_Collect_eq}
val rangeE = @{thm rangeE}
val rangeI = @{thm rangeI}
val range_eqI = @{thm range_eqI}
val subsetCE = @{thm subsetCE}
val subsetD = @{thm subsetD}
val subsetI = @{thm subsetI}
val subset_refl = @{thm subset_refl}
val subset_trans = @{thm subset_trans}
val vimageD = @{thm vimageD}
val vimageE = @{thm vimageE}
val vimageI = @{thm vimageI}
val vimageI2 = @{thm vimageI2}
val vimage_Collect = @{thm vimage_Collect}
val vimage_Int = @{thm vimage_Int}
val vimage_Un = @{thm vimage_Un}
*}

end
