(*  Title:      HOL/Set.thy
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
*)

header {* Set theory for higher-order logic *}

theory Set
imports Lattices
begin

subsection {* Sets as predicates *}

global

types 'a set = "'a => bool"

consts
  Collect       :: "('a => bool) => 'a set"              -- "comprehension"
  "op :"        :: "'a => 'a set => bool"                -- "membership"

local

notation
  "op :"  ("op :") and
  "op :"  ("(_/ : _)" [50, 51] 50)

defs
  mem_def [code]: "x : S == S x"
  Collect_def [code]: "Collect P == P"

abbreviation
  "not_mem x A == ~ (x : A)" -- "non-membership"

notation
  not_mem  ("op ~:") and
  not_mem  ("(_/ ~: _)" [50, 51] 50)

notation (xsymbols)
  "op :"  ("op \<in>") and
  "op :"  ("(_/ \<in> _)" [50, 51] 50) and
  not_mem  ("op \<notin>") and
  not_mem  ("(_/ \<notin> _)" [50, 51] 50)

notation (HTML output)
  "op :"  ("op \<in>") and
  "op :"  ("(_/ \<in> _)" [50, 51] 50) and
  not_mem  ("op \<notin>") and
  not_mem  ("(_/ \<notin> _)" [50, 51] 50)

text {* Set comprehensions *}

syntax
  "@Coll"       :: "pttrn => bool => 'a set"              ("(1{_./ _})")

translations
  "{x. P}"      == "Collect (%x. P)"

syntax
  "@SetCompr"   :: "'a => idts => bool => 'a set"         ("(1{_ |/_./ _})")
  "@Collect"    :: "idt => 'a set => bool => 'a set"      ("(1{_ :/ _./ _})")

syntax (xsymbols)
  "@Collect"    :: "idt => 'a set => bool => 'a set"      ("(1{_ \<in>/ _./ _})")

translations
  "{x:A. P}"    => "{x. x:A & P}"

lemma mem_Collect_eq [iff]: "(a : {x. P(x)}) = P(a)"
  by (simp add: Collect_def mem_def)

lemma Collect_mem_eq [simp]: "{x. x:A} = A"
  by (simp add: Collect_def mem_def)

lemma CollectI: "P(a) ==> a : {x. P(x)}"
  by simp

lemma CollectD: "a : {x. P(x)} ==> P(a)"
  by simp

lemma Collect_cong: "(!!x. P x = Q x) ==> {x. P(x)} = {x. Q(x)}"
  by simp

text {*
Simproc for pulling @{text "x=t"} in @{text "{x. \<dots> & x=t & \<dots>}"}
to the front (and similarly for @{text "t=x"}):
*}

setup {*
let
  val Coll_perm_tac = rtac @{thm Collect_cong} 1 THEN rtac @{thm iffI} 1 THEN
    ALLGOALS(EVERY'[REPEAT_DETERM o (etac @{thm conjE}),
                    DEPTH_SOLVE_1 o (ares_tac [@{thm conjI}])])
  val defColl_regroup = Simplifier.simproc @{theory}
    "defined Collect" ["{x. P x & Q x}"]
    (Quantifier1.rearrange_Coll Coll_perm_tac)
in
  Simplifier.map_simpset (fn ss => ss addsimprocs [defColl_regroup])
end
*}

lemmas CollectE = CollectD [elim_format]

text {* Set enumerations *}

definition empty :: "'a set" ("{}") where
  bot_set_eq [symmetric]: "{} = bot"

definition insert :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  insert_compr: "insert a B = {x. x = a \<or> x \<in> B}"

syntax
  "@Finset"     :: "args => 'a set"                       ("{(_)}")

translations
  "{x, xs}"     == "CONST insert x {xs}"
  "{x}"         == "CONST insert x {}"


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

global

consts
  Ball          :: "'a set => ('a => bool) => bool"      -- "bounded universal quantifiers"
  Bex           :: "'a set => ('a => bool) => bool"      -- "bounded existential quantifiers"
  Bex1          :: "'a set => ('a => bool) => bool"      -- "bounded unique existential quantifiers"

local

defs
  Ball_def:     "Ball A P       == ALL x. x:A --> P(x)"
  Bex_def:      "Bex A P        == EX x. x:A & P(x)"
  Bex1_def:     "Bex1 A P       == EX! x. x:A & P(x)"

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
  "ALL x:A. P"  == "Ball A (%x. P)"
  "EX x:A. P"   == "Bex A (%x. P)"
  "EX! x:A. P"  == "Bex1 A (%x. P)"
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
  val Type (set_type, _) = @{typ "'a set"};
  val All_binder = Syntax.binder_name @{const_syntax "All"};
  val Ex_binder = Syntax.binder_name @{const_syntax "Ex"};
  val impl = @{const_syntax "op -->"};
  val conj = @{const_syntax "op &"};
  val sbset = @{const_syntax "subset"};
  val sbset_eq = @{const_syntax "subset_eq"};

  val trans =
   [((All_binder, impl, sbset), "_setlessAll"),
    ((All_binder, impl, sbset_eq), "_setleAll"),
    ((Ex_binder, conj, sbset), "_setlessEx"),
    ((Ex_binder, conj, sbset_eq), "_setleEx")];

  fun mk v v' c n P =
    if v = v' andalso not (Term.exists_subterm (fn Free (x, _) => x = v | _ => false) n)
    then Syntax.const c $ Syntax.mark_bound v' $ n $ P else raise Match;

  fun tr' q = (q,
    fn [Const ("_bound", _) $ Free (v, Type (T, _)), Const (c, _) $ (Const (d, _) $ (Const ("_bound", _) $ Free (v', _)) $ n) $ P] =>
         if T = (set_type) then case AList.lookup (op =) trans (q, c, d)
          of NONE => raise Match
           | SOME l => mk v v' l n P
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

parse_translation {*
  let
    val ex_tr = snd (mk_binder_tr ("EX ", "Ex"));

    fun nvars (Const ("_idts", _) $ _ $ idts) = nvars idts + 1
      | nvars _ = 1;

    fun setcompr_tr [e, idts, b] =
      let
        val eq = Syntax.const "op =" $ Bound (nvars idts) $ e;
        val P = Syntax.const "op &" $ eq $ b;
        val exP = ex_tr [idts, P];
      in Syntax.const "Collect" $ Term.absdummy (dummyT, exP) end;

  in [("@SetCompr", setcompr_tr)] end;
*}

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax Ball} "_Ball",
Syntax.preserve_binder_abs2_tr' @{const_syntax Bex} "_Bex"
] *} -- {* to avoid eta-contraction of body *}

print_translation {*
let
  val ex_tr' = snd (mk_binder_tr' ("Ex", "DUMMY"));

  fun setcompr_tr' [Abs (abs as (_, _, P))] =
    let
      fun check (Const ("Ex", _) $ Abs (_, _, P), n) = check (P, n + 1)
        | check (Const ("op &", _) $ (Const ("op =", _) $ Bound m $ e) $ P, n) =
            n > 0 andalso m = n andalso not (loose_bvar1 (P, n)) andalso
            ((0 upto (n - 1)) subset add_loose_bnos (e, 0, []))
        | check _ = false

        fun tr' (_ $ abs) =
          let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr' [abs]
          in Syntax.const "@SetCompr" $ e $ idts $ Q end;
    in if check (P, 0) then tr' P
       else let val (x as _ $ Free(xN,_), t) = atomic_abs_tr' abs
                val M = Syntax.const "@Coll" $ x $ t
            in case t of
                 Const("op &",_)
                   $ (Const("op :",_) $ (Const("_bound",_) $ Free(yN,_)) $ A)
                   $ P =>
                   if xN=yN then Syntax.const "@Collect" $ x $ A $ P else M
               | _ => M
            end
    end;
  in [("Collect", setcompr_tr')] end;
*}

setup {*
let
  val unfold_bex_tac = unfold_tac @{thms "Bex_def"};
  fun prove_bex_tac ss = unfold_bex_tac ss THEN Quantifier1.prove_one_point_ex_tac;
  val rearrange_bex = Quantifier1.rearrange_bex prove_bex_tac;
  val unfold_ball_tac = unfold_tac @{thms "Ball_def"};
  fun prove_ball_tac ss = unfold_ball_tac ss THEN Quantifier1.prove_one_point_all_tac;
  val rearrange_ball = Quantifier1.rearrange_ball prove_ball_tac;
  val defBEX_regroup = Simplifier.simproc @{theory}
    "defined BEX" ["EX x:A. P x & Q x"] rearrange_bex;
  val defBALL_regroup = Simplifier.simproc @{theory}
    "defined BALL" ["ALL x:A. P x --> Q x"] rearrange_ball;
in
  Simplifier.map_simpset (fn ss => ss addsimprocs [defBALL_regroup, defBEX_regroup])
end
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
  Simplifier.map_ss (fn ss => ss setmksimps (mksimps mksimps_pairs))
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

lemma subsetI [atp,intro!]: "(!!x. x:A ==> x:B) ==> A \<subseteq> B"
  by (auto simp add: mem_def intro: predicate1I)

text {*
  \medskip Map the type @{text "'a set => anything"} to just @{typ
  'a}; for overloading constants whose first argument has type @{typ
  "'a set"}.
*}

lemma subsetD [elim, intro?]: "A \<subseteq> B ==> c \<in> A ==> c \<in> B"
  -- {* Rule in Modus Ponens style. *}
  by (unfold mem_def) blast

lemma rev_subsetD [intro?]: "c \<in> A ==> A \<subseteq> B ==> c \<in> B"
  -- {* The same, with reversed premises for use with @{text erule} --
      cf @{text rev_mp}. *}
  by (rule subsetD)

text {*
  \medskip Converts @{prop "A \<subseteq> B"} to @{prop "x \<in> A ==> x \<in> B"}.
*}

lemma subsetCE [elim]: "A \<subseteq>  B ==> (c \<notin> A ==> P) ==> (c \<in> B ==> P) ==> P"
  -- {* Classical elimination rule. *}
  by (unfold mem_def) blast

lemma subset_eq: "A \<le> B = (\<forall>x\<in>A. x \<in> B)" by blast

lemma contra_subsetD: "A \<subseteq> B ==> c \<notin> B ==> c \<notin> A"
  by blast

lemma subset_refl [simp,atp]: "A \<subseteq> A"
  by (fact order_refl)

lemma subset_trans: "A \<subseteq> B ==> B \<subseteq> C ==> A \<subseteq> C"
  by (fact order_trans)

lemma set_rev_mp: "x:A ==> A \<subseteq> B ==> x:B"
  by (rule subsetD)

lemma set_mp: "A \<subseteq> B ==> x:A ==> x:B"
  by (rule subsetD)

lemmas basic_trans_rules [trans] =
  order_trans_rules set_rev_mp set_mp


subsubsection {* Equality *}

lemma set_ext: assumes prem: "(!!x. (x:A) = (x:B))" shows "A = B"
  apply (rule prem [THEN ext, THEN arg_cong, THEN box_equals])
   apply (rule Collect_mem_eq)
  apply (rule Collect_mem_eq)
  done

(* Due to Brian Huffman *)
lemma expand_set_eq: "(A = B) = (ALL x. (x:A) = (x:B))"
by(auto intro:set_ext)

lemma subset_antisym [intro!]: "A \<subseteq> B ==> B \<subseteq> A ==> A = B"
  -- {* Anti-symmetry of the subset relation. *}
  by (iprover intro: set_ext subsetD)

text {*
  \medskip Equality rules from ZF set theory -- are they appropriate
  here?
*}

lemma equalityD1: "A = B ==> A \<subseteq> B"
  by (simp add: subset_refl)

lemma equalityD2: "A = B ==> B \<subseteq> A"
  by (simp add: subset_refl)

text {*
  \medskip Be careful when adding this to the claset as @{text
  subset_empty} is in the simpset: @{prop "A = {}"} goes to @{prop "{}
  \<subseteq> A"} and @{prop "A \<subseteq> {}"} and then back to @{prop "A = {}"}!
*}

lemma equalityE: "A = B ==> (A \<subseteq> B ==> B \<subseteq> A ==> P) ==> P"
  by (simp add: subset_refl)

lemma equalityCE [elim]:
    "A = B ==> (c \<in> A ==> c \<in> B ==> P) ==> (c \<notin> A ==> c \<notin> B ==> P) ==> P"
  by blast

lemma eqset_imp_iff: "A = B ==> (x : A) = (x : B)"
  by simp

lemma eqelem_imp_iff: "x = y ==> (x : A) = (y : A)"
  by simp


subsubsection {* The universal set -- UNIV *}

definition UNIV :: "'a set" where
  top_set_eq [symmetric]: "UNIV = top"

lemma UNIV_def:
  "UNIV = {x. True}"
  by (simp add: top_set_eq [symmetric] top_fun_eq top_bool_eq Collect_def)

lemma UNIV_I [simp]: "x : UNIV"
  by (simp add: UNIV_def)

declare UNIV_I [intro]  -- {* unsafe makes it less likely to cause problems *}

lemma UNIV_witness [intro?]: "EX x. x : UNIV"
  by simp

lemma subset_UNIV [simp]: "A \<subseteq> UNIV"
  by (rule subsetI) (rule UNIV_I)

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


subsubsection {* The empty set *}

lemma empty_def:
  "{} = {x. False}"
  by (simp add: bot_set_eq [symmetric] bot_fun_eq bot_bool_eq Collect_def)

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
  by (simp add: subset_refl)


subsubsection {* Set complement *}

lemma Compl_iff [simp]: "(c \<in> -A) = (c \<notin> A)"
  by (simp add: mem_def fun_Compl_def bool_Compl_def)

lemma ComplI [intro!]: "(c \<in> A ==> False) ==> c \<in> -A"
  by (unfold mem_def fun_Compl_def bool_Compl_def) blast

text {*
  \medskip This form, with negated conclusion, works well with the
  Classical prover.  Negated assumptions behave like formulae on the
  right side of the notional turnstile ... *}

lemma ComplD [dest!]: "c : -A ==> c~:A"
  by (simp add: mem_def fun_Compl_def bool_Compl_def)

lemmas ComplE = ComplD [elim_format]

lemma Compl_eq: "- A = {x. ~ x : A}" by blast


subsubsection {* Binary union -- Un *}

definition union :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "Un" 65) where
  sup_set_eq [symmetric]: "A Un B = sup A B"

notation (xsymbols)
  union  (infixl "\<union>" 65)

notation (HTML output)
  union  (infixl "\<union>" 65)

lemma Un_def:
  "A \<union> B = {x. x \<in> A \<or> x \<in> B}"
  by (simp add: sup_fun_eq sup_bool_eq sup_set_eq [symmetric] Collect_def mem_def)

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
  apply (fold sup_set_eq)
  apply (erule mono_sup)
  done


subsubsection {* Binary intersection -- Int *}

definition inter :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set" (infixl "Int" 70) where
  inf_set_eq [symmetric]: "A Int B = inf A B"

notation (xsymbols)
  inter  (infixl "\<inter>" 70)

notation (HTML output)
  inter  (infixl "\<inter>" 70)

lemma Int_def:
  "A \<inter> B = {x. x \<in> A \<and> x \<in> B}"
  by (simp add: inf_fun_eq inf_bool_eq inf_set_eq [symmetric] Collect_def mem_def)

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
  apply (fold inf_set_eq)
  apply (erule mono_inf)
  done


subsubsection {* Set difference *}

lemma Diff_iff [simp]: "(c : A - B) = (c:A & c~:B)"
  by (simp add: mem_def fun_diff_def bool_diff_def)

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

subsubsection {* Singletons, using insert *}

lemma singletonI [intro!,noatp]: "a : {a}"
    -- {* Redundant? But unlike @{text insertCI}, it proves the subgoal immediately! *}
  by (rule insertI1)

lemma singletonD [dest!,noatp]: "b : {a} ==> b = a"
  by blast

lemmas singletonE = singletonD [elim_format]

lemma singleton_iff: "(b : {a}) = (b = a)"
  by blast

lemma singleton_inject [dest!]: "{a} = {b} ==> a = b"
  by blast

lemma singleton_insert_inj_eq [iff,noatp]:
     "({b} = insert a A) = (a = b & A \<subseteq> {b})"
  by blast

lemma singleton_insert_inj_eq' [iff,noatp]:
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
  image_def [noatp]: "f ` A = {y. EX x:A. y = f(x)}"

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

lemma image_subset_iff: "(f`A \<subseteq> B) = (\<forall>x\<in>A. f x \<in> B)"
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
  outer-level constant, which in this case is just "op :"; we instead need
  to use term-nets to associate patterns with rules.  Also, if a rule fails to
  apply, then the formula should be kept.
  [("HOL.uminus", Compl_iff RS iffD1), ("HOL.minus", [Diff_iff RS iffD1]),
   ("Int", [IntD1,IntD2]),
   ("Collect", [CollectD]), ("Inter", [InterD]), ("INTER", [INT_D])]
 *)


subsection {* Further operations and lemmas *}

subsubsection {* The ``proper subset'' relation *}

lemma psubsetI [intro!,noatp]: "A \<subseteq> B ==> A \<noteq> B ==> A \<subset> B"
  by (unfold less_le) blast

lemma psubsetE [elim!,noatp]: 
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
  by blast

lemma Un_upper2: "B \<subseteq> A \<union> B"
  by blast

lemma Un_least: "A \<subseteq> C ==> B \<subseteq> C ==> A \<union> B \<subseteq> C"
  by blast


text {* \medskip Finite Intersection -- the greatest lower bound of two sets. *}

lemma Int_lower1: "A \<inter> B \<subseteq> A"
  by blast

lemma Int_lower2: "A \<inter> B \<subseteq> B"
  by blast

lemma Int_greatest: "C \<subseteq> A ==> C \<subseteq> B ==> C \<subseteq> A \<inter> B"
  by blast


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
  by blast

lemma not_psubset_empty [iff]: "\<not> (A < {})"
  by (unfold less_le) blast

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

lemmas empty_not_insert = insert_not_empty [symmetric, standard]
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

lemma insert_disjoint [simp,noatp]:
 "(insert a A \<inter> B = {}) = (a \<notin> B \<and> A \<inter> B = {})"
 "({} = insert a A \<inter> B) = (a \<notin> B \<and> {} = A \<inter> B)"
  by auto

lemma disjoint_insert [simp,noatp]:
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


lemma image_Collect [noatp]: "f ` {x. P x} = {f x | x. P x}"
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


text {* \medskip @{text range}. *}

lemma full_SetCompr_eq [noatp]: "{u. \<exists>x. u = f x} = range f"
  by auto

lemma range_composition: "range (\<lambda>x. f (g x)) = f`range g"
by (subst image_image, simp)


text {* \medskip @{text Int} *}

lemma Int_absorb [simp]: "A \<inter> A = A"
  by blast

lemma Int_left_absorb: "A \<inter> (A \<inter> B) = A \<inter> B"
  by blast

lemma Int_commute: "A \<inter> B = B \<inter> A"
  by blast

lemma Int_left_commute: "A \<inter> (B \<inter> C) = B \<inter> (A \<inter> C)"
  by blast

lemma Int_assoc: "(A \<inter> B) \<inter> C = A \<inter> (B \<inter> C)"
  by blast

lemmas Int_ac = Int_assoc Int_left_absorb Int_commute Int_left_commute
  -- {* Intersection is an AC-operator *}

lemma Int_absorb1: "B \<subseteq> A ==> A \<inter> B = B"
  by blast

lemma Int_absorb2: "A \<subseteq> B ==> A \<inter> B = A"
  by blast

lemma Int_empty_left [simp]: "{} \<inter> B = {}"
  by blast

lemma Int_empty_right [simp]: "A \<inter> {} = {}"
  by blast

lemma disjoint_eq_subset_Compl: "(A \<inter> B = {}) = (A \<subseteq> -B)"
  by blast

lemma disjoint_iff_not_equal: "(A \<inter> B = {}) = (\<forall>x\<in>A. \<forall>y\<in>B. x \<noteq> y)"
  by blast

lemma Int_UNIV_left [simp]: "UNIV \<inter> B = B"
  by blast

lemma Int_UNIV_right [simp]: "A \<inter> UNIV = A"
  by blast

lemma Int_Un_distrib: "A \<inter> (B \<union> C) = (A \<inter> B) \<union> (A \<inter> C)"
  by blast

lemma Int_Un_distrib2: "(B \<union> C) \<inter> A = (B \<inter> A) \<union> (C \<inter> A)"
  by blast

lemma Int_UNIV [simp,noatp]: "(A \<inter> B = UNIV) = (A = UNIV & B = UNIV)"
  by blast

lemma Int_subset_iff [simp]: "(C \<subseteq> A \<inter> B) = (C \<subseteq> A & C \<subseteq> B)"
  by blast

lemma Int_Collect: "(x \<in> A \<inter> {x. P x}) = (x \<in> A & P x)"
  by blast


text {* \medskip @{text Un}. *}

lemma Un_absorb [simp]: "A \<union> A = A"
  by blast

lemma Un_left_absorb: "A \<union> (A \<union> B) = A \<union> B"
  by blast

lemma Un_commute: "A \<union> B = B \<union> A"
  by blast

lemma Un_left_commute: "A \<union> (B \<union> C) = B \<union> (A \<union> C)"
  by blast

lemma Un_assoc: "(A \<union> B) \<union> C = A \<union> (B \<union> C)"
  by blast

lemmas Un_ac = Un_assoc Un_left_absorb Un_commute Un_left_commute
  -- {* Union is an AC-operator *}

lemma Un_absorb1: "A \<subseteq> B ==> A \<union> B = B"
  by blast

lemma Un_absorb2: "B \<subseteq> A ==> A \<union> B = A"
  by blast

lemma Un_empty_left [simp]: "{} \<union> B = B"
  by blast

lemma Un_empty_right [simp]: "A \<union> {} = A"
  by blast

lemma Un_UNIV_left [simp]: "UNIV \<union> B = UNIV"
  by blast

lemma Un_UNIV_right [simp]: "A \<union> UNIV = UNIV"
  by blast

lemma Un_insert_left [simp]: "(insert a B) \<union> C = insert a (B \<union> C)"
  by blast

lemma Un_insert_right [simp]: "A \<union> (insert a B) = insert a (A \<union> B)"
  by blast

lemma Int_insert_left:
    "(insert a B) Int C = (if a \<in> C then insert a (B \<inter> C) else B \<inter> C)"
  by auto

lemma Int_insert_right:
    "A \<inter> (insert a B) = (if a \<in> A then insert a (A \<inter> B) else A \<inter> B)"
  by auto

lemma Un_Int_distrib: "A \<union> (B \<inter> C) = (A \<union> B) \<inter> (A \<union> C)"
  by blast

lemma Un_Int_distrib2: "(B \<inter> C) \<union> A = (B \<union> A) \<inter> (C \<union> A)"
  by blast

lemma Un_Int_crazy:
    "(A \<inter> B) \<union> (B \<inter> C) \<union> (C \<inter> A) = (A \<union> B) \<inter> (B \<union> C) \<inter> (C \<union> A)"
  by blast

lemma subset_Un_eq: "(A \<subseteq> B) = (A \<union> B = B)"
  by blast

lemma Un_empty [iff]: "(A \<union> B = {}) = (A = {} & B = {})"
  by blast

lemma Un_subset_iff [simp]: "(A \<union> B \<subseteq> C) = (A \<subseteq> C & B \<subseteq> C)"
  by blast

lemma Un_Diff_Int: "(A - B) \<union> (A \<inter> B) = A"
  by blast

lemma Diff_Int2: "A \<inter> C - B \<inter> C = A \<inter> C - B"
  by blast


text {* \medskip Set complement *}

lemma Compl_disjoint [simp]: "A \<inter> -A = {}"
  by blast

lemma Compl_disjoint2 [simp]: "-A \<inter> A = {}"
  by blast

lemma Compl_partition: "A \<union> -A = UNIV"
  by blast

lemma Compl_partition2: "-A \<union> A = UNIV"
  by blast

lemma double_complement [simp]: "- (-A) = (A::'a set)"
  by blast

lemma Compl_Un [simp]: "-(A \<union> B) = (-A) \<inter> (-B)"
  by blast

lemma Compl_Int [simp]: "-(A \<inter> B) = (-A) \<union> (-B)"
  by blast

lemma subset_Compl_self_eq: "(A \<subseteq> -A) = (A = {})"
  by blast

lemma Un_Int_assoc_eq: "((A \<inter> B) \<union> C = A \<inter> (B \<union> C)) = (C \<subseteq> A)"
  -- {* Halmos, Naive Set Theory, page 16. *}
  by blast

lemma Compl_UNIV_eq [simp]: "-UNIV = {}"
  by blast

lemma Compl_empty_eq [simp]: "-{} = UNIV"
  by blast

lemma Compl_subset_Compl_iff [iff]: "(-A \<subseteq> -B) = (B \<subseteq> A)"
  by blast

lemma Compl_eq_Compl_iff [iff]: "(-A = -B) = (A = (B::'a set))"
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

lemma Diff_eq_empty_iff [simp,noatp]: "(A - B = {}) = (A \<subseteq> B)"
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

lemma Diff_insert0 [simp,noatp]: "x \<notin> A ==> A - insert x B = A - B"
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

lemma subset_iff: "(A \<subseteq> B) = (\<forall>t. t \<in> A --> t \<in> B)"
  by blast

lemma subset_iff_psubset_eq: "(A \<subseteq> B) = ((A \<subset> B) | (A = B))"
  by (unfold less_le) blast

lemma all_not_in_conv [simp]: "(\<forall>x. x \<notin> A) = (A = {})"
  by blast

lemma ex_in_conv: "(\<exists>x. x \<in> A) = (A \<noteq> {})"
  by blast

lemma distinct_lemma: "f x \<noteq> f y ==> x \<noteq> y"
  by iprover


subsubsection {* Monotonicity of various operations *}

lemma image_mono: "A \<subseteq> B ==> f`A \<subseteq> f`B"
  by blast

lemma Pow_mono: "A \<subseteq> B ==> Pow A \<subseteq> Pow B"
  by blast

lemma insert_mono: "C \<subseteq> D ==> insert a C \<subseteq> insert a D"
  by blast

lemma Un_mono: "A \<subseteq> C ==> B \<subseteq> D ==> A \<union> B \<subseteq> C \<union> D"
  by blast

lemma Int_mono: "A \<subseteq> C ==> B \<subseteq> D ==> A \<inter> B \<subseteq> C \<inter> D"
  by blast

lemma Diff_mono: "A \<subseteq> C ==> D \<subseteq> B ==> A - B \<subseteq> C - D"
  by blast

lemma Compl_anti_mono: "A \<subseteq> B ==> -B \<subseteq> -A"
  by blast

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

lemma eq_to_mono2: "a = b ==> c = d ==> ~ b --> ~ d ==> ~ a --> ~ c"
  by iprover


subsubsection {* Inverse image of a function *}

constdefs
  vimage :: "('a => 'b) => 'b set => 'a set"    (infixr "-`" 90)
  [code del]: "f -` B == {x. f x : B}"

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

lemma vimage_image_eq [noatp]: "f -` (f ` A) = {y. EX x:A. f x = f y}"
by (blast intro: sym)

lemma image_vimage_subset: "f ` (f -` A) <= A"
by blast

lemma image_vimage_eq [simp]: "f ` (f -` A) = A Int range f"
by blast

lemma image_Int_subset: "f`(A Int B) <= f`A Int f`B"
by blast

lemma image_diff_subset: "f`A - f`B <= f`(A - B)"
by blast


subsubsection {* Getting the Contents of a Singleton Set *}

definition contents :: "'a set \<Rightarrow> 'a" where
  [code del]: "contents X = (THE x. X = {x})"

lemma contents_eq [simp]: "contents {x} = x"
  by (simp add: contents_def)


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
val eq_to_mono = @{thm eq_to_mono}
val eq_to_mono2 = @{thm eq_to_mono2}
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


subsection {* Complete lattices *}

notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65)

class complete_lattice = lattice + bot + top +
  fixes Inf :: "'a set \<Rightarrow> 'a" ("\<Sqinter>_" [900] 900)
    and Sup :: "'a set \<Rightarrow> 'a" ("\<Squnion>_" [900] 900)
  assumes Inf_lower: "x \<in> A \<Longrightarrow> \<Sqinter>A \<sqsubseteq> x"
     and Inf_greatest: "(\<And>x. x \<in> A \<Longrightarrow> z \<sqsubseteq> x) \<Longrightarrow> z \<sqsubseteq> \<Sqinter>A"
  assumes Sup_upper: "x \<in> A \<Longrightarrow> x \<sqsubseteq> \<Squnion>A"
     and Sup_least: "(\<And>x. x \<in> A \<Longrightarrow> x \<sqsubseteq> z) \<Longrightarrow> \<Squnion>A \<sqsubseteq> z"
begin

lemma Inf_Sup: "\<Sqinter>A = \<Squnion>{b. \<forall>a \<in> A. b \<le> a}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Sup_Inf:  "\<Squnion>A = \<Sqinter>{b. \<forall>a \<in> A. a \<le> b}"
  by (auto intro: antisym Inf_lower Inf_greatest Sup_upper Sup_least)

lemma Inf_Univ: "\<Sqinter>UNIV = \<Squnion>{}"
  unfolding Sup_Inf by auto

lemma Sup_Univ: "\<Squnion>UNIV = \<Sqinter>{}"
  unfolding Inf_Sup by auto

lemma Inf_insert: "\<Sqinter>insert a A = a \<sqinter> \<Sqinter>A"
  by (auto intro: le_infI le_infI1 le_infI2 antisym Inf_greatest Inf_lower)

lemma Sup_insert: "\<Squnion>insert a A = a \<squnion> \<Squnion>A"
  by (auto intro: le_supI le_supI1 le_supI2 antisym Sup_least Sup_upper)

lemma Inf_singleton [simp]:
  "\<Sqinter>{a} = a"
  by (auto intro: antisym Inf_lower Inf_greatest)

lemma Sup_singleton [simp]:
  "\<Squnion>{a} = a"
  by (auto intro: antisym Sup_upper Sup_least)

lemma Inf_insert_simp:
  "\<Sqinter>insert a A = (if A = {} then a else a \<sqinter> \<Sqinter>A)"
  by (cases "A = {}") (simp_all, simp add: Inf_insert)

lemma Sup_insert_simp:
  "\<Squnion>insert a A = (if A = {} then a else a \<squnion> \<Squnion>A)"
  by (cases "A = {}") (simp_all, simp add: Sup_insert)

lemma Inf_binary:
  "\<Sqinter>{a, b} = a \<sqinter> b"
  by (auto simp add: Inf_insert_simp)

lemma Sup_binary:
  "\<Squnion>{a, b} = a \<squnion> b"
  by (auto simp add: Sup_insert_simp)

lemma bot_def:
  "bot = \<Squnion>{}"
  by (auto intro: antisym Sup_least)

lemma top_def:
  "top = \<Sqinter>{}"
  by (auto intro: antisym Inf_greatest)

lemma sup_bot [simp]:
  "x \<squnion> bot = x"
  using bot_least [of x] by (simp add: le_iff_sup sup_commute)

lemma inf_top [simp]:
  "x \<sqinter> top = x"
  using top_greatest [of x] by (simp add: le_iff_inf inf_commute)

definition SUPR :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "SUPR A f = \<Squnion> (f ` A)"

definition INFI :: "'b set \<Rightarrow> ('b \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "INFI A f = \<Sqinter> (f ` A)"

end

syntax
  "_SUP1"     :: "pttrns => 'b => 'b"           ("(3SUP _./ _)" [0, 10] 10)
  "_SUP"      :: "pttrn => 'a set => 'b => 'b"  ("(3SUP _:_./ _)" [0, 10] 10)
  "_INF1"     :: "pttrns => 'b => 'b"           ("(3INF _./ _)" [0, 10] 10)
  "_INF"      :: "pttrn => 'a set => 'b => 'b"  ("(3INF _:_./ _)" [0, 10] 10)

translations
  "SUP x y. B"   == "SUP x. SUP y. B"
  "SUP x. B"     == "CONST SUPR CONST UNIV (%x. B)"
  "SUP x. B"     == "SUP x:CONST UNIV. B"
  "SUP x:A. B"   == "CONST SUPR A (%x. B)"
  "INF x y. B"   == "INF x. INF y. B"
  "INF x. B"     == "CONST INFI CONST UNIV (%x. B)"
  "INF x. B"     == "INF x:CONST UNIV. B"
  "INF x:A. B"   == "CONST INFI A (%x. B)"

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax SUPR} "_SUP",
Syntax.preserve_binder_abs2_tr' @{const_syntax INFI} "_INF"
] *} -- {* to avoid eta-contraction of body *}

context complete_lattice
begin

lemma le_SUPI: "i : A \<Longrightarrow> M i \<le> (SUP i:A. M i)"
  by (auto simp add: SUPR_def intro: Sup_upper)

lemma SUP_leI: "(\<And>i. i : A \<Longrightarrow> M i \<le> u) \<Longrightarrow> (SUP i:A. M i) \<le> u"
  by (auto simp add: SUPR_def intro: Sup_least)

lemma INF_leI: "i : A \<Longrightarrow> (INF i:A. M i) \<le> M i"
  by (auto simp add: INFI_def intro: Inf_lower)

lemma le_INFI: "(\<And>i. i : A \<Longrightarrow> u \<le> M i) \<Longrightarrow> u \<le> (INF i:A. M i)"
  by (auto simp add: INFI_def intro: Inf_greatest)

lemma SUP_const[simp]: "A \<noteq> {} \<Longrightarrow> (SUP i:A. M) = M"
  by (auto intro: antisym SUP_leI le_SUPI)

lemma INF_const[simp]: "A \<noteq> {} \<Longrightarrow> (INF i:A. M) = M"
  by (auto intro: antisym INF_leI le_INFI)

end


subsubsection {* @{typ bool} and @{typ "_ \<Rightarrow> _"} as complete lattice *}

instantiation bool :: complete_lattice
begin

definition
  Inf_bool_def: "\<Sqinter>A \<longleftrightarrow> (\<forall>x\<in>A. x)"

definition
  Sup_bool_def: "\<Squnion>A \<longleftrightarrow> (\<exists>x\<in>A. x)"

instance proof
qed (auto simp add: Inf_bool_def Sup_bool_def le_bool_def)

end

lemma Inf_empty_bool [simp]:
  "\<Sqinter>{}"
  unfolding Inf_bool_def by auto

lemma not_Sup_empty_bool [simp]:
  "\<not> \<Squnion>{}"
  unfolding Sup_bool_def by auto

lemma INFI_bool_eq:
  "INFI = Ball"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(INF x:A. P x) \<longleftrightarrow> (\<forall>x \<in> A. P x)"
    by (auto simp add: Ball_def INFI_def Inf_bool_def)
qed

lemma SUPR_bool_eq:
  "SUPR = Bex"
proof (rule ext)+
  fix A :: "'a set"
  fix P :: "'a \<Rightarrow> bool"
  show "(SUP x:A. P x) \<longleftrightarrow> (\<exists>x \<in> A. P x)"
    by (auto simp add: Bex_def SUPR_def Sup_bool_def)
qed

instantiation "fun" :: (type, complete_lattice) complete_lattice
begin

definition
  Inf_fun_def [code del]: "\<Sqinter>A = (\<lambda>x. \<Sqinter>{y. \<exists>f\<in>A. y = f x})"

definition
  Sup_fun_def [code del]: "\<Squnion>A = (\<lambda>x. \<Squnion>{y. \<exists>f\<in>A. y = f x})"

instance proof
qed (auto simp add: Inf_fun_def Sup_fun_def le_fun_def
  intro: Inf_lower Sup_upper Inf_greatest Sup_least)

end

lemma Inf_empty_fun:
  "\<Sqinter>{} = (\<lambda>_. \<Sqinter>{})"
  by (simp add: Inf_fun_def)

lemma Sup_empty_fun:
  "\<Squnion>{} = (\<lambda>_. \<Squnion>{})"
  by (simp add: Sup_fun_def)


subsubsection {* Union *}

definition Union :: "'a set set \<Rightarrow> 'a set" where
  Sup_set_eq [symmetric]: "Union S = \<Squnion>S"

notation (xsymbols)
  Union  ("\<Union>_" [90] 90)

lemma Union_eq:
  "\<Union>A = {x. \<exists>B \<in> A. x \<in> B}"
proof (rule set_ext)
  fix x
  have "(\<exists>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<exists>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Union>A \<longleftrightarrow> x \<in> {x. \<exists>B\<in>A. x \<in> B}"
    by (simp add: Sup_set_eq [symmetric] Sup_fun_def Sup_bool_def) (simp add: mem_def)
qed

lemma Union_iff [simp, noatp]:
  "A \<in> \<Union>C \<longleftrightarrow> (\<exists>X\<in>C. A\<in>X)"
  by (unfold Union_eq) blast

lemma UnionI [intro]:
  "X \<in> C \<Longrightarrow> A \<in> X \<Longrightarrow> A \<in> \<Union>C"
  -- {* The order of the premises presupposes that @{term C} is rigid;
    @{term A} may be flexible. *}
  by auto

lemma UnionE [elim!]:
  "A \<in> \<Union>C \<Longrightarrow> (\<And>X. A\<in>X \<Longrightarrow> X\<in>C \<Longrightarrow> R) \<Longrightarrow> R"
  by auto

lemma Union_upper: "B \<in> A ==> B \<subseteq> Union A"
  by (iprover intro: subsetI UnionI)

lemma Union_least: "(!!X. X \<in> A ==> X \<subseteq> C) ==> Union A \<subseteq> C"
  by (iprover intro: subsetI elim: UnionE dest: subsetD)

lemma Un_eq_Union: "A \<union> B = \<Union>{A, B}"
  by blast

lemma Union_empty [simp]: "Union({}) = {}"
  by blast

lemma Union_UNIV [simp]: "Union UNIV = UNIV"
  by blast

lemma Union_insert [simp]: "Union (insert a B) = a \<union> \<Union>B"
  by blast

lemma Union_Un_distrib [simp]: "\<Union>(A Un B) = \<Union>A \<union> \<Union>B"
  by blast

lemma Union_Int_subset: "\<Union>(A \<inter> B) \<subseteq> \<Union>A \<inter> \<Union>B"
  by blast

lemma Union_empty_conv [simp,noatp]: "(\<Union>A = {}) = (\<forall>x\<in>A. x = {})"
  by blast

lemma empty_Union_conv [simp,noatp]: "({} = \<Union>A) = (\<forall>x\<in>A. x = {})"
  by blast

lemma Union_disjoint: "(\<Union>C \<inter> A = {}) = (\<forall>B\<in>C. B \<inter> A = {})"
  by blast

lemma subset_Pow_Union: "A \<subseteq> Pow (\<Union>A)"
  by blast

lemma Union_Pow_eq [simp]: "\<Union>(Pow A) = A"
  by blast

lemma Union_mono: "A \<subseteq> B ==> \<Union>A \<subseteq> \<Union>B"
  by blast


subsubsection {* Unions of families *}

definition UNION :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  SUPR_set_eq [symmetric]: "UNION S f = (SUP x:S. f x)"

syntax
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3UN _./ _)" [0, 10] 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3UN _:_./ _)" [0, 10] 10)

syntax (xsymbols)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" [0, 10] 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" [0, 10] 10)

syntax (latex output)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 10] 10)

translations
  "UN x y. B"   == "UN x. UN y. B"
  "UN x. B"     == "CONST UNION CONST UNIV (%x. B)"
  "UN x. B"     == "UN x:CONST UNIV. B"
  "UN x:A. B"   == "CONST UNION A (%x. B)"

text {*
  Note the difference between ordinary xsymbol syntax of indexed
  unions and intersections (e.g.\ @{text"\<Union>a\<^isub>1\<in>A\<^isub>1. B"})
  and their \LaTeX\ rendition: @{term"\<Union>a\<^isub>1\<in>A\<^isub>1. B"}. The
  former does not make the index expression a subscript of the
  union/intersection symbol because this leads to problems with nested
  subscripts in Proof General.
*}

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax UNION} "@UNION"
] *} -- {* to avoid eta-contraction of body *}

lemma UNION_eq_Union_image:
  "(\<Union>x\<in>A. B x) = \<Union>(B`A)"
  by (simp add: SUPR_def SUPR_set_eq [symmetric] Sup_set_eq)

lemma Union_def:
  "\<Union>S = (\<Union>x\<in>S. x)"
  by (simp add: UNION_eq_Union_image image_def)

lemma UNION_def [noatp]:
  "(\<Union>x\<in>A. B x) = {y. \<exists>x\<in>A. y \<in> B x}"
  by (auto simp add: UNION_eq_Union_image Union_eq)
  
lemma Union_image_eq [simp]:
  "\<Union>(B`A) = (\<Union>x\<in>A. B x)"
  by (rule sym) (fact UNION_eq_Union_image)
  
lemma UN_iff [simp]: "(b: (UN x:A. B x)) = (EX x:A. b: B x)"
  by (unfold UNION_def) blast

lemma UN_I [intro]: "a:A ==> b: B a ==> b: (UN x:A. B x)"
  -- {* The order of the premises presupposes that @{term A} is rigid;
    @{term b} may be flexible. *}
  by auto

lemma UN_E [elim!]: "b : (UN x:A. B x) ==> (!!x. x:A ==> b: B x ==> R) ==> R"
  by (unfold UNION_def) blast

lemma UN_cong [cong]:
    "A = B ==> (!!x. x:B ==> C x = D x) ==> (UN x:A. C x) = (UN x:B. D x)"
  by (simp add: UNION_def)

lemma strong_UN_cong:
    "A = B ==> (!!x. x:B =simp=> C x = D x) ==> (UN x:A. C x) = (UN x:B. D x)"
  by (simp add: UNION_def simp_implies_def)

lemma image_eq_UN: "f`A = (UN x:A. {f x})"
  by blast

lemma UN_upper: "a \<in> A ==> B a \<subseteq> (\<Union>x\<in>A. B x)"
  by blast

lemma UN_least: "(!!x. x \<in> A ==> B x \<subseteq> C) ==> (\<Union>x\<in>A. B x) \<subseteq> C"
  by (iprover intro: subsetI elim: UN_E dest: subsetD)

lemma Collect_bex_eq [noatp]: "{x. \<exists>y\<in>A. P x y} = (\<Union>y\<in>A. {x. P x y})"
  by blast

lemma UN_insert_distrib: "u \<in> A ==> (\<Union>x\<in>A. insert a (B x)) = insert a (\<Union>x\<in>A. B x)"
  by blast

lemma UN_empty [simp,noatp]: "(\<Union>x\<in>{}. B x) = {}"
  by blast

lemma UN_empty2 [simp]: "(\<Union>x\<in>A. {}) = {}"
  by blast

lemma UN_singleton [simp]: "(\<Union>x\<in>A. {x}) = A"
  by blast

lemma UN_absorb: "k \<in> I ==> A k \<union> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. A i)"
  by auto

lemma UN_insert [simp]: "(\<Union>x\<in>insert a A. B x) = B a \<union> UNION A B"
  by blast

lemma UN_Un[simp]: "(\<Union>i \<in> A \<union> B. M i) = (\<Union>i\<in>A. M i) \<union> (\<Union>i\<in>B. M i)"
  by blast

lemma UN_UN_flatten: "(\<Union>x \<in> (\<Union>y\<in>A. B y). C x) = (\<Union>y\<in>A. \<Union>x\<in>B y. C x)"
  by blast

lemma UN_subset_iff: "((\<Union>i\<in>I. A i) \<subseteq> B) = (\<forall>i\<in>I. A i \<subseteq> B)"
  by blast

lemma image_Union: "f ` \<Union>S = (\<Union>x\<in>S. f ` x)"
  by blast

lemma UN_constant [simp]: "(\<Union>y\<in>A. c) = (if A = {} then {} else c)"
  by auto

lemma UN_eq: "(\<Union>x\<in>A. B x) = \<Union>({Y. \<exists>x\<in>A. Y = B x})"
  by blast

lemma UNION_empty_conv[simp]:
  "({} = (UN x:A. B x)) = (\<forall>x\<in>A. B x = {})"
  "((UN x:A. B x) = {}) = (\<forall>x\<in>A. B x = {})"
by blast+

lemma Collect_ex_eq [noatp]: "{x. \<exists>y. P x y} = (\<Union>y. {x. P x y})"
  by blast

lemma ball_UN: "(\<forall>z \<in> UNION A B. P z) = (\<forall>x\<in>A. \<forall>z \<in> B x. P z)"
  by blast

lemma bex_UN: "(\<exists>z \<in> UNION A B. P z) = (\<exists>x\<in>A. \<exists>z\<in>B x. P z)"
  by blast

lemma Un_eq_UN: "A \<union> B = (\<Union>b. if b then A else B)"
  by (auto simp add: split_if_mem2)

lemma UN_bool_eq: "(\<Union>b::bool. A b) = (A True \<union> A False)"
  by (auto intro: bool_contrapos)

lemma UN_Pow_subset: "(\<Union>x\<in>A. Pow (B x)) \<subseteq> Pow (\<Union>x\<in>A. B x)"
  by blast

lemma UN_mono:
  "A \<subseteq> B ==> (!!x. x \<in> A ==> f x \<subseteq> g x) ==>
    (\<Union>x\<in>A. f x) \<subseteq> (\<Union>x\<in>B. g x)"
  by (blast dest: subsetD)

lemma vimage_Union: "f -` (Union A) = (UN X:A. f -` X)"
  by blast

lemma vimage_UN: "f-`(UN x:A. B x) = (UN x:A. f -` B x)"
  by blast

lemma vimage_eq_UN: "f-`B = (UN y: B. f-`{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma image_UN: "(f ` (UNION A B)) = (UN x:A.(f ` (B x)))"
by blast


subsubsection {* Inter *}

definition Inter :: "'a set set \<Rightarrow> 'a set" where
  Inf_set_eq [symmetric]: "Inter S = \<Sqinter>S"
  
notation (xsymbols)
  Inter  ("\<Inter>_" [90] 90)

lemma Inter_eq [code del]:
  "\<Inter>A = {x. \<forall>B \<in> A. x \<in> B}"
proof (rule set_ext)
  fix x
  have "(\<forall>Q\<in>{P. \<exists>B\<in>A. P \<longleftrightarrow> x \<in> B}. Q) \<longleftrightarrow> (\<forall>B\<in>A. x \<in> B)"
    by auto
  then show "x \<in> \<Inter>A \<longleftrightarrow> x \<in> {x. \<forall>B \<in> A. x \<in> B}"
    by (simp add: Inf_fun_def Inf_bool_def Inf_set_eq [symmetric]) (simp add: mem_def)
qed

lemma Inter_iff [simp,noatp]: "(A : Inter C) = (ALL X:C. A:X)"
  by (unfold Inter_eq) blast

lemma InterI [intro!]: "(!!X. X:C ==> A:X) ==> A : Inter C"
  by (simp add: Inter_eq)

text {*
  \medskip A ``destruct'' rule -- every @{term X} in @{term C}
  contains @{term A} as an element, but @{prop "A:X"} can hold when
  @{prop "X:C"} does not!  This rule is analogous to @{text spec}.
*}

lemma InterD [elim]: "A : Inter C ==> X:C ==> A:X"
  by auto

lemma InterE [elim]: "A : Inter C ==> (X~:C ==> R) ==> (A:X ==> R) ==> R"
  -- {* ``Classical'' elimination rule -- does not require proving
    @{prop "X:C"}. *}
  by (unfold Inter_eq) blast

lemma Inter_lower: "B \<in> A ==> Inter A \<subseteq> B"
  by blast

lemma Inter_subset:
  "[| !!X. X \<in> A ==> X \<subseteq> B; A ~= {} |] ==> \<Inter>A \<subseteq> B"
  by blast

lemma Inter_greatest: "(!!X. X \<in> A ==> C \<subseteq> X) ==> C \<subseteq> Inter A"
  by (iprover intro: InterI subsetI dest: subsetD)

lemma Int_eq_Inter: "A \<inter> B = \<Inter>{A, B}"
  by blast

lemma Inter_empty [simp]: "\<Inter>{} = UNIV"
  by blast

lemma Inter_UNIV [simp]: "\<Inter>UNIV = {}"
  by blast

lemma Inter_insert [simp]: "\<Inter>(insert a B) = a \<inter> \<Inter>B"
  by blast

lemma Inter_Un_subset: "\<Inter>A \<union> \<Inter>B \<subseteq> \<Inter>(A \<inter> B)"
  by blast

lemma Inter_Un_distrib: "\<Inter>(A \<union> B) = \<Inter>A \<inter> \<Inter>B"
  by blast

lemma Inter_UNIV_conv [simp,noatp]:
  "(\<Inter>A = UNIV) = (\<forall>x\<in>A. x = UNIV)"
  "(UNIV = \<Inter>A) = (\<forall>x\<in>A. x = UNIV)"
  by blast+

lemma Inter_anti_mono: "B \<subseteq> A ==> \<Inter>A \<subseteq> \<Inter>B"
  by blast


subsubsection {* Intersections of families *}

definition INTER :: "'a set \<Rightarrow> ('a \<Rightarrow> 'b set) \<Rightarrow> 'b set" where
  INFI_set_eq [symmetric]: "INTER S f = (INF x:S. f x)"

syntax
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3INT _./ _)" [0, 10] 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3INT _:_./ _)" [0, 10] 10)

syntax (xsymbols)
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>_./ _)" [0, 10] 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>_\<in>_./ _)" [0, 10] 10)

syntax (latex output)
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>(00\<^bsub>_\<^esub>)/ _)" [0, 10] 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>(00\<^bsub>_\<in>_\<^esub>)/ _)" [0, 10] 10)

translations
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "CONST INTER CONST UNIV (%x. B)"
  "INT x. B"    == "INT x:CONST UNIV. B"
  "INT x:A. B"  == "CONST INTER A (%x. B)"

print_translation {* [
Syntax.preserve_binder_abs2_tr' @{const_syntax INTER} "@INTER"
] *} -- {* to avoid eta-contraction of body *}

lemma INTER_eq_Inter_image:
  "(\<Inter>x\<in>A. B x) = \<Inter>(B`A)"
  by (simp add: INFI_def INFI_set_eq [symmetric] Inf_set_eq)
  
lemma Inter_def:
  "\<Inter>S = (\<Inter>x\<in>S. x)"
  by (simp add: INTER_eq_Inter_image image_def)

lemma INTER_def:
  "(\<Inter>x\<in>A. B x) = {y. \<forall>x\<in>A. y \<in> B x}"
  by (auto simp add: INTER_eq_Inter_image Inter_eq)

lemma Inter_image_eq [simp]:
  "\<Inter>(B`A) = (\<Inter>x\<in>A. B x)"
  by (rule sym) (fact INTER_eq_Inter_image)

lemma INT_iff [simp]: "(b: (INT x:A. B x)) = (ALL x:A. b: B x)"
  by (unfold INTER_def) blast

lemma INT_I [intro!]: "(!!x. x:A ==> b: B x) ==> b : (INT x:A. B x)"
  by (unfold INTER_def) blast

lemma INT_D [elim]: "b : (INT x:A. B x) ==> a:A ==> b: B a"
  by auto

lemma INT_E [elim]: "b : (INT x:A. B x) ==> (b: B a ==> R) ==> (a~:A ==> R) ==> R"
  -- {* "Classical" elimination -- by the Excluded Middle on @{prop "a:A"}. *}
  by (unfold INTER_def) blast

lemma INT_cong [cong]:
    "A = B ==> (!!x. x:B ==> C x = D x) ==> (INT x:A. C x) = (INT x:B. D x)"
  by (simp add: INTER_def)

lemma Collect_ball_eq: "{x. \<forall>y\<in>A. P x y} = (\<Inter>y\<in>A. {x. P x y})"
  by blast

lemma Collect_all_eq: "{x. \<forall>y. P x y} = (\<Inter>y. {x. P x y})"
  by blast

lemma INT_lower: "a \<in> A ==> (\<Inter>x\<in>A. B x) \<subseteq> B a"
  by blast

lemma INT_greatest: "(!!x. x \<in> A ==> C \<subseteq> B x) ==> C \<subseteq> (\<Inter>x\<in>A. B x)"
  by (iprover intro: INT_I subsetI dest: subsetD)

lemma INT_empty [simp]: "(\<Inter>x\<in>{}. B x) = UNIV"
  by blast

lemma INT_absorb: "k \<in> I ==> A k \<inter> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. A i)"
  by blast

lemma INT_subset_iff: "(B \<subseteq> (\<Inter>i\<in>I. A i)) = (\<forall>i\<in>I. B \<subseteq> A i)"
  by blast

lemma INT_insert [simp]: "(\<Inter>x \<in> insert a A. B x) = B a \<inter> INTER A B"
  by blast

lemma INT_Un: "(\<Inter>i \<in> A \<union> B. M i) = (\<Inter>i \<in> A. M i) \<inter> (\<Inter>i\<in>B. M i)"
  by blast

lemma INT_insert_distrib:
    "u \<in> A ==> (\<Inter>x\<in>A. insert a (B x)) = insert a (\<Inter>x\<in>A. B x)"
  by blast

lemma INT_constant [simp]: "(\<Inter>y\<in>A. c) = (if A = {} then UNIV else c)"
  by auto

lemma INT_eq: "(\<Inter>x\<in>A. B x) = \<Inter>({Y. \<exists>x\<in>A. Y = B x})"
  -- {* Look: it has an \emph{existential} quantifier *}
  by blast

lemma INTER_UNIV_conv[simp]:
 "(UNIV = (INT x:A. B x)) = (\<forall>x\<in>A. B x = UNIV)"
 "((INT x:A. B x) = UNIV) = (\<forall>x\<in>A. B x = UNIV)"
by blast+

lemma INT_bool_eq: "(\<Inter>b::bool. A b) = (A True \<inter> A False)"
  by (auto intro: bool_induct)

lemma Pow_INT_eq: "Pow (\<Inter>x\<in>A. B x) = (\<Inter>x\<in>A. Pow (B x))"
  by blast

lemma INT_anti_mono:
  "B \<subseteq> A ==> (!!x. x \<in> A ==> f x \<subseteq> g x) ==>
    (\<Inter>x\<in>A. f x) \<subseteq> (\<Inter>x\<in>A. g x)"
  -- {* The last inclusion is POSITIVE! *}
  by (blast dest: subsetD)

lemma vimage_INT: "f-`(INT x:A. B x) = (INT x:A. f -` B x)"
  by blast


subsubsection {* Distributive laws *}

lemma Int_Union: "A \<inter> \<Union>B = (\<Union>C\<in>B. A \<inter> C)"
  by blast

lemma Int_Union2: "\<Union>B \<inter> A = (\<Union>C\<in>B. C \<inter> A)"
  by blast

lemma Un_Union_image: "(\<Union>x\<in>C. A x \<union> B x) = \<Union>(A`C) \<union> \<Union>(B`C)"
  -- {* Devlin, Fundamentals of Contemporary Set Theory, page 12, exercise 5: *}
  -- {* Union of a family of unions *}
  by blast

lemma UN_Un_distrib: "(\<Union>i\<in>I. A i \<union> B i) = (\<Union>i\<in>I. A i) \<union> (\<Union>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Un_Inter: "A \<union> \<Inter>B = (\<Inter>C\<in>B. A \<union> C)"
  by blast

lemma Int_Inter_image: "(\<Inter>x\<in>C. A x \<inter> B x) = \<Inter>(A`C) \<inter> \<Inter>(B`C)"
  by blast

lemma INT_Int_distrib: "(\<Inter>i\<in>I. A i \<inter> B i) = (\<Inter>i\<in>I. A i) \<inter> (\<Inter>i\<in>I. B i)"
  -- {* Equivalent version *}
  by blast

lemma Int_UN_distrib: "B \<inter> (\<Union>i\<in>I. A i) = (\<Union>i\<in>I. B \<inter> A i)"
  -- {* Halmos, Naive Set Theory, page 35. *}
  by blast

lemma Un_INT_distrib: "B \<union> (\<Inter>i\<in>I. A i) = (\<Inter>i\<in>I. B \<union> A i)"
  by blast

lemma Int_UN_distrib2: "(\<Union>i\<in>I. A i) \<inter> (\<Union>j\<in>J. B j) = (\<Union>i\<in>I. \<Union>j\<in>J. A i \<inter> B j)"
  by blast

lemma Un_INT_distrib2: "(\<Inter>i\<in>I. A i) \<union> (\<Inter>j\<in>J. B j) = (\<Inter>i\<in>I. \<Inter>j\<in>J. A i \<union> B j)"
  by blast


subsubsection {* Complement *}

lemma Compl_UN [simp]: "-(\<Union>x\<in>A. B x) = (\<Inter>x\<in>A. -B x)"
  by blast

lemma Compl_INT [simp]: "-(\<Inter>x\<in>A. B x) = (\<Union>x\<in>A. -B x)"
  by blast


subsubsection {* Miniscoping and maxiscoping *}

text {* \medskip Miniscoping: pushing in quantifiers and big Unions
           and Intersections. *}

lemma UN_simps [simp]:
  "!!a B C. (UN x:C. insert a (B x)) = (if C={} then {} else insert a (UN x:C. B x))"
  "!!A B C. (UN x:C. A x Un B)   = ((if C={} then {} else (UN x:C. A x) Un B))"
  "!!A B C. (UN x:C. A Un B x)   = ((if C={} then {} else A Un (UN x:C. B x)))"
  "!!A B C. (UN x:C. A x Int B)  = ((UN x:C. A x) Int B)"
  "!!A B C. (UN x:C. A Int B x)  = (A Int (UN x:C. B x))"
  "!!A B C. (UN x:C. A x - B)    = ((UN x:C. A x) - B)"
  "!!A B C. (UN x:C. A - B x)    = (A - (INT x:C. B x))"
  "!!A B. (UN x: Union A. B x) = (UN y:A. UN x:y. B x)"
  "!!A B C. (UN z: UNION A B. C z) = (UN  x:A. UN z: B(x). C z)"
  "!!A B f. (UN x:f`A. B x)     = (UN a:A. B (f a))"
  by auto

lemma INT_simps [simp]:
  "!!A B C. (INT x:C. A x Int B) = (if C={} then UNIV else (INT x:C. A x) Int B)"
  "!!A B C. (INT x:C. A Int B x) = (if C={} then UNIV else A Int (INT x:C. B x))"
  "!!A B C. (INT x:C. A x - B)   = (if C={} then UNIV else (INT x:C. A x) - B)"
  "!!A B C. (INT x:C. A - B x)   = (if C={} then UNIV else A - (UN x:C. B x))"
  "!!a B C. (INT x:C. insert a (B x)) = insert a (INT x:C. B x)"
  "!!A B C. (INT x:C. A x Un B)  = ((INT x:C. A x) Un B)"
  "!!A B C. (INT x:C. A Un B x)  = (A Un (INT x:C. B x))"
  "!!A B. (INT x: Union A. B x) = (INT y:A. INT x:y. B x)"
  "!!A B C. (INT z: UNION A B. C z) = (INT x:A. INT z: B(x). C z)"
  "!!A B f. (INT x:f`A. B x)    = (INT a:A. B (f a))"
  by auto

lemma ball_simps [simp,noatp]:
  "!!A P Q. (ALL x:A. P x | Q) = ((ALL x:A. P x) | Q)"
  "!!A P Q. (ALL x:A. P | Q x) = (P | (ALL x:A. Q x))"
  "!!A P Q. (ALL x:A. P --> Q x) = (P --> (ALL x:A. Q x))"
  "!!A P Q. (ALL x:A. P x --> Q) = ((EX x:A. P x) --> Q)"
  "!!P. (ALL x:{}. P x) = True"
  "!!P. (ALL x:UNIV. P x) = (ALL x. P x)"
  "!!a B P. (ALL x:insert a B. P x) = (P a & (ALL x:B. P x))"
  "!!A P. (ALL x:Union A. P x) = (ALL y:A. ALL x:y. P x)"
  "!!A B P. (ALL x: UNION A B. P x) = (ALL a:A. ALL x: B a. P x)"
  "!!P Q. (ALL x:Collect Q. P x) = (ALL x. Q x --> P x)"
  "!!A P f. (ALL x:f`A. P x) = (ALL x:A. P (f x))"
  "!!A P. (~(ALL x:A. P x)) = (EX x:A. ~P x)"
  by auto

lemma bex_simps [simp,noatp]:
  "!!A P Q. (EX x:A. P x & Q) = ((EX x:A. P x) & Q)"
  "!!A P Q. (EX x:A. P & Q x) = (P & (EX x:A. Q x))"
  "!!P. (EX x:{}. P x) = False"
  "!!P. (EX x:UNIV. P x) = (EX x. P x)"
  "!!a B P. (EX x:insert a B. P x) = (P(a) | (EX x:B. P x))"
  "!!A P. (EX x:Union A. P x) = (EX y:A. EX x:y. P x)"
  "!!A B P. (EX x: UNION A B. P x) = (EX a:A. EX x:B a. P x)"
  "!!P Q. (EX x:Collect Q. P x) = (EX x. Q x & P x)"
  "!!A P f. (EX x:f`A. P x) = (EX x:A. P (f x))"
  "!!A P. (~(EX x:A. P x)) = (ALL x:A. ~P x)"
  by auto

lemma ball_conj_distrib:
  "(ALL x:A. P x & Q x) = ((ALL x:A. P x) & (ALL x:A. Q x))"
  by blast

lemma bex_disj_distrib:
  "(EX x:A. P x | Q x) = ((EX x:A. P x) | (EX x:A. Q x))"
  by blast


text {* \medskip Maxiscoping: pulling out big Unions and Intersections. *}

lemma UN_extend_simps:
  "!!a B C. insert a (UN x:C. B x) = (if C={} then {a} else (UN x:C. insert a (B x)))"
  "!!A B C. (UN x:C. A x) Un B    = (if C={} then B else (UN x:C. A x Un B))"
  "!!A B C. A Un (UN x:C. B x)   = (if C={} then A else (UN x:C. A Un B x))"
  "!!A B C. ((UN x:C. A x) Int B) = (UN x:C. A x Int B)"
  "!!A B C. (A Int (UN x:C. B x)) = (UN x:C. A Int B x)"
  "!!A B C. ((UN x:C. A x) - B) = (UN x:C. A x - B)"
  "!!A B C. (A - (INT x:C. B x)) = (UN x:C. A - B x)"
  "!!A B. (UN y:A. UN x:y. B x) = (UN x: Union A. B x)"
  "!!A B C. (UN  x:A. UN z: B(x). C z) = (UN z: UNION A B. C z)"
  "!!A B f. (UN a:A. B (f a)) = (UN x:f`A. B x)"
  by auto

lemma INT_extend_simps:
  "!!A B C. (INT x:C. A x) Int B = (if C={} then B else (INT x:C. A x Int B))"
  "!!A B C. A Int (INT x:C. B x) = (if C={} then A else (INT x:C. A Int B x))"
  "!!A B C. (INT x:C. A x) - B   = (if C={} then UNIV-B else (INT x:C. A x - B))"
  "!!A B C. A - (UN x:C. B x)   = (if C={} then A else (INT x:C. A - B x))"
  "!!a B C. insert a (INT x:C. B x) = (INT x:C. insert a (B x))"
  "!!A B C. ((INT x:C. A x) Un B)  = (INT x:C. A x Un B)"
  "!!A B C. A Un (INT x:C. B x)  = (INT x:C. A Un B x)"
  "!!A B. (INT y:A. INT x:y. B x) = (INT x: Union A. B x)"
  "!!A B C. (INT x:A. INT z: B(x). C z) = (INT z: UNION A B. C z)"
  "!!A B f. (INT a:A. B (f a))    = (INT x:f`A. B x)"
  by auto


no_notation
  less_eq  (infix "\<sqsubseteq>" 50) and
  less (infix "\<sqsubset>" 50) and
  inf  (infixl "\<sqinter>" 70) and
  sup  (infixl "\<squnion>" 65) and
  Inf  ("\<Sqinter>_" [900] 900) and
  Sup  ("\<Squnion>_" [900] 900)

lemmas mem_simps =
  insert_iff empty_iff Un_iff Int_iff Compl_iff Diff_iff
  mem_Collect_eq UN_iff Union_iff INT_iff Inter_iff
  -- {* Each of these has ALREADY been added @{text "[simp]"} above. *}

end
