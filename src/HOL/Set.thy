(*  Title:      HOL/Set.thy
    ID:         $Id$
    Author:     Tobias Nipkow, Lawrence C Paulson and Markus Wenzel
    License:    GPL (GNU GENERAL PUBLIC LICENSE)
*)

header {* Set theory for higher-order logic *}

theory Set = HOL
files ("subset.ML") ("equalities.ML") ("mono.ML"):

text {* A set in HOL is simply a predicate. *}


subsection {* Basic syntax *}

global

typedecl 'a set
arities set :: (type) type

consts
  "{}"          :: "'a set"                             ("{}")
  UNIV          :: "'a set"
  insert        :: "'a => 'a set => 'a set"
  Collect       :: "('a => bool) => 'a set"              -- "comprehension"
  Int           :: "'a set => 'a set => 'a set"          (infixl 70)
  Un            :: "'a set => 'a set => 'a set"          (infixl 65)
  UNION         :: "'a set => ('a => 'b set) => 'b set"  -- "general union"
  INTER         :: "'a set => ('a => 'b set) => 'b set"  -- "general intersection"
  Union         :: "'a set set => 'a set"                -- "union of a set"
  Inter         :: "'a set set => 'a set"                -- "intersection of a set"
  Pow           :: "'a set => 'a set set"                -- "powerset"
  Ball          :: "'a set => ('a => bool) => bool"      -- "bounded universal quantifiers"
  Bex           :: "'a set => ('a => bool) => bool"      -- "bounded existential quantifiers"
  image         :: "('a => 'b) => 'a set => 'b set"      (infixr "`" 90)

syntax
  "op :"        :: "'a => 'a set => bool"                ("op :")
consts
  "op :"        :: "'a => 'a set => bool"                ("(_/ : _)" [50, 51] 50)  -- "membership"

local

instance set :: (type) ord ..
instance set :: (type) minus ..


subsection {* Additional concrete syntax *}

syntax
  range         :: "('a => 'b) => 'b set"             -- "of function"

  "op ~:"       :: "'a => 'a set => bool"                 ("op ~:")  -- "non-membership"
  "op ~:"       :: "'a => 'a set => bool"                 ("(_/ ~: _)" [50, 51] 50)

  "@Finset"     :: "args => 'a set"                       ("{(_)}")
  "@Coll"       :: "pttrn => bool => 'a set"              ("(1{_./ _})")
  "@SetCompr"   :: "'a => idts => bool => 'a set"         ("(1{_ |/_./ _})")

  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3INT _./ _)" 10)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3UN _./ _)" 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3INT _:_./ _)" 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3UN _:_./ _)" 10)

  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3ALL _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3EX _:_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3! _:_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3? _:_./ _)" [0, 0, 10] 10)

translations
  "range f"     == "f`UNIV"
  "x ~: y"      == "~ (x : y)"
  "{x, xs}"     == "insert x {xs}"
  "{x}"         == "insert x {}"
  "{x. P}"      == "Collect (%x. P)"
  "UN x y. B"   == "UN x. UN y. B"
  "UN x. B"     == "UNION UNIV (%x. B)"
  "INT x y. B"  == "INT x. INT y. B"
  "INT x. B"    == "INTER UNIV (%x. B)"
  "UN x:A. B"   == "UNION A (%x. B)"
  "INT x:A. B"  == "INTER A (%x. B)"
  "ALL x:A. P"  == "Ball A (%x. P)"
  "EX x:A. P"   == "Bex A (%x. P)"

syntax ("" output)
  "_setle"      :: "'a set => 'a set => bool"             ("op <=")
  "_setle"      :: "'a set => 'a set => bool"             ("(_/ <= _)" [50, 51] 50)
  "_setless"    :: "'a set => 'a set => bool"             ("op <")
  "_setless"    :: "'a set => 'a set => bool"             ("(_/ < _)" [50, 51] 50)

syntax (xsymbols)
  "_setle"      :: "'a set => 'a set => bool"             ("op \<subseteq>")
  "_setle"      :: "'a set => 'a set => bool"             ("(_/ \<subseteq> _)" [50, 51] 50)
  "_setless"    :: "'a set => 'a set => bool"             ("op \<subset>")
  "_setless"    :: "'a set => 'a set => bool"             ("(_/ \<subset> _)" [50, 51] 50)
  "op Int"      :: "'a set => 'a set => 'a set"           (infixl "\<inter>" 70)
  "op Un"       :: "'a set => 'a set => 'a set"           (infixl "\<union>" 65)
  "op :"        :: "'a => 'a set => bool"                 ("op \<in>")
  "op :"        :: "'a => 'a set => bool"                 ("(_/ \<in> _)" [50, 51] 50)
  "op ~:"       :: "'a => 'a set => bool"                 ("op \<notin>")
  "op ~:"       :: "'a => 'a set => bool"                 ("(_/ \<notin> _)" [50, 51] 50)
  "@UNION1"     :: "pttrns => 'b set => 'b set"           ("(3\<Union>_./ _)" 10)
  "@INTER1"     :: "pttrns => 'b set => 'b set"           ("(3\<Inter>_./ _)" 10)
  "@UNION"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Union>_\<in>_./ _)" 10)
  "@INTER"      :: "pttrn => 'a set => 'b set => 'b set"  ("(3\<Inter>_\<in>_./ _)" 10)
  Union         :: "'a set set => 'a set"                 ("\<Union>_" [90] 90)
  Inter         :: "'a set set => 'a set"                 ("\<Inter>_" [90] 90)
  "_Ball"       :: "pttrn => 'a set => bool => bool"      ("(3\<forall>_\<in>_./ _)" [0, 0, 10] 10)
  "_Bex"        :: "pttrn => 'a set => bool => bool"      ("(3\<exists>_\<in>_./ _)" [0, 0, 10] 10)

translations
  "op \<subseteq>" => "op <= :: _ set => _ set => bool"
  "op \<subset>" => "op <  :: _ set => _ set => bool"


typed_print_translation {*
  let
    fun le_tr' _ (Type ("fun", (Type ("set", _) :: _))) ts =
          list_comb (Syntax.const "_setle", ts)
      | le_tr' _ _ _ = raise Match;

    fun less_tr' _ (Type ("fun", (Type ("set", _) :: _))) ts =
          list_comb (Syntax.const "_setless", ts)
      | less_tr' _ _ _ = raise Match;
  in [("op <=", le_tr'), ("op <", less_tr')] end
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
      in Syntax.const "Collect" $ Abs ("", dummyT, exP) end;

  in [("@SetCompr", setcompr_tr)] end;
*}

print_translation {*
  let
    val ex_tr' = snd (mk_binder_tr' ("Ex", "DUMMY"));

    fun setcompr_tr' [Abs (_, _, P)] =
      let
        fun check (Const ("Ex", _) $ Abs (_, _, P), n) = check (P, n + 1)
          | check (Const ("op &", _) $ (Const ("op =", _) $ Bound m $ e) $ P, n) =
              if n > 0 andalso m = n andalso not (loose_bvar1 (P, n)) andalso
                ((0 upto (n - 1)) subset add_loose_bnos (e, 0, [])) then ()
              else raise Match;

        fun tr' (_ $ abs) =
          let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr' [abs]
          in Syntax.const "@SetCompr" $ e $ idts $ Q end;
      in check (P, 0); tr' P end;
  in [("Collect", setcompr_tr')] end;
*}


subsection {* Rules and definitions *}

text {* Isomorphisms between predicates and sets. *}

axioms
  mem_Collect_eq [iff]: "(a : {x. P(x)}) = P(a)"
  Collect_mem_eq [simp]: "{x. x:A} = A"

defs
  Ball_def:     "Ball A P       == ALL x. x:A --> P(x)"
  Bex_def:      "Bex A P        == EX x. x:A & P(x)"

defs (overloaded)
  subset_def:   "A <= B         == ALL x:A. x:B"
  psubset_def:  "A < B          == (A::'a set) <= B & ~ A=B"
  Compl_def:    "- A            == {x. ~x:A}"
  set_diff_def: "A - B          == {x. x:A & ~x:B}"

defs
  Un_def:       "A Un B         == {x. x:A | x:B}"
  Int_def:      "A Int B        == {x. x:A & x:B}"
  INTER_def:    "INTER A B      == {y. ALL x:A. y: B(x)}"
  UNION_def:    "UNION A B      == {y. EX x:A. y: B(x)}"
  Inter_def:    "Inter S        == (INT x:S. x)"
  Union_def:    "Union S        == (UN x:S. x)"
  Pow_def:      "Pow A          == {B. B <= A}"
  empty_def:    "{}             == {x. False}"
  UNIV_def:     "UNIV           == {x. True}"
  insert_def:   "insert a B     == {x. x=a} Un B"
  image_def:    "f`A            == {y. EX x:A. y = f(x)}"


subsection {* Lemmas and proof tool setup *}

subsubsection {* Relating predicates and sets *}

lemma CollectI: "P(a) ==> a : {x. P(x)}"
  by simp

lemma CollectD: "a : {x. P(x)} ==> P(a)"
  by simp

lemma set_ext: (assumes prem: "(!!x. (x:A) = (x:B))") "A = B"
  apply (rule prem [THEN ext, THEN arg_cong, THEN box_equals])
   apply (rule Collect_mem_eq)
  apply (rule Collect_mem_eq)
  done

lemma Collect_cong: "(!!x. P x = Q x) ==> {x. P(x)} = {x. Q(x)}"
  by simp

lemmas CollectE = CollectD [elim_format]


subsubsection {* Bounded quantifiers *}

lemma ballI [intro!]: "(!!x. x:A ==> P x) ==> ALL x:A. P x"
  by (simp add: Ball_def)

lemmas strip = impI allI ballI

lemma bspec [dest?]: "ALL x:A. P x ==> x:A ==> P x"
  by (simp add: Ball_def)

lemma ballE [elim]: "ALL x:A. P x ==> (P x ==> Q) ==> (x ~: A ==> Q) ==> Q"
  by (unfold Ball_def) blast

text {*
  \medskip This tactic takes assumptions @{prop "ALL x:A. P x"} and
  @{prop "a:A"}; creates assumption @{prop "P a"}.
*}

ML {*
  local val ballE = thm "ballE"
  in fun ball_tac i = etac ballE i THEN contr_tac (i + 1) end;
*}

text {*
  Gives better instantiation for bound:
*}

ML_setup {*
  claset_ref() := claset() addbefore ("bspec", datac (thm "bspec") 1);
*}

lemma bexI [intro]: "P x ==> x:A ==> EX x:A. P x"
  -- {* Normally the best argument order: @{prop "P x"} constrains the
    choice of @{prop "x:A"}. *}
  by (unfold Bex_def) blast

lemma rev_bexI: "x:A ==> P x ==> EX x:A. P x"
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

ML_setup {*
  let
    val Ball_def = thm "Ball_def";
    val Bex_def = thm "Bex_def";

    val ex_pattern = Thm.read_cterm (Theory.sign_of (the_context ()))
      ("EX x:A. P x & Q x", HOLogic.boolT);

    val prove_bex_tac =
      rewrite_goals_tac [Bex_def] THEN Quantifier1.prove_one_point_ex_tac;
    val rearrange_bex = Quantifier1.rearrange_bex prove_bex_tac;

    val all_pattern = Thm.read_cterm (Theory.sign_of (the_context ()))
      ("ALL x:A. P x --> Q x", HOLogic.boolT);

    val prove_ball_tac =
      rewrite_goals_tac [Ball_def] THEN Quantifier1.prove_one_point_all_tac;
    val rearrange_ball = Quantifier1.rearrange_ball prove_ball_tac;

    val defBEX_regroup = mk_simproc "defined BEX" [ex_pattern] rearrange_bex;
    val defBALL_regroup = mk_simproc "defined BALL" [all_pattern] rearrange_ball;
  in
    Addsimprocs [defBALL_regroup, defBEX_regroup]
  end;
*}


subsubsection {* Congruence rules *}

lemma ball_cong [cong]:
  "A = B ==> (!!x. x:B ==> P x = Q x) ==>
    (ALL x:A. P x) = (ALL x:B. Q x)"
  by (simp add: Ball_def)

lemma bex_cong [cong]:
  "A = B ==> (!!x. x:B ==> P x = Q x) ==>
    (EX x:A. P x) = (EX x:B. Q x)"
  by (simp add: Bex_def cong: conj_cong)


subsubsection {* Subsets *}

lemma subsetI [intro!]: "(!!x. x:A ==> x:B) ==> A <= B"
  by (simp add: subset_def)

text {*
  \medskip Map the type @{text "'a set => anything"} to just @{typ
  'a}; for overloading constants whose first argument has type @{typ
  "'a set"}.
*}

ML {*
  fun overload_1st_set s = Blast.overloaded (s, HOLogic.dest_setT o domain_type);
*}

ML "
  (* While (:) is not, its type must be kept
    for overloading of = to work. *)
  Blast.overloaded (\"op :\", domain_type);

  overload_1st_set \"Ball\";            (*need UNION, INTER also?*)
  overload_1st_set \"Bex\";

  (*Image: retain the type of the set being expressed*)
  Blast.overloaded (\"image\", domain_type);
"

lemma subsetD [elim]: "A <= B ==> c:A ==> c:B"
  -- {* Rule in Modus Ponens style. *}
  by (unfold subset_def) blast

declare subsetD [intro?] -- FIXME

lemma rev_subsetD: "c:A ==> A <= B ==> c:B"
  -- {* The same, with reversed premises for use with @{text erule} --
      cf @{text rev_mp}. *}
  by (rule subsetD)

declare rev_subsetD [intro?] -- FIXME

text {*
  \medskip Converts @{prop "A <= B"} to @{prop "x:A ==> x:B"}.
*}

ML {*
  local val rev_subsetD = thm "rev_subsetD"
  in fun impOfSubs th = th RSN (2, rev_subsetD) end;
*}

lemma subsetCE [elim]: "A <= B ==> (c~:A ==> P) ==> (c:B ==> P) ==> P"
  -- {* Classical elimination rule. *}
  by (unfold subset_def) blast

text {*
  \medskip Takes assumptions @{prop "A <= B"}; @{prop "c:A"} and
  creates the assumption @{prop "c:B"}.
*}

ML {*
  local val subsetCE = thm "subsetCE"
  in fun set_mp_tac i = etac subsetCE i THEN mp_tac i end;
*}

lemma contra_subsetD: "A <= B ==> c ~: B ==> c ~: A"
  by blast

lemma subset_refl: "A <= (A::'a set)"
  by fast

lemma subset_trans: "A <= B ==> B <= C ==> A <= (C::'a set)"
  by blast


subsubsection {* Equality *}

lemma subset_antisym [intro!]: "A <= B ==> B <= A ==> A = (B::'a set)"
  -- {* Anti-symmetry of the subset relation. *}
  by (rule set_ext) (blast intro: subsetD)

lemmas equalityI = subset_antisym

text {*
  \medskip Equality rules from ZF set theory -- are they appropriate
  here?
*}

lemma equalityD1: "A = B ==> A <= (B::'a set)"
  by (simp add: subset_refl)

lemma equalityD2: "A = B ==> B <= (A::'a set)"
  by (simp add: subset_refl)

text {*
  \medskip Be careful when adding this to the claset as @{text
  subset_empty} is in the simpset: @{prop "A = {}"} goes to @{prop "{}
  <= A"} and @{prop "A <= {}"} and then back to @{prop "A = {}"}!
*}

lemma equalityE: "A = B ==> (A <= B ==> B <= (A::'a set) ==> P) ==> P"
  by (simp add: subset_refl)

lemma equalityCE [elim]:
    "A = B ==> (c:A ==> c:B ==> P) ==> (c~:A ==> c~:B ==> P) ==> P"
  by blast

text {*
  \medskip Lemma for creating induction formulae -- for "pattern
  matching" on @{text p}.  To make the induction hypotheses usable,
  apply @{text spec} or @{text bspec} to put universal quantifiers over the free
  variables in @{text p}.
*}

lemma setup_induction: "p:A ==> (!!z. z:A ==> p = z --> R) ==> R"
  by simp

lemma eqset_imp_iff: "A = B ==> (x : A) = (x : B)"
  by simp


subsubsection {* The universal set -- UNIV *}

lemma UNIV_I [simp]: "x : UNIV"
  by (simp add: UNIV_def)

declare UNIV_I [intro]  -- {* unsafe makes it less likely to cause problems *}

lemma UNIV_witness [intro?]: "EX x. x : UNIV"
  by simp

lemma subset_UNIV: "A <= UNIV"
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


subsubsection {* The empty set *}

lemma empty_iff [simp]: "(c : {}) = False"
  by (simp add: empty_def)

lemma emptyE [elim!]: "a : {} ==> P"
  by simp

lemma empty_subsetI [iff]: "{} <= A"
    -- {* One effect is to delete the ASSUMPTION @{prop "{} <= A"} *}
  by blast

lemma equals0I: "(!!y. y:A ==> False) ==> A = {}"
  by blast

lemma equals0D: "A={} ==> a ~: A"
    -- {* Use for reasoning about disjointness: @{prop "A Int B = {}"} *}
  by blast

lemma ball_empty [simp]: "Ball {} P = True"
  by (simp add: Ball_def)

lemma bex_empty [simp]: "Bex {} P = False"
  by (simp add: Bex_def)

lemma UNIV_not_empty [iff]: "UNIV ~= {}"
  by (blast elim: equalityE)


subsubsection {* The Powerset operator -- Pow *}

lemma Pow_iff [iff]: "(A : Pow B) = (A <= B)"
  by (simp add: Pow_def)

lemma PowI: "A <= B ==> A : Pow B"
  by (simp add: Pow_def)

lemma PowD: "A : Pow B ==> A <= B"
  by (simp add: Pow_def)

lemma Pow_bottom: "{}: Pow B"
  by simp

lemma Pow_top: "A : Pow A"
  by (simp add: subset_refl)


subsubsection {* Set complement *}

lemma Compl_iff [simp]: "(c : -A) = (c~:A)"
  by (unfold Compl_def) blast

lemma ComplI [intro!]: "(c:A ==> False) ==> c : -A"
  by (unfold Compl_def) blast

text {*
  \medskip This form, with negated conclusion, works well with the
  Classical prover.  Negated assumptions behave like formulae on the
  right side of the notional turnstile ... *}

lemma ComplD: "c : -A ==> c~:A"
  by (unfold Compl_def) blast

lemmas ComplE [elim!] = ComplD [elim_format]


subsubsection {* Binary union -- Un *}

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


subsubsection {* Binary intersection -- Int *}

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


subsubsection {* Set difference *}

lemma Diff_iff [simp]: "(c : A - B) = (c:A & c~:B)"
  by (unfold set_diff_def) blast

lemma DiffI [intro!]: "c : A ==> c ~: B ==> c : A - B"
  by simp

lemma DiffD1: "c : A - B ==> c : A"
  by simp

lemma DiffD2: "c : A - B ==> c : B ==> P"
  by simp

lemma DiffE [elim!]: "c : A - B ==> (c:A ==> c~:B ==> P) ==> P"
  by simp


subsubsection {* Augmenting a set -- insert *}

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

lemma subset_insert_iff: "(A <= insert x B) = (if x:A then A - {x} <= B else A <= B)"
  by auto


subsubsection {* Singletons, using insert *}

lemma singletonI [intro!]: "a : {a}"
    -- {* Redundant? But unlike @{text insertCI}, it proves the subgoal immediately! *}
  by (rule insertI1)

lemma singletonD: "b : {a} ==> b = a"
  by blast

lemmas singletonE [elim!] = singletonD [elim_format]

lemma singleton_iff: "(b : {a}) = (b = a)"
  by blast

lemma singleton_inject [dest!]: "{a} = {b} ==> a = b"
  by blast

lemma singleton_insert_inj_eq [iff]: "({b} = insert a A) = (a = b & A <= {b})"
  by blast

lemma singleton_insert_inj_eq' [iff]: "(insert a A = {b}) = (a = b & A <= {b})"
  by blast

lemma subset_singletonD: "A <= {x} ==> A={} | A = {x}"
  by fast

lemma singleton_conv [simp]: "{x. x = a} = {a}"
  by blast

lemma singleton_conv2 [simp]: "{x. a = x} = {a}"
  by blast

lemma diff_single_insert: "A - {x} <= B ==> x : A ==> A <= insert x B"
  by blast


subsubsection {* Unions of families *}

text {*
  @{term [source] "UN x:A. B x"} is @{term "Union (B`A)"}.
*}

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


subsubsection {* Intersections of families *}

text {* @{term [source] "INT x:A. B x"} is @{term "Inter (B`A)"}. *}

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


subsubsection {* Union *}

lemma Union_iff [simp]: "(A : Union C) = (EX X:C. A:X)"
  by (unfold Union_def) blast

lemma UnionI [intro]: "X:C ==> A:X ==> A : Union C"
  -- {* The order of the premises presupposes that @{term C} is rigid;
    @{term A} may be flexible. *}
  by auto

lemma UnionE [elim!]: "A : Union C ==> (!!X. A:X ==> X:C ==> R) ==> R"
  by (unfold Union_def) blast


subsubsection {* Inter *}

lemma Inter_iff [simp]: "(A : Inter C) = (ALL X:C. A:X)"
  by (unfold Inter_def) blast

lemma InterI [intro!]: "(!!X. X:C ==> A:X) ==> A : Inter C"
  by (simp add: Inter_def)

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
  by (unfold Inter_def) blast

text {*
  \medskip Image of a set under a function.  Frequently @{term b} does
  not have the syntactic form of @{term "f x"}.
*}

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

lemma image_subset_iff: "(f`A <= B) = (ALL x:A. f x: B)"
  -- {* This rewrite rule would confuse users if made default. *}
  by blast

lemma subset_image_iff: "(B <= f ` A) = (EX AA. AA <= A & B = f ` AA)"
  apply safe
   prefer 2 apply fast
  apply (rule_tac x = "{a. a : A & f a : B}" in exI)
  apply fast
  done

lemma image_subsetI: "(!!x. x:A ==> f x : B) ==> f`A <= B"
  -- {* Replaces the three steps @{text subsetI}, @{text imageE},
    @{text hypsubst}, but breaks too many existing proofs. *}
  by blast

text {*
  \medskip Range of a function -- just a translation for image!
*}

lemma range_eqI: "b = f x ==> b : range f"
  by simp

lemma rangeI: "f x : range f"
  by simp

lemma rangeE [elim?]: "b : range (%x. f x) ==> (!!x. b = f x ==> P) ==> P"
  by blast


subsubsection {* Set reasoning tools *}

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
  by (rule split_if)

lemmas split_ifs = if_bool_eq_conj split_if_eq1 split_if_eq2 split_if_mem1 split_if_mem2

lemmas mem_simps =
  insert_iff empty_iff Un_iff Int_iff Compl_iff Diff_iff
  mem_Collect_eq UN_iff Union_iff INT_iff Inter_iff
  -- {* Each of these has ALREADY been added @{text "[simp]"} above. *}

(*Would like to add these, but the existing code only searches for the
  outer-level constant, which in this case is just "op :"; we instead need
  to use term-nets to associate patterns with rules.  Also, if a rule fails to
  apply, then the formula should be kept.
  [("uminus", Compl_iff RS iffD1), ("op -", [Diff_iff RS iffD1]),
   ("op Int", [IntD1,IntD2]),
   ("Collect", [CollectD]), ("Inter", [InterD]), ("INTER", [INT_D])]
 *)

ML_setup {*
  val mksimps_pairs = [("Ball", [thm "bspec"])] @ mksimps_pairs;
  simpset_ref() := simpset() setmksimps (mksimps mksimps_pairs);
*}

declare subset_UNIV [simp] subset_refl [simp]


subsubsection {* The ``proper subset'' relation *}

lemma psubsetI [intro!]: "(A::'a set) <= B ==> A ~= B ==> A < B"
  by (unfold psubset_def) blast

lemma psubset_insert_iff:
  "(A < insert x B) = (if x:B then A < B else if x:A then A - {x} < B else A <= B)"
  apply (simp add: psubset_def subset_insert_iff)
  apply blast
  done

lemma psubset_eq: "((A::'a set) < B) = (A <= B & A ~= B)"
  by (simp only: psubset_def)

lemma psubset_imp_subset: "(A::'a set) < B ==> A <= B"
  by (simp add: psubset_eq)

lemma psubset_subset_trans: "(A::'a set) < B ==> B <= C ==> A < C"
  by (auto simp add: psubset_eq)

lemma subset_psubset_trans: "(A::'a set) <= B ==> B < C ==> A < C"
  by (auto simp add: psubset_eq)

lemma psubset_imp_ex_mem: "A < B ==> EX b. b : (B - A)"
  by (unfold psubset_def) blast

lemma atomize_ball:
    "(!!x. x:A ==> P x) == Trueprop (ALL x:A. P x)"
  by (simp only: Ball_def atomize_all atomize_imp)

declare atomize_ball [symmetric, rulify]


subsection {* Further set-theory lemmas *}

use "subset.ML"
use "equalities.ML"
use "mono.ML"

lemma Least_mono:
  "mono (f::'a::order => 'b::order) ==> EX x:S. ALL y:S. x <= y
    ==> (LEAST y. y : f ` S) = f (LEAST x. x : S)"
    -- {* Courtesy of Stephan Merz *}
  apply clarify
  apply (erule_tac P = "%x. x : S" in LeastI2)
   apply fast
  apply (rule LeastI2)
  apply (auto elim: monoD intro!: order_antisym)
  done


subsection {* Inverse image of a function *}

constdefs
  vimage :: "('a => 'b) => 'b set => 'a set"    (infixr "-`" 90)
  "f -` B == {x. f x : B}"


subsubsection {* Basic rules *}

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


subsubsection {* Equations *}

lemma vimage_empty [simp]: "f -` {} = {}"
  by blast

lemma vimage_Compl: "f -` (-A) = -(f -` A)"
  by blast

lemma vimage_Un [simp]: "f -` (A Un B) = (f -` A) Un (f -` B)"
  by blast

lemma vimage_Int [simp]: "f -` (A Int B) = (f -` A) Int (f -` B)"
  by fast

lemma vimage_Union: "f -` (Union A) = (UN X:A. f -` X)"
  by blast

lemma vimage_UN: "f-`(UN x:A. B x) = (UN x:A. f -` B x)"
  by blast

lemma vimage_INT: "f-`(INT x:A. B x) = (INT x:A. f -` B x)"
  by blast

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

lemma vimage_eq_UN: "f-`B = (UN y: B. f-`{y})"
  -- {* NOT suitable for rewriting *}
  by blast

lemma vimage_mono: "A <= B ==> f -` A <= f -` B"
  -- {* monotonicity *}
  by blast


subsection {* Transitivity rules for calculational reasoning *}

lemma forw_subst: "a = b ==> P b ==> P a"
  by (rule ssubst)

lemma back_subst: "P a ==> a = b ==> P b"
  by (rule subst)

lemma set_rev_mp: "x:A ==> A <= B ==> x:B"
  by (rule subsetD)

lemma set_mp: "A <= B ==> x:A ==> x:B"
  by (rule subsetD)

lemma order_neq_le_trans: "a ~= b ==> (a::'a::order) <= b ==> a < b"
  by (simp add: order_less_le)

lemma order_le_neq_trans: "(a::'a::order) <= b ==> a ~= b ==> a < b"
  by (simp add: order_less_le)

lemma order_less_asym': "(a::'a::order) < b ==> b < a ==> P"
  by (rule order_less_asym)

lemma ord_le_eq_trans: "a <= b ==> b = c ==> a <= c"
  by (rule subst)

lemma ord_eq_le_trans: "a = b ==> b <= c ==> a <= c"
  by (rule ssubst)

lemma ord_less_eq_trans: "a < b ==> b = c ==> a < c"
  by (rule subst)

lemma ord_eq_less_trans: "a = b ==> b < c ==> a < c"
  by (rule ssubst)

lemma order_less_subst2: "(a::'a::order) < b ==> f b < (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b < c"
  finally (order_less_trans) show ?thesis .
qed

lemma order_less_subst1: "(a::'a::order) < f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_less_trans) show ?thesis .
qed

lemma order_le_less_subst2: "(a::'a::order) <= b ==> f b < (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a < c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b < c"
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_le_less_subst1: "(a::'a::order) <= f b ==> (b::'b::order) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a <= f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (order_le_less_trans) show ?thesis .
qed

lemma order_less_le_subst2: "(a::'a::order) < b ==> f b <= (c::'c::order) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b <= c"
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_less_le_subst1: "(a::'a::order) < f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a < f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a < f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_less_le_trans) show ?thesis .
qed

lemma order_subst1: "(a::'a::order) <= f b ==> (b::'b::order) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (order_trans) show ?thesis .
qed

lemma order_subst2: "(a::'a::order) <= b ==> f b <= (c::'c::order) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b <= c"
  finally (order_trans) show ?thesis .
qed

lemma ord_le_eq_subst: "a <= b ==> f b = c ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b = c"
  finally (ord_le_eq_trans) show ?thesis .
qed

lemma ord_eq_le_subst: "a = f b ==> b <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a = f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (ord_eq_le_trans) show ?thesis .
qed

lemma ord_less_eq_subst: "a < b ==> f b = c ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b = c"
  finally (ord_less_eq_trans) show ?thesis .
qed

lemma ord_eq_less_subst: "a = f b ==> b < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a = f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (ord_eq_less_trans) show ?thesis .
qed

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas basic_trans_rules [trans] =
  order_less_subst2
  order_less_subst1
  order_le_less_subst2
  order_le_less_subst1
  order_less_le_subst2
  order_less_le_subst1
  order_subst2
  order_subst1
  ord_le_eq_subst
  ord_eq_le_subst
  ord_less_eq_subst
  ord_eq_less_subst
  forw_subst
  back_subst
  rev_mp
  mp
  set_rev_mp
  set_mp
  order_neq_le_trans
  order_le_neq_trans
  order_less_trans
  order_less_asym'
  order_le_less_trans
  order_less_le_trans
  order_trans
  order_antisym
  ord_le_eq_trans
  ord_eq_le_trans
  ord_less_eq_trans
  ord_eq_less_trans
  trans

end
