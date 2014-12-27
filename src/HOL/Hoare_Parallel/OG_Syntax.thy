theory OG_Syntax
imports OG_Tactics Quote_Antiquote
begin

text\<open>Syntax for commands and for assertions and boolean expressions in
 commands @{text com} and annotated commands @{text ann_com}.\<close>

abbreviation Skip :: "'a com"  ("SKIP" 63)
  where "SKIP \<equiv> Basic id"

abbreviation AnnSkip :: "'a assn \<Rightarrow> 'a ann_com"  ("_//SKIP" [90] 63)
  where "r SKIP \<equiv> AnnBasic r id"

notation
  Seq  ("_,,/ _" [55, 56] 55) and
  AnnSeq  ("_;;/ _" [60,61] 60)

syntax
  "_Assign"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_AnnAssign"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(_ \<acute>_ :=/ _)" [90,70,65] 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "r \<acute>x := a" \<rightharpoonup> "CONST AnnBasic r \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"

syntax
  "_AnnCond1"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //IF _ /THEN _ /ELSE _ /FI"  [90,0,0,0] 61)
  "_AnnCond2"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //IF _ /THEN _ /FI"  [90,0,0] 61)
  "_AnnWhile"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    ("_ //WHILE _ /INV _ //DO _//OD"  [90,0,0,0] 61)
  "_AnnAwait"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"
                    ("_ //AWAIT _ /THEN /_ /END"  [90,0,0] 61)
  "_AnnAtom"     :: "'a assn  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"   ("_//\<langle>_\<rangle>" [90,0] 61)
  "_AnnWait"     :: "'a assn \<Rightarrow> 'a bexp \<Rightarrow> 'a ann_com"   ("_//WAIT _ END" [90,0] 61)

  "_Cond"        :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"
                                  ("(0IF _/ THEN _/ ELSE _/ FI)" [0, 0, 0] 61)
  "_Cond2"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"   ("IF _ THEN _ FI" [0,0] 56)
  "_While_inv"   :: "'a bexp \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    ("(0WHILE _/ INV _ //DO _ /OD)"  [0, 0, 0] 61)
  "_While"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    ("(0WHILE _ //DO _ /OD)"  [0, 0] 61)

translations
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cond \<lbrace>b\<rbrace> c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b INV i DO c OD" \<rightharpoonup> "CONST While \<lbrace>b\<rbrace> i c"
  "WHILE b DO c OD" \<rightleftharpoons> "WHILE b INV CONST undefined DO c OD"

  "r IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST AnnCond1 r \<lbrace>b\<rbrace> c1 c2"
  "r IF b THEN c FI" \<rightharpoonup> "CONST AnnCond2 r \<lbrace>b\<rbrace> c"
  "r WHILE b INV i DO c OD" \<rightharpoonup> "CONST AnnWhile r \<lbrace>b\<rbrace> i c"
  "r AWAIT b THEN c END" \<rightharpoonup> "CONST AnnAwait r \<lbrace>b\<rbrace> c"
  "r \<langle>c\<rangle>" \<rightleftharpoons> "r AWAIT CONST True THEN c END"
  "r WAIT b END" \<rightleftharpoons> "r AWAIT b THEN SKIP END"

nonterminal prgs

syntax
  "_PAR" :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" [57] 56)
  "_prg" :: "['a, 'a] \<Rightarrow> prgs"        ("_//_" [60, 90] 57)
  "_prgs" :: "['a, 'a, prgs] \<Rightarrow> prgs"  ("_//_//\<parallel>//_" [60,90,57] 57)

  "_prg_scheme" :: "['a, 'a, 'a, 'a, 'a] \<Rightarrow> prgs"
                  ("SCHEME [_ \<le> _ < _] _// _" [0,0,0,60, 90] 57)

translations
  "_prg c q" \<rightleftharpoons> "[(CONST Some c, q)]"
  "_prgs c q ps" \<rightleftharpoons> "(CONST Some c, q) # ps"
  "_PAR ps" \<rightleftharpoons> "CONST Parallel ps"

  "_prg_scheme j i k c q" \<rightleftharpoons> "CONST map (\<lambda>i. (CONST Some c, q)) [j..<k]"

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | quote_tr' _ _ = raise Match;

    fun annquote_tr' f (r :: t :: ts) =
          Term.list_comb (f $ r $ Syntax_Trans.quote_tr' @{syntax_const "_antiquote"} t, ts)
      | annquote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const @{syntax_const "_Assert"});

    fun bexp_tr' name ((Const (@{const_syntax Collect}, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun annbexp_tr' name (r :: (Const (@{const_syntax Collect}, _) $ t) :: ts) =
          annquote_tr' (Syntax.const name) (r :: t :: ts)
      | annbexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const @{syntax_const "_Assign"} $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;

    fun annassign_tr' (r :: Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const @{syntax_const "_AnnAssign"} $ r $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | annassign_tr' _ = raise Match;

    fun Parallel_PAR [(Const (@{const_syntax Cons}, _) $
            (Const (@{const_syntax Pair}, _) $ (Const (@{const_syntax Some},_) $ t1 ) $ t2) $
            Const (@{const_syntax Nil}, _))] = Syntax.const @{syntax_const "_prg"} $ t1 $ t2
      | Parallel_PAR [(Const (@{const_syntax Cons}, _) $
            (Const (@{const_syntax Pair}, _) $ (Const (@{const_syntax Some}, _) $ t1) $ t2) $ ts)] =
          Syntax.const @{syntax_const "_prgs"} $ t1 $ t2 $ Parallel_PAR [ts]
      | Parallel_PAR _ = raise Match;

    fun Parallel_tr' ts = Syntax.const @{syntax_const "_PAR"} $ Parallel_PAR ts;
  in
   [(@{const_syntax Collect}, K assert_tr'),
    (@{const_syntax Basic}, K assign_tr'),
    (@{const_syntax Cond}, K (bexp_tr' @{syntax_const "_Cond"})),
    (@{const_syntax While}, K (bexp_tr' @{syntax_const "_While_inv"})),
    (@{const_syntax AnnBasic}, K annassign_tr'),
    (@{const_syntax AnnWhile}, K (annbexp_tr' @{syntax_const "_AnnWhile"})),
    (@{const_syntax AnnAwait}, K (annbexp_tr' @{syntax_const "_AnnAwait"})),
    (@{const_syntax AnnCond1}, K (annbexp_tr' @{syntax_const "_AnnCond1"})),
    (@{const_syntax AnnCond2}, K (annbexp_tr' @{syntax_const "_AnnCond2"}))]
  end;
\<close>

end