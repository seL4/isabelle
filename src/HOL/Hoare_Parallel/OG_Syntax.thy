theory OG_Syntax
imports OG_Tactics Quote_Antiquote
begin

text\<open>Syntax for commands and for assertions and boolean expressions in
 commands \<open>com\<close> and annotated commands \<open>ann_com\<close>.\<close>

abbreviation Skip :: "'a com"  (\<open>SKIP\<close> 63)
  where "SKIP \<equiv> Basic id"

abbreviation AnnSkip :: "'a assn \<Rightarrow> 'a ann_com"  (\<open>_//SKIP\<close> [90] 63)
  where "r SKIP \<equiv> AnnBasic r id"

notation
  Seq  (\<open>_,,/ _\<close> [55, 56] 55) and
  AnnSeq  (\<open>_;;/ _\<close> [60,61] 60)

syntax
  "_Assign"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"    (\<open>(\<acute>_ :=/ _)\<close> [70, 65] 61)
  "_AnnAssign"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    (\<open>(_ \<acute>_ :=/ _)\<close> [90,70,65] 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "r \<acute>x := a" \<rightharpoonup> "CONST AnnBasic r \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"

syntax
  "_AnnCond1"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    (\<open>_ //IF _ /THEN _ /ELSE _ /FI\<close>  [90,0,0,0] 61)
  "_AnnCond2"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    (\<open>_ //IF _ /THEN _ /FI\<close>  [90,0,0] 61)
  "_AnnWhile"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a assn \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"
                    (\<open>_ //WHILE _ /INV _ //DO _//OD\<close>  [90,0,0,0] 61)
  "_AnnAwait"    :: "'a assn \<Rightarrow> 'a bexp  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"
                    (\<open>_ //AWAIT _ /THEN /_ /END\<close>  [90,0,0] 61)
  "_AnnAtom"     :: "'a assn  \<Rightarrow> 'a com \<Rightarrow> 'a ann_com"   (\<open>_//\<langle>_\<rangle>\<close> [90,0] 61)
  "_AnnWait"     :: "'a assn \<Rightarrow> 'a bexp \<Rightarrow> 'a ann_com"   (\<open>_//WAIT _ END\<close> [90,0] 61)

  "_Cond"        :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"
                                  (\<open>(0IF _/ THEN _/ ELSE _/ FI)\<close> [0, 0, 0] 61)
  "_Cond2"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"   (\<open>IF _ THEN _ FI\<close> [0,0] 56)
  "_While_inv"   :: "'a bexp \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    (\<open>(0WHILE _/ INV _ //DO _ /OD)\<close>  [0, 0, 0] 61)
  "_While"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    (\<open>(0WHILE _ //DO _ /OD)\<close>  [0, 0] 61)

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
  "_PAR" :: "prgs \<Rightarrow> 'a"              (\<open>COBEGIN//_//COEND\<close> [57] 56)
  "_prg" :: "['a, 'a] \<Rightarrow> prgs"        (\<open>_//_\<close> [60, 90] 57)
  "_prgs" :: "['a, 'a, prgs] \<Rightarrow> prgs"  (\<open>_//_//\<parallel>//_\<close> [60,90,57] 57)

  "_prg_scheme" :: "['a, 'a, 'a, 'a, 'a] \<Rightarrow> prgs"
                  (\<open>SCHEME [_ \<le> _ < _] _// _\<close> [0,0,0,60, 90] 57)

translations
  "_prg c q" \<rightleftharpoons> "[(CONST Some c, q)]"
  "_prgs c q ps" \<rightleftharpoons> "(CONST Some c, q) # ps"
  "_PAR ps" \<rightleftharpoons> "CONST Parallel ps"

  "_prg_scheme j i k c q" \<rightleftharpoons> "CONST map (\<lambda>i. (CONST Some c, q)) [j..<k]"

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' \<^syntax_const>\<open>_antiquote\<close> t, ts)
      | quote_tr' _ _ = raise Match;

    fun annquote_tr' f (r :: t :: ts) =
          Term.list_comb (f $ r $ Syntax_Trans.quote_tr' \<^syntax_const>\<open>_antiquote\<close> t, ts)
      | annquote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const \<^syntax_const>\<open>_Assert\<close>);

    fun bexp_tr' name ((Const (\<^const_syntax>\<open>Collect\<close>, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun annbexp_tr' name (r :: (Const (\<^const_syntax>\<open>Collect\<close>, _) $ t) :: ts) =
          annquote_tr' (Syntax.const name) (r :: t :: ts)
      | annbexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const \<^syntax_const>\<open>_Assign\<close> $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;

    fun annassign_tr' (r :: Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const \<^syntax_const>\<open>_AnnAssign\<close> $ r $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | annassign_tr' _ = raise Match;

    fun Parallel_PAR [(Const (\<^const_syntax>\<open>Cons\<close>, _) $
            (Const (\<^const_syntax>\<open>Pair\<close>, _) $ (Const (\<^const_syntax>\<open>Some\<close>,_) $ t1 ) $ t2) $
            Const (\<^const_syntax>\<open>Nil\<close>, _))] = Syntax.const \<^syntax_const>\<open>_prg\<close> $ t1 $ t2
      | Parallel_PAR [(Const (\<^const_syntax>\<open>Cons\<close>, _) $
            (Const (\<^const_syntax>\<open>Pair\<close>, _) $ (Const (\<^const_syntax>\<open>Some\<close>, _) $ t1) $ t2) $ ts)] =
          Syntax.const \<^syntax_const>\<open>_prgs\<close> $ t1 $ t2 $ Parallel_PAR [ts]
      | Parallel_PAR _ = raise Match;

    fun Parallel_tr' ts = Syntax.const \<^syntax_const>\<open>_PAR\<close> $ Parallel_PAR ts;
  in
   [(\<^const_syntax>\<open>Collect\<close>, K assert_tr'),
    (\<^const_syntax>\<open>Basic\<close>, K assign_tr'),
    (\<^const_syntax>\<open>Cond\<close>, K (bexp_tr' \<^syntax_const>\<open>_Cond\<close>)),
    (\<^const_syntax>\<open>While\<close>, K (bexp_tr' \<^syntax_const>\<open>_While_inv\<close>)),
    (\<^const_syntax>\<open>AnnBasic\<close>, K annassign_tr'),
    (\<^const_syntax>\<open>AnnWhile\<close>, K (annbexp_tr' \<^syntax_const>\<open>_AnnWhile\<close>)),
    (\<^const_syntax>\<open>AnnAwait\<close>, K (annbexp_tr' \<^syntax_const>\<open>_AnnAwait\<close>)),
    (\<^const_syntax>\<open>AnnCond1\<close>, K (annbexp_tr' \<^syntax_const>\<open>_AnnCond1\<close>)),
    (\<^const_syntax>\<open>AnnCond2\<close>, K (annbexp_tr' \<^syntax_const>\<open>_AnnCond2\<close>))]
  end
\<close>

end
