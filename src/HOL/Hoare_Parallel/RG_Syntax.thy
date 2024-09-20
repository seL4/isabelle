section \<open>Concrete Syntax\<close>

theory RG_Syntax
imports RG_Hoare Quote_Antiquote
begin

abbreviation Skip :: "'a com"  (\<open>SKIP\<close>)
  where "SKIP \<equiv> Basic id"

notation Seq  (\<open>(_;;/ _)\<close> [60,61] 60)

syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"                     (\<open>(\<acute>_ :=/ _)\<close> [70, 65] 61)
  "_Cond"      :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"   (\<open>(0IF _/ THEN _/ ELSE _/FI)\<close> [0, 0, 0] 61)
  "_Cond2"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             (\<open>(0IF _ THEN _ FI)\<close> [0,0] 56)
  "_While"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             (\<open>(0WHILE _ /DO _ /OD)\<close>  [0, 0] 61)
  "_Await"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             (\<open>(0AWAIT _ /THEN /_ /END)\<close>  [0,0] 61)
  "_Atom"      :: "'a com \<Rightarrow> 'a com"                        (\<open>(\<langle>_\<rangle>)\<close> 61)
  "_Wait"      :: "'a bexp \<Rightarrow> 'a com"                       (\<open>(0WAIT _ END)\<close> 61)

translations
  "\<acute>x := a" \<rightharpoonup> "CONST Basic \<guillemotleft>\<acute>(_update_name x (\<lambda>_. a))\<guillemotright>"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "CONST Cond \<lbrace>b\<rbrace> c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b DO c OD" \<rightharpoonup> "CONST While \<lbrace>b\<rbrace> c"
  "AWAIT b THEN c END" \<rightleftharpoons> "CONST Await \<lbrace>b\<rbrace> c"
  "\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT CONST True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"

nonterminal prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              (\<open>COBEGIN//_//COEND\<close> 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              (\<open>_\<close> 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      (\<open>_//\<parallel>//_\<close> [60,57] 57)

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_PAR ps" \<rightharpoonup> "ps"

syntax
  "_prg_scheme" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"  (\<open>SCHEME [_ \<le> _ < _] _\<close> [0,0,0,60] 57)

translations
  "_prg_scheme j i k c" \<rightleftharpoons> "(CONST map (\<lambda>i. c) [j..<k])"

text \<open>Translations for variables before and after a transition:\<close>

syntax
  "_before" :: "id \<Rightarrow> 'a" (\<open>\<ordmasculine>_\<close>)
  "_after"  :: "id \<Rightarrow> 'a" (\<open>\<ordfeminine>_\<close>)

translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute>CONST fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute>CONST snd"

print_translation \<open>
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax_Trans.quote_tr' \<^syntax_const>\<open>_antiquote\<close> t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const \<^syntax_const>\<open>_Assert\<close>);

    fun bexp_tr' name ((Const (\<^const_syntax>\<open>Collect\<close>, _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ k $ Bound 0) :: ts) =
          quote_tr' (Syntax.const \<^syntax_const>\<open>_Assign\<close> $ Syntax_Trans.update_name_tr' f)
            (Abs (x, dummyT, Syntax_Trans.const_abs_tr' k) :: ts)
      | assign_tr' _ = raise Match;
  in
   [(\<^const_syntax>\<open>Collect\<close>, K assert_tr'),
    (\<^const_syntax>\<open>Basic\<close>, K assign_tr'),
    (\<^const_syntax>\<open>Cond\<close>, K (bexp_tr' \<^syntax_const>\<open>_Cond\<close>)),
    (\<^const_syntax>\<open>While\<close>, K (bexp_tr' \<^syntax_const>\<open>_While\<close>))]
  end
\<close>

end
