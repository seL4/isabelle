
header {* \section{Concrete Syntax} *}

theory RG_Syntax = Quote_Antiquote + RG_Hoare:

syntax
  "_Assign"    :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"                     ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_skip"      :: "'a com"                                  ("SKIP")
  "_Seq"       :: "'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"              ("(_;;/ _)" [60,61] 60)
  "_Cond"      :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com"   ("(0IF _/ THEN _/ ELSE _/FI)" [0, 0, 0] 61)
  "_Cond2"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             ("(0IF _ THEN _ FI)" [0,0] 56)
  "_While"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             ("(0WHILE _ /DO _ /OD)"  [0, 0] 61)
  "_Await"     :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"             ("(0AWAIT _ /THEN /_ /END)"  [0,0] 61)
  "_Atom"      :: "'a com \<Rightarrow> 'a com"                        ("(\<langle>_\<rangle>)" 61)
  "_Wait"      :: "'a bexp \<Rightarrow> 'a com"                       ("(0WAIT _ END)" 61)

translations
  "\<acute>\<spacespace>x := a" \<rightharpoonup> "Basic \<guillemotleft>\<acute>\<spacespace>(_update_name x a)\<guillemotright>"
  "SKIP" \<rightleftharpoons> "Basic id"
  "c1;; c2" \<rightleftharpoons> "Seq c1 c2"
  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "Cond .{b}. c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b DO c OD" \<rightharpoonup> "While .{b}. c"
  "AWAIT b THEN c END" \<rightleftharpoons> "Await .{b}. c"
  "\<langle>c\<rangle>" \<rightleftharpoons> "AWAIT True THEN c END"
  "WAIT b END" \<rightleftharpoons> "AWAIT b THEN SKIP END"

nonterminals
  prgs

syntax
  "_PAR"        :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" 60)
  "_prg"        :: "'a \<Rightarrow> prgs"              ("_" 57)
  "_prgs"       :: "['a, prgs] \<Rightarrow> prgs"      ("_//\<parallel>//_" [60,57] 57)

translations
  "_prg a" \<rightharpoonup> "[a]"
  "_prgs a ps" \<rightharpoonup> "a # ps"
  "_PAR ps" \<rightharpoonup> "ps"

syntax
  "_prg_scheme" :: "['a, 'a, 'a, 'a] \<Rightarrow> prgs"  ("SCHEME [_ \<le> _ < _] _" [0,0,0,60] 57)

translations
  "_prg_scheme j i k c" \<rightleftharpoons> "(map (\<lambda>i. c) [j..k(])"

text {* Translations for variables before and after a transition: *}

syntax 
  "_before" :: "id \<Rightarrow> 'a" ("\<ordmasculine>_")
  "_after"  :: "id \<Rightarrow> 'a" ("\<ordfeminine>_")
 
translations
  "\<ordmasculine>x" \<rightleftharpoons> "x \<acute>fst"
  "\<ordfeminine>x" \<rightleftharpoons> "x \<acute>snd"

print_translation {*
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax.quote_tr' "_antiquote" t, ts)
      | quote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const "_Assert");

    fun bexp_tr' name ((Const ("Collect", _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun upd_tr' (x_upd, T) =
      (case try (unsuffix RecordPackage.updateN) x_upd of
        Some x => (x, if T = dummyT then T else Term.domain_type T)
      | None => raise Match);

    fun update_name_tr' (Free x) = Free (upd_tr' x)
      | update_name_tr' ((c as Const ("_free", _)) $ Free x) =
          c $ Free (upd_tr' x)
      | update_name_tr' (Const x) = Const (upd_tr' x)
      | update_name_tr' _ = raise Match;

    fun assign_tr' (Abs (x, _, f $ t $ Bound 0) :: ts) =
          quote_tr' (Syntax.const "_Assign" $ update_name_tr' f)
            (Abs (x, dummyT, t) :: ts)
      | assign_tr' _ = raise Match;
  in
    [("Collect", assert_tr'), ("Basic", assign_tr'),
      ("Cond", bexp_tr' "_Cond"), ("While", bexp_tr' "_While_inv")]
  end
*}

end