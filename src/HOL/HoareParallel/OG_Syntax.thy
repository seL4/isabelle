
header {* \section{Concrete Syntax} *}

theory OG_Syntax = Quote_Antiquote + OG_Tactics:

text{* Syntax for commands and for assertions and boolean expressions in 
 commands @{text com} and annotated commands @{text ann_com}. *}

syntax
  "_Assign"      :: "idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(\<acute>_ :=/ _)" [70, 65] 61)
  "_AnnAssign"   :: "'a assn \<Rightarrow> idt \<Rightarrow> 'b \<Rightarrow> 'a com"    ("(_ \<acute>_ :=/ _)" [90,70,65] 61)

translations
  "\<acute>\<spacespace>x := a" \<rightharpoonup> "Basic \<guillemotleft>\<acute>\<spacespace>(_update_name x a)\<guillemotright>"
  "r \<acute>\<spacespace>x := a" \<rightharpoonup> "AnnBasic r \<guillemotleft>\<acute>\<spacespace>(_update_name x a)\<guillemotright>"

syntax
  "_AnnSkip"     :: "'a assn \<Rightarrow> 'a ann_com"              ("_//SKIP" [90] 63)
  "_AnnSeq"      :: "'a ann_com \<Rightarrow> 'a ann_com \<Rightarrow> 'a ann_com"  ("_;;/ _" [60,61] 60)
  
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

  "_Skip"        :: "'a com"                 ("SKIP" 63)
  "_Seq"         :: "'a com \<Rightarrow> 'a com \<Rightarrow> 'a com" ("_,,/ _" [55, 56] 55)
  "_Cond"        :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com \<Rightarrow> 'a com" 
                                  ("(0IF _/ THEN _/ ELSE _/ FI)" [0, 0, 0] 61)
  "_Cond2"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"   ("IF _ THEN _ FI" [0,0] 56)
  "_While_inv"   :: "'a bexp \<Rightarrow> 'a assn \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    ("(0WHILE _/ INV _ //DO _ /OD)"  [0, 0, 0] 61)
  "_While"       :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a com"
                    ("(0WHILE _ //DO _ /OD)"  [0, 0] 61)

translations
  "SKIP" \<rightleftharpoons> "Basic id"
  "c_1,, c_2" \<rightleftharpoons> "Seq c_1 c_2"

  "IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "Cond .{b}. c1 c2"
  "IF b THEN c FI" \<rightleftharpoons> "IF b THEN c ELSE SKIP FI"
  "WHILE b INV i DO c OD" \<rightharpoonup> "While .{b}. i c"
  "WHILE b DO c OD" \<rightleftharpoons> "WHILE b INV arbitrary DO c OD"

  "r SKIP" \<rightleftharpoons> "AnnBasic r id"
  "c_1;; c_2" \<rightleftharpoons> "AnnSeq c_1 c_2" 
  "r IF b THEN c1 ELSE c2 FI" \<rightharpoonup> "AnnCond1 r .{b}. c1 c2"
  "r IF b THEN c FI" \<rightharpoonup> "AnnCond2 r .{b}. c"
  "r WHILE b INV i DO c OD" \<rightharpoonup> "AnnWhile r .{b}. i c"
  "r AWAIT b THEN c END" \<rightharpoonup> "AnnAwait r .{b}. c"
  "r \<langle>c\<rangle>" \<rightleftharpoons> "r AWAIT True THEN c END"
  "r WAIT b END" \<rightleftharpoons> "r AWAIT b THEN SKIP END"
 
nonterminals
  prgs

syntax
  "_PAR" :: "prgs \<Rightarrow> 'a"              ("COBEGIN//_//COEND" [57] 56)
  "_prg" :: "['a, 'a] \<Rightarrow> prgs"        ("_//_" [60, 90] 57)
  "_prgs" :: "['a, 'a, prgs] \<Rightarrow> prgs"  ("_//_//\<parallel>//_" [60,90,57] 57)

  "_prg_scheme" :: "['a, 'a, 'a, 'a, 'a] \<Rightarrow> prgs"  
                  ("SCHEME [_ \<le> _ < _] _// _" [0,0,0,60, 90] 57)

translations
  "_prg c q" \<rightleftharpoons> "[(Some c, q)]"
  "_prgs c q ps" \<rightleftharpoons> "(Some c, q) # ps"
  "_PAR ps" \<rightleftharpoons> "Parallel ps"

  "_prg_scheme j i k c q" \<rightleftharpoons> "(map (\<lambda>i. (Some c, q)) [j..k(])"

print_translation {*
  let
    fun quote_tr' f (t :: ts) =
          Term.list_comb (f $ Syntax.quote_tr' "_antiquote" t, ts)
      | quote_tr' _ _ = raise Match;

    fun annquote_tr' f (r :: t :: ts) =
          Term.list_comb (f $ r $ Syntax.quote_tr' "_antiquote" t, ts)
      | annquote_tr' _ _ = raise Match;

    val assert_tr' = quote_tr' (Syntax.const "_Assert");

    fun bexp_tr' name ((Const ("Collect", _) $ t) :: ts) =
          quote_tr' (Syntax.const name) (t :: ts)
      | bexp_tr' _ _ = raise Match;

    fun annbexp_tr' name (r :: (Const ("Collect", _) $ t) :: ts) =
          annquote_tr' (Syntax.const name) (r :: t :: ts)
      | annbexp_tr' _ _ = raise Match;

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

    fun annassign_tr' (r :: Abs (x, _, f $ t $ Bound 0) :: ts) =
          quote_tr' (Syntax.const "_AnnAssign" $ r $ update_name_tr' f)
            (Abs (x, dummyT, t) :: ts)
      | annassign_tr' _ = raise Match;

    fun Parallel_PAR [(Const ("Cons",_) $ (Const ("Pair",_) $ (Const ("Some",_) $ t1 ) $ t2) $ Const ("Nil",_))] = 
                   (Syntax.const "_prg" $ t1 $ t2)
      | Parallel_PAR [(Const ("Cons",_) $ (Const ("Pair",_) $ (Const ("Some",_) $ t1) $ t2) $ ts)] =
                     (Syntax.const "_prgs" $ t1 $ t2 $ Parallel_PAR [ts])
      | Parallel_PAR _ = raise Match;

fun Parallel_tr' ts = Syntax.const "_PAR" $ Parallel_PAR ts;
  in
    [("Collect", assert_tr'), ("Basic", assign_tr'), 
      ("Cond", bexp_tr' "_Cond"), ("While", bexp_tr' "_While_inv"),
      ("AnnBasic", annassign_tr'), 
      ("AnnWhile", annbexp_tr' "_AnnWhile"), ("AnnAwait", annbexp_tr' "_AnnAwait"),
      ("AnnCond1", annbexp_tr' "_AnnCond1"), ("AnnCond2", annbexp_tr' "_AnnCond2")]

  end

*}

end