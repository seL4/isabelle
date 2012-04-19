(* Author: Tobias Nipkow *)

theory ACom
imports Com
begin

(* is there a better place? *)
definition "show_state xs s = [(x,s x). x \<leftarrow> xs]"

subsection "Annotated Commands"

datatype 'a acom =
  SKIP   'a                           ("SKIP {_}" 61) |
  Assign vname aexp 'a                ("(_ ::= _/ {_})" [1000, 61, 0] 61) |
  Semi   "('a acom)" "('a acom)"          ("_;//_"  [60, 61] 60) |
  If     bexp "('a acom)" "('a acom)" 'a
    ("(IF _/ THEN _/ ELSE _//{_})"  [0, 0, 61, 0] 61) |
  While  'a bexp "('a acom)" 'a
    ("({_}//WHILE _/ DO (_)//{_})"  [0, 0, 61, 0] 61)

fun post :: "'a acom \<Rightarrow>'a" where
"post (SKIP {P}) = P" |
"post (x ::= e {P}) = P" |
"post (c1; c2) = post c2" |
"post (IF b THEN c1 ELSE c2 {P}) = P" |
"post ({Inv} WHILE b DO c {P}) = P"

fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {P}) = com.SKIP" |
"strip (x ::= e {P}) = (x ::= e)" |
"strip (c1;c2) = (strip c1; strip c2)" |
"strip (IF b THEN c1 ELSE c2 {P}) = (IF b THEN strip c1 ELSE strip c2)" |
"strip ({Inv} WHILE b DO c {P}) = (WHILE b DO strip c)"

fun anno :: "'a \<Rightarrow> com \<Rightarrow> 'a acom" where
"anno a com.SKIP = SKIP {a}" |
"anno a (x ::= e) = (x ::= e {a})" |
"anno a (c1;c2) = (anno a c1; anno a c2)" |
"anno a (IF b THEN c1 ELSE c2) =
  (IF b THEN anno a c1 ELSE anno a c2 {a})" |
"anno a (WHILE b DO c) =
  ({a} WHILE b DO anno a c {a})"

fun annos :: "'a acom \<Rightarrow> 'a list" where
"annos (SKIP {a}) = [a]" |
"annos (x::=e {a}) = [a]" |
"annos (C1;C2) = annos C1 @ annos C2" |
"annos (IF b THEN C1 ELSE C2 {a}) = a #  annos C1 @ annos C2" |
"annos ({i} WHILE b DO C {a}) = i # a # annos C"

fun map_acom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a acom \<Rightarrow> 'b acom" where
"map_acom f (SKIP {P}) = SKIP {f P}" |
"map_acom f (x ::= e {P}) = (x ::= e {f P})" |
"map_acom f (c1;c2) = (map_acom f c1; map_acom f c2)" |
"map_acom f (IF b THEN c1 ELSE c2 {P}) =
  (IF b THEN map_acom f c1 ELSE map_acom f c2 {f P})" |
"map_acom f ({Inv} WHILE b DO c {P}) =
  ({f Inv} WHILE b DO map_acom f c {f P})"


lemma post_map_acom[simp]: "post(map_acom f c) = f(post c)"
by (induction c) simp_all

lemma strip_acom[simp]: "strip (map_acom f c) = strip c"
by (induction c) auto

lemma map_acom_SKIP:
 "map_acom f c = SKIP {S'} \<longleftrightarrow> (\<exists>S. c = SKIP {S} \<and> S' = f S)"
by (cases c) auto

lemma map_acom_Assign:
 "map_acom f c = x ::= e {S'} \<longleftrightarrow> (\<exists>S. c = x::=e {S} \<and> S' = f S)"
by (cases c) auto

lemma map_acom_Semi:
 "map_acom f c = c1';c2' \<longleftrightarrow>
 (\<exists>c1 c2. c = c1;c2 \<and> map_acom f c1 = c1' \<and> map_acom f c2 = c2')"
by (cases c) auto

lemma map_acom_If:
 "map_acom f c = IF b THEN c1' ELSE c2' {S'} \<longleftrightarrow>
 (\<exists>S c1 c2. c = IF b THEN c1 ELSE c2 {S} \<and> map_acom f c1 = c1' \<and> map_acom f c2 = c2' \<and> S' = f S)"
by (cases c) auto

lemma map_acom_While:
 "map_acom f w = {I'} WHILE b DO c' {P'} \<longleftrightarrow>
 (\<exists>I P c. w = {I} WHILE b DO c {P} \<and> map_acom f c = c' \<and> I' = f I \<and> P' = f P)"
by (cases w) auto


lemma strip_anno[simp]: "strip (anno a c) = c"
by(induct c) simp_all

lemma strip_eq_SKIP:
  "strip c = com.SKIP \<longleftrightarrow> (EX P. c = SKIP {P})"
by (cases c) simp_all

lemma strip_eq_Assign:
  "strip c = x::=e \<longleftrightarrow> (EX P. c = x::=e {P})"
by (cases c) simp_all

lemma strip_eq_Semi:
  "strip c = c1;c2 \<longleftrightarrow> (EX d1 d2. c = d1;d2 & strip d1 = c1 & strip d2 = c2)"
by (cases c) simp_all

lemma strip_eq_If:
  "strip c = IF b THEN c1 ELSE c2 \<longleftrightarrow>
  (EX d1 d2 P. c = IF b THEN d1 ELSE d2 {P} & strip d1 = c1 & strip d2 = c2)"
by (cases c) simp_all

lemma strip_eq_While:
  "strip c = WHILE b DO c1 \<longleftrightarrow>
  (EX I d1 P. c = {I} WHILE b DO d1 {P} & strip d1 = c1)"
by (cases c) simp_all


lemma set_annos_anno[simp]: "set (annos (anno a C)) = {a}"
by(induction C)(auto)

lemma size_annos_same: "strip C1 = strip C2 \<Longrightarrow> size(annos C1) = size(annos C2)"
apply(induct C2 arbitrary: C1)
apply (auto simp: strip_eq_SKIP strip_eq_Assign strip_eq_Semi strip_eq_If strip_eq_While)
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]


end
