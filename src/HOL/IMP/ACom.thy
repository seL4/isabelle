(* Author: Tobias Nipkow *)

theory ACom
imports Com
begin

(* is there a better place? *)
definition "show_state xs s = [(x,s x). x \<leftarrow> xs]"

section "Annotated Commands"

datatype 'a acom =
  SKIP   'a                           ("SKIP {_}") |
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


lemma strip_anno[simp]: "strip (anno a c) = c"
by(induct c) simp_all

lemma strip_eq_SKIP: "strip c = com.SKIP \<longleftrightarrow> (EX P. c = SKIP {P})"
by (cases c) simp_all

lemma strip_eq_Assign: "strip c = x::=e \<longleftrightarrow> (EX P. c = x::=e {P})"
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

end
