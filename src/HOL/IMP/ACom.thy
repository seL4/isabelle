(* Author: Tobias Nipkow *)

theory ACom
imports Com
begin

(* is there a better place? *)
definition "show_state xs s = [(x,s x). x \<leftarrow> xs]"

subsection "Annotated Commands"

datatype 'a acom =
  SKIP 'a                           ("SKIP {_}" 61) |
  Assign vname aexp 'a              ("(_ ::= _/ {_})" [1000, 61, 0] 61) |
  Seq "('a acom)" "('a acom)"       ("_;//_"  [60, 61] 60) |
  If bexp 'a "('a acom)" 'a "('a acom)" 'a
    ("(IF _/ THEN ({_}/ _)/ ELSE ({_}/ _)//{_})"  [0, 0, 0, 61, 0, 0] 61) |
  While 'a bexp 'a "('a acom)" 'a
    ("({_}//WHILE _//DO ({_}//_)//{_})"  [0, 0, 0, 61, 0] 61)

fun post :: "'a acom \<Rightarrow>'a" where
"post (SKIP {P}) = P" |
"post (x ::= e {P}) = P" |
"post (c1; c2) = post c2" |
"post (IF b THEN {P1} c1 ELSE {P2} c2 {P}) = P" |
"post ({Inv} WHILE b DO {Pc} c {P}) = P"

fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {P}) = com.SKIP" |
"strip (x ::= e {P}) = (x ::= e)" |
"strip (c1;c2) = (strip c1; strip c2)" |
"strip (IF b THEN {P1} c1 ELSE {P2} c2 {P}) = (IF b THEN strip c1 ELSE strip c2)" |
"strip ({Inv} WHILE b DO {Pc} c {P}) = (WHILE b DO strip c)"

fun anno :: "'a \<Rightarrow> com \<Rightarrow> 'a acom" where
"anno a com.SKIP = SKIP {a}" |
"anno a (x ::= e) = (x ::= e {a})" |
"anno a (c1;c2) = (anno a c1; anno a c2)" |
"anno a (IF b THEN c1 ELSE c2) =
  (IF b THEN {a} anno a c1 ELSE {a} anno a c2 {a})" |
"anno a (WHILE b DO c) =
  ({a} WHILE b DO {a} anno a c {a})"

fun annos :: "'a acom \<Rightarrow> 'a list" where
"annos (SKIP {a}) = [a]" |
"annos (x::=e {a}) = [a]" |
"annos (C1;C2) = annos C1 @ annos C2" |
"annos (IF b THEN {a1} C1 ELSE {a2} C2 {a}) = a1 # a2 #a #  annos C1 @ annos C2" |
"annos ({i} WHILE b DO {ac} C {a}) = i # ac # a # annos C"

fun map_acom :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a acom \<Rightarrow> 'b acom" where
"map_acom f (SKIP {P}) = SKIP {f P}" |
"map_acom f (x ::= e {P}) = (x ::= e {f P})" |
"map_acom f (c1;c2) = (map_acom f c1; map_acom f c2)" |
"map_acom f (IF b THEN {p1} c1 ELSE {p2} c2 {P}) =
  (IF b THEN {f p1} map_acom f c1 ELSE {f p2} map_acom f c2 {f P})" |
"map_acom f ({Inv} WHILE b DO {p} c {P}) =
  ({f Inv} WHILE b DO {f p} map_acom f c {f P})"


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

lemma map_acom_Seq:
 "map_acom f c = c1';c2' \<longleftrightarrow>
 (\<exists>c1 c2. c = c1;c2 \<and> map_acom f c1 = c1' \<and> map_acom f c2 = c2')"
by (cases c) auto

lemma map_acom_If:
 "map_acom f c = IF b THEN {p1'} c1' ELSE {p2'} c2' {S'} \<longleftrightarrow>
 (\<exists>S p1 p2 c1 c2. c = IF b THEN {p1} c1 ELSE {p2} c2 {S} \<and>
     map_acom f c1 = c1' \<and> map_acom f c2 = c2' \<and> p1' = f p1 \<and> p2' = f p2 \<and> S' = f S)"
by (cases c) auto

lemma map_acom_While:
 "map_acom f w = {I'} WHILE b DO {p'} c' {P'} \<longleftrightarrow>
 (\<exists>I p P c. w = {I} WHILE b DO {p} c {P} \<and> map_acom f c = c' \<and> I' = f I \<and> p' = f p \<and> P' = f P)"
by (cases w) auto


lemma strip_anno[simp]: "strip (anno a c) = c"
by(induct c) simp_all

lemma strip_eq_SKIP:
  "strip C = com.SKIP \<longleftrightarrow> (EX P. C = SKIP {P})"
by (cases C) simp_all

lemma strip_eq_Assign:
  "strip C = x::=e \<longleftrightarrow> (EX P. C = x::=e {P})"
by (cases C) simp_all

lemma strip_eq_Seq:
  "strip C = c1;c2 \<longleftrightarrow> (EX C1 C2. C = C1;C2 & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_If:
  "strip C = IF b THEN c1 ELSE c2 \<longleftrightarrow>
  (EX p1 p2 C1 C2 P. C = IF b THEN {p1} C1 ELSE {p2} C2 {P} & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_While:
  "strip C = WHILE b DO c1 \<longleftrightarrow>
  (EX I p C1 P. C = {I} WHILE b DO {p} C1 {P} & strip C1 = c1)"
by (cases C) simp_all

lemma set_annos_anno[simp]: "set (annos (anno a C)) = {a}"
by(induction C)(auto)

lemma size_annos_same: "strip C1 = strip C2 \<Longrightarrow> size(annos C1) = size(annos C2)"
apply(induct C2 arbitrary: C1)
apply (auto simp: strip_eq_SKIP strip_eq_Assign strip_eq_Seq strip_eq_If strip_eq_While)
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]

end
