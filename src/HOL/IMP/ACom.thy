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
"post (C1; C2) = post C2" |
"post (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) = Q" |
"post ({Inv} WHILE b DO {P} C {Q}) = Q"

fun strip :: "'a acom \<Rightarrow> com" where
"strip (SKIP {P}) = com.SKIP" |
"strip (x ::= e {P}) = (x ::= e)" |
"strip (C1;C2) = (strip C1; strip C2)" |
"strip (IF b THEN {P1} C1 ELSE {P2} C2 {P}) = (IF b THEN strip C1 ELSE strip C2)" |
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
"map_acom f (C1;C2) = (map_acom f C1; map_acom f C2)" |
"map_acom f (IF b THEN {P1} C1 ELSE {P2} C2 {Q}) =
  (IF b THEN {f P1} map_acom f C1 ELSE {f P2} map_acom f C2 {f Q})" |
"map_acom f ({Inv} WHILE b DO {P} C {Q}) =
  ({f Inv} WHILE b DO {f P} map_acom f C {f Q})"


lemma post_map_acom[simp]: "post(map_acom f C) = f(post C)"
by (induction C) simp_all

lemma strip_acom[simp]: "strip (map_acom f C) = strip C"
by (induction C) auto

lemma map_acom_SKIP:
 "map_acom f C = SKIP {S'} \<longleftrightarrow> (\<exists>S. C = SKIP {S} \<and> S' = f S)"
by (cases C) auto

lemma map_acom_Assign:
 "map_acom f C = x ::= e {S'} \<longleftrightarrow> (\<exists>S. C = x::=e {S} \<and> S' = f S)"
by (cases C) auto

lemma map_acom_Seq:
 "map_acom f C = C1';C2' \<longleftrightarrow>
 (\<exists>C1 C2. C = C1;C2 \<and> map_acom f C1 = C1' \<and> map_acom f C2 = C2')"
by (cases C) auto

lemma map_acom_If:
 "map_acom f C = IF b THEN {P1'} C1' ELSE {P2'} C2' {Q'} \<longleftrightarrow>
 (\<exists>P1 P2 C1 C2 Q. C = IF b THEN {P1} C1 ELSE {P2} C2 {Q} \<and>
     map_acom f C1 = C1' \<and> map_acom f C2 = C2' \<and> P1' = f P1 \<and> P2' = f P2 \<and> Q' = f Q)"
by (cases C) auto

lemma map_acom_While:
 "map_acom f w = {I'} WHILE b DO {p'} C' {P'} \<longleftrightarrow>
 (\<exists>I p P C. w = {I} WHILE b DO {p} C {P} \<and> map_acom f C = C' \<and> I' = f I \<and> p' = f p \<and> P' = f P)"
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
  (EX P1 P2 C1 C2 Q. C = IF b THEN {P1} C1 ELSE {P2} C2 {Q} & strip C1 = c1 & strip C2 = c2)"
by (cases C) simp_all

lemma strip_eq_While:
  "strip C = WHILE b DO c1 \<longleftrightarrow>
  (EX I P C1 Q. C = {I} WHILE b DO {P} C1 {Q} & strip C1 = c1)"
by (cases C) simp_all

lemma set_annos_anno[simp]: "set (annos (anno a c)) = {a}"
by(induction c)(auto)

lemma size_annos_same: "strip C1 = strip C2 \<Longrightarrow> size(annos C1) = size(annos C2)"
apply(induct C2 arbitrary: C1)
apply (auto simp: strip_eq_SKIP strip_eq_Assign strip_eq_Seq strip_eq_If strip_eq_While)
done

lemmas size_annos_same2 = eqTrueI[OF size_annos_same]

end
