theory l2 = Main:

text {*
  \section*{Sortieren auf Listen}

  Der erste Teil des Blattes beschäftigt sich mit einem
  einfachen Sortieralgorithmus auf Listen von natürlichen Zahlen.
  Ihre Aufgabe ist es, den Sortieralgorithmus in Isabelle zu
  programmieren und zu zeigen, dass Ihre Implementierung korrekt ist.

  Der Algorithmus lässt sich in folgende Funktionen zerlegen:
*}
consts 
  insort :: "nat \<Rightarrow> nat list \<Rightarrow> nat list"
  sort   :: "nat list \<Rightarrow> nat list"
  le     :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  sorted :: "nat list \<Rightarrow> bool"
text {*
  Hierbei soll @{term "insort x xs"} eine Zahl @{term x} in eine
  sortierte Liste @{text xs} einfügen, und die Funktion @{term "sort ys"}
  (aufbauend auf @{text insort}) die sortierte Version von @{text ys}
  liefern.

  Um zu zeigen, dass die resultierende Liste tatsächlich sortiert
  ist, benötigen sie das Prädikat @{term "sorted xs"}, das überprüft
  ob jedes Element der Liste kleiner ist als alle folgenden Elemente
  der Liste. Die Funktion @{term "le n xs"} soll genau dann wahr sein,
  wenn @{term n} kleiner oder gleich allen Elementen von @{text xs}
  ist. 
*}
primrec
  "le a [] = True"
  "le a (x#xs) = (a <= x & le a xs)"

primrec
  "sorted [] = True"
  "sorted (x#xs) = (le x xs & sorted xs)"

primrec
  "insort a [] = [a]"
  "insort a (x#xs) = (if a <= x then a#x#xs else x # insort a xs)"

primrec
  "sort [] = []"
  "sort (x#xs) = insort x (sort xs)"

lemma "le 3 [7,10,3]" by auto

lemma "\<not> le 3 [7,10,2]" by auto

lemma "sorted [1,2,3,4]" by auto

lemma "\<not> sorted [3,1,4,2]" by auto

lemma "sort [3,1,4,2] = [1,2,3,4]" by auto

text {*
  Zeigen Sie zu Beginn folgendes Monotonie-Lemma über @{term le}. Die
  Formulierung des Lemmas ist aus technischen Gründen (über die sie
  später mehr erfahren werden) etwas ungewohnt:
*} 
lemma [simp]: "x \<le> y \<Longrightarrow> le y xs \<longrightarrow> le x xs"
  apply (induct_tac xs)
  apply auto
  done

lemma [simp]: 
  "le x (insort a xs) = (x <= a & le x xs)"
  apply (induct_tac xs)
  apply auto
  done

lemma [simp]:
  "sorted (insort a xs) = sorted xs"
  apply (induct_tac xs)
  apply auto
  done

theorem "sorted (sort xs)"
  apply (induct_tac xs)
  apply auto
  done

text  {*
  Das Theorem sagt zwar aus, dass Ihr Algorithmus eine sortierte
  Liste zurückgibt, es gibt Ihnen aber nicht die Sicherheit, dass die sortierte
  Liste auch die gleichen Elemente wie das Original enthält. Formulieren Sie deswegen
  eine Funktion @{term "count xs x"}, die zählt, wie oft die Zahl
  @{term x} in @{term xs} vorkommt.  
*}
consts
  count :: "nat list => nat => nat"
primrec
  "count [] y = 0"
  "count (x#xs) y = (if x=y then Suc(count xs y) else count xs y)"

lemma "count [2,3,1,3] 3 = 2" by auto

lemma "count [2,3,1,3] 7 = 0" by auto

lemma "count [2,3,1,3] 2 = 1" by auto

lemma [simp]:
  "count (insort x xs) y =
  (if x=y then Suc (count xs y) else count xs y)"
  apply (induct_tac xs)
  apply auto
  done

theorem "count (sort xs) x = count xs x"
  apply (induct_tac xs)
  apply auto
  done

text {*
  \section*{Sortieren mit Bäumen}

  Der zweite Teil des Blattes beschäftigt sich mit einem
  Sortieralgorithmus, der Bäume verwendet.
  Definieren Sie dazu zuerst den Datentyp @{text bintree} der
  Binärbäume. Für diese Aufgabe sind Binärbäume entweder leer, oder
  bestehen aus einem
  Knoten mit einer natürlichen Zahl und zwei Unterbäumen.  

  Schreiben Sie dann eine Funktion @{text tsorted}, die feststellt, ob
  ein Binärbaum geordnet ist. Sie werden dazu zwei Hilfsfunktionen
  @{text tge} und @{text tle} benötigen, die überprüfen ob eine Zahl
  grössergleich/kleinergleich als alle Elemente eines Baumes sind.

  Formulieren Sie schliesslich eine Funktion @{text tree_of}, die zu einer
  (unsortierten) Liste den geordneten Binärbaum zurückgibt. Stützen Sie
  sich dabei auf eine Funktion @{term "ins n b"}, die eine Zahl @{term
  n} in einen geordneten Binärbaum @{term b} einfügt.  
*}

datatype bintree = Empty | Node nat bintree bintree

consts
  tsorted :: "bintree \<Rightarrow> bool"
  tge :: "nat \<Rightarrow> bintree \<Rightarrow> bool"
  tle :: "nat \<Rightarrow> bintree \<Rightarrow> bool"
  ins :: "nat \<Rightarrow> bintree \<Rightarrow> bintree"
  tree_of :: "nat list \<Rightarrow> bintree"

primrec
  "tsorted Empty = True"
  "tsorted (Node n t1 t2) = (tsorted t1 \<and> tsorted t2 \<and> tge n t1 \<and> tle n t2)"

primrec
  "tge x Empty = True"
  "tge x (Node n t1 t2) = (n \<le> x \<and> tge x t1 \<and> tge x t2)"

primrec
  "tle x Empty = True"
  "tle x (Node n t1 t2) = (x \<le> n \<and> tle x t1 \<and> tle x t2)"

primrec
  "ins x Empty = Node x Empty Empty"
  "ins x (Node n t1 t2) = (if x \<le> n then Node n (ins x t1) t2 else Node n t1 (ins x t2))"

primrec
  "tree_of [] = Empty"
  "tree_of (x#xs) = ins x (tree_of xs)"


lemma "tge 5 (Node 3 (Node 2 Empty Empty) Empty)" by auto

lemma "\<not> tge 5 (Node 3 Empty (Node 7 Empty Empty))" by auto

lemma "\<not> tle 5 (Node 3 (Node 2 Empty Empty) Empty)" by auto

lemma "\<not> tle 5 (Node 3 Empty (Node 7 Empty Empty))" by auto

lemma "tle 3 (Node 3 Empty (Node 7 Empty Empty))" by auto

lemma "tsorted (Node 3 Empty (Node 7 Empty Empty))" by auto

lemma "tree_of [3,2] = Node 2 Empty (Node 3 Empty Empty)" by auto

lemma [simp]:
  "tge a (ins x t) = (x \<le> a \<and> tge a t)"
  apply (induct_tac t)
  apply auto
  done

lemma [simp]:
  "tle a (ins x t) = (a \<le> x \<and> tle a t)"
  apply (induct_tac t)
  apply auto
  done

lemma [simp]:
  "tsorted (ins x t) = tsorted t"
  apply (induct_tac t)
  apply auto
  done

theorem [simp]: "tsorted (tree_of xs)"
  apply (induct_tac xs)
  apply auto
  done

text {* 
  Auch bei diesem Algorithmus müssen wir noch zeigen, dass keine
  Elemente beim Sortieren verloren gehen (oder erfunden werden). Formulieren
  Sie analog zu den Listen eine Funktion @{term "tcount x b"}, die zählt, wie
  oft die Zahl @{term x} im Baum @{term b} vorkommt.
*} 
consts
  tcount :: "bintree => nat => nat"
primrec
  "tcount Empty y = 0"
  "tcount (Node x t1 t2) y = 
  (if x=y 
   then Suc (tcount t1 y + tcount t2 y) 
   else tcount t1 y + tcount t2 y)"

lemma [simp]:
  "tcount (ins x t) y =
  (if x=y then Suc (tcount t y) else tcount t y)"
  apply(induct_tac t)
  apply auto
  done

theorem "tcount (tree_of xs) x = count xs x"
  apply (induct_tac xs)
  apply auto
  done

text {*
  Die eigentliche Aufgabe war es, Listen zu sortieren. Bis jetzt haben
  wir lediglich einen Algorithmus, der Listen in geordnete Bäume
  transformiert. Definieren Sie deswegen eine Funktion @{text
  list_of}, die zu einen (geordneten) Baum eine (geordnete) Liste liefert. 
*}

consts
  ge      :: "nat \<Rightarrow> nat list \<Rightarrow> bool"
  list_of :: "bintree \<Rightarrow> nat list"

primrec
  "ge a [] = True"
  "ge a (x#xs) = (x \<le> a \<and> ge a xs)"

primrec
  "list_of Empty = []"
  "list_of (Node n t1 t2) = list_of t1 @ [n] @ list_of t2"


lemma [simp]:
  "le x (a@b) = (le x a \<and> le x b)"
  apply (induct_tac a)
  apply auto
  done

lemma [simp]:
  "ge x (a@b) = (ge x a \<and> ge x b)"
  apply (induct_tac a)
  apply auto
  done

lemma [simp]:
  "sorted (a@x#b) = (sorted a \<and> sorted b \<and> ge x a \<and> le x b)"
  apply (induct_tac a)
  apply auto
  done

lemma [simp]:
  "ge n (list_of t) = tge n t"
  apply (induct_tac t)
  apply auto
  done

lemma [simp]:
  "le n (list_of t) = tle n t"
  apply (induct_tac t)
  apply auto
  done
  
lemma [simp]:
  "sorted (list_of t) = tsorted t"
  apply (induct_tac t)
  apply auto
  done

theorem "sorted (list_of (tree_of xs))"
  apply auto
  done

lemma count_append [simp]:
  "count (a@b) n = count a n + count b n"
  apply (induct a)
  apply auto
  done

lemma [simp]:
  "count (list_of b) n = tcount b n"
  apply (induct b)
  apply auto
  done

theorem "count (list_of (tree_of xs)) n = count xs n"    
  apply (induct xs)
  apply auto
  done

end
