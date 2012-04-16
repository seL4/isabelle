(*  Title:      HOL/ex/Coherent.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Marc Bezem, Institutt for Informatikk, Universitetet i Bergen 
*)

header {* Coherent Logic Problems *}

theory Coherent
imports Main
begin

subsection {* Equivalence of two versions of Pappus' Axiom *}

no_notation
  comp (infixl "o" 55) and
  relcomp (infixr "O" 75)

lemma p1p2:
  assumes
  "col a b c l \<and> col d e f m"
  "col b f g n \<and> col c e g o"
  "col b d h p \<and> col a e h q"
  "col c d i r \<and> col a f i s"
  "el n o \<Longrightarrow> goal"
  "el p q \<Longrightarrow> goal"
  "el s r \<Longrightarrow> goal"
  "\<And>A. el A A \<Longrightarrow> pl g A \<Longrightarrow> pl h A \<Longrightarrow> pl i A \<Longrightarrow> goal"
  "\<And>A B C D. col A B C D \<Longrightarrow> pl A D"
  "\<And>A B C D. col A B C D \<Longrightarrow> pl B D"
  "\<And>A B C D. col A B C D \<Longrightarrow> pl C D"
  "\<And>A B. pl A B \<Longrightarrow> ep A A"
  "\<And>A B. ep A B \<Longrightarrow> ep B A"
  "\<And>A B C. ep A B \<Longrightarrow> ep B C \<Longrightarrow> ep A C"
  "\<And>A B. pl A B \<Longrightarrow> el B B"
  "\<And>A B. el A B \<Longrightarrow> el B A"
  "\<And>A B C. el A B \<Longrightarrow> el B C \<Longrightarrow> el A C"
  "\<And>A B C. ep A B \<Longrightarrow> pl B C \<Longrightarrow> pl A C"
  "\<And>A B C. pl A B \<Longrightarrow> el B C \<Longrightarrow> pl A C"
  "\<And>A B C D E F G H I J K L M N O P Q.
     col A B C D \<Longrightarrow> col E F G H \<Longrightarrow> col B G I J \<Longrightarrow> col C F I K \<Longrightarrow>
     col B E L M \<Longrightarrow> col A F L N \<Longrightarrow> col C E O P \<Longrightarrow> col A G O Q \<Longrightarrow>
     (\<exists> R. col I L O R) \<or> pl A H \<or> pl B H \<or> pl C H \<or> pl E D \<or> pl F D \<or> pl G D"
  "\<And>A B C D. pl A B \<Longrightarrow> pl A C \<Longrightarrow> pl D B \<Longrightarrow> pl D C \<Longrightarrow> ep A D \<or> el B C"
  "\<And>A B. ep A A \<Longrightarrow> ep B B \<Longrightarrow> \<exists>C. pl A C \<and> pl B C"
  shows goal using assms
  by coherent

lemma p2p1:
  assumes
  "col a b c l \<and> col d e f m"
  "col b f g n \<and> col c e g o"
  "col b d h p \<and> col a e h q"
  "col c d i r \<and> col a f i s"
  "pl a m \<Longrightarrow> goal"
  "pl b m \<Longrightarrow> goal"
  "pl c m \<Longrightarrow> goal"
  "pl d l \<Longrightarrow> goal"
  "pl e l \<Longrightarrow> goal"
  "pl f l \<Longrightarrow> goal"
  "\<And>A. pl g A \<Longrightarrow> pl h A \<Longrightarrow> pl i A \<Longrightarrow> goal"
  "\<And>A B C D. col A B C D \<Longrightarrow> pl A D"
  "\<And>A B C D. col A B C D \<Longrightarrow> pl B D"
  "\<And>A B C D. col A B C D \<Longrightarrow> pl C D"
  "\<And>A B. pl A B \<Longrightarrow> ep A A"
  "\<And>A B. ep A B \<Longrightarrow> ep B A"
  "\<And>A B C. ep A B \<Longrightarrow> ep B C \<Longrightarrow> ep A C"
  "\<And>A B. pl A B \<Longrightarrow> el B B"
  "\<And>A B. el A B \<Longrightarrow> el B A"
  "\<And>A B C. el A B \<Longrightarrow> el B C \<Longrightarrow> el A C"
  "\<And>A B C. ep A B \<Longrightarrow> pl B C \<Longrightarrow> pl A C"
  "\<And>A B C. pl A B \<Longrightarrow> el B C \<Longrightarrow> pl A C"
  "\<And>A B C D E F G H I J K L M N O P Q.
     col A B C J \<Longrightarrow> col D E F K \<Longrightarrow> col B F G L \<Longrightarrow> col C E G M \<Longrightarrow>
     col B D H N \<Longrightarrow> col A E H O \<Longrightarrow> col C D I P \<Longrightarrow> col A F I Q \<Longrightarrow>
     (\<exists> R. col G H I R) \<or> el L M \<or> el N O \<or> el P Q"
  "\<And>A B C D. pl C A \<Longrightarrow> pl C B \<Longrightarrow> pl D A \<Longrightarrow> pl D B \<Longrightarrow> ep C D \<or> el A B"
  "\<And>A B C. ep A A \<Longrightarrow> ep B B \<Longrightarrow> \<exists>C. pl A C \<and> pl B C"
  shows goal using assms
  by coherent


subsection {* Preservation of the Diamond Property under reflexive closure *}

lemma diamond:
  assumes
  "reflexive_rewrite a b" "reflexive_rewrite a c"
  "\<And>A. reflexive_rewrite b A \<Longrightarrow> reflexive_rewrite c A \<Longrightarrow> goal"
  "\<And>A. equalish A A" 
  "\<And>A B. equalish A B \<Longrightarrow> equalish B A"
  "\<And>A B C. equalish A B \<Longrightarrow> reflexive_rewrite B C \<Longrightarrow> reflexive_rewrite A C"
  "\<And>A B. equalish A B \<Longrightarrow> reflexive_rewrite A B"
  "\<And>A B. rewrite A B \<Longrightarrow> reflexive_rewrite A B"
  "\<And>A B. reflexive_rewrite A B \<Longrightarrow> equalish A B \<or> rewrite A B"
  "\<And>A B C. rewrite A B \<Longrightarrow> rewrite A C \<Longrightarrow> \<exists>D. rewrite B D \<and> rewrite C D"
  shows goal using assms
  by coherent

end
