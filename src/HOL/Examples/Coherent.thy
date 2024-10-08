(*  Title:      HOL/Examples/Coherent.thy
    Author:     Stefan Berghofer, TU Muenchen
    Author:     Marc Bezem, Institutt for Informatikk, Universitetet i Bergen 
*)

section \<open>Coherent Logic Problems\<close>

theory Coherent
imports Main
begin

subsection \<open>Equivalence of two versions of Pappus' Axiom\<close>

no_notation comp  (infixl \<open>o\<close> 55) and relcomp  (infixr \<open>O\<close> 75)

lemma p1p2:
  assumes "col a b c l \<and> col d e f m"
    and "col b f g n \<and> col c e g o"
    and "col b d h p \<and> col a e h q"
    and "col c d i r \<and> col a f i s"
    and "el n o \<Longrightarrow> goal"
    and "el p q \<Longrightarrow> goal"
    and "el s r \<Longrightarrow> goal"
    and "\<And>A. el A A \<Longrightarrow> pl g A \<Longrightarrow> pl h A \<Longrightarrow> pl i A \<Longrightarrow> goal"
    and "\<And>A B C D. col A B C D \<Longrightarrow> pl A D"
    and "\<And>A B C D. col A B C D \<Longrightarrow> pl B D"
    and "\<And>A B C D. col A B C D \<Longrightarrow> pl C D"
    and "\<And>A B. pl A B \<Longrightarrow> ep A A"
    and "\<And>A B. ep A B \<Longrightarrow> ep B A"
    and "\<And>A B C. ep A B \<Longrightarrow> ep B C \<Longrightarrow> ep A C"
    and "\<And>A B. pl A B \<Longrightarrow> el B B"
    and "\<And>A B. el A B \<Longrightarrow> el B A"
    and "\<And>A B C. el A B \<Longrightarrow> el B C \<Longrightarrow> el A C"
    and "\<And>A B C. ep A B \<Longrightarrow> pl B C \<Longrightarrow> pl A C"
    and "\<And>A B C. pl A B \<Longrightarrow> el B C \<Longrightarrow> pl A C"
    and "\<And>A B C D E F G H I J K L M N O P Q.
           col A B C D \<Longrightarrow> col E F G H \<Longrightarrow> col B G I J \<Longrightarrow> col C F I K \<Longrightarrow>
           col B E L M \<Longrightarrow> col A F L N \<Longrightarrow> col C E O P \<Longrightarrow> col A G O Q \<Longrightarrow>
           (\<exists> R. col I L O R) \<or> pl A H \<or> pl B H \<or> pl C H \<or> pl E D \<or> pl F D \<or> pl G D"
    and "\<And>A B C D. pl A B \<Longrightarrow> pl A C \<Longrightarrow> pl D B \<Longrightarrow> pl D C \<Longrightarrow> ep A D \<or> el B C"
    and "\<And>A B. ep A A \<Longrightarrow> ep B B \<Longrightarrow> \<exists>C. pl A C \<and> pl B C"
  shows goal using assms
  by coherent

lemma p2p1:
  assumes "col a b c l \<and> col d e f m"
    and "col b f g n \<and> col c e g o"
    and "col b d h p \<and> col a e h q"
    and "col c d i r \<and> col a f i s"
    and "pl a m \<Longrightarrow> goal"
    and "pl b m \<Longrightarrow> goal"
    and "pl c m \<Longrightarrow> goal"
    and "pl d l \<Longrightarrow> goal"
    and "pl e l \<Longrightarrow> goal"
    and "pl f l \<Longrightarrow> goal"
    and "\<And>A. pl g A \<Longrightarrow> pl h A \<Longrightarrow> pl i A \<Longrightarrow> goal"
    and "\<And>A B C D. col A B C D \<Longrightarrow> pl A D"
    and "\<And>A B C D. col A B C D \<Longrightarrow> pl B D"
    and "\<And>A B C D. col A B C D \<Longrightarrow> pl C D"
    and "\<And>A B. pl A B \<Longrightarrow> ep A A"
    and "\<And>A B. ep A B \<Longrightarrow> ep B A"
    and "\<And>A B C. ep A B \<Longrightarrow> ep B C \<Longrightarrow> ep A C"
    and "\<And>A B. pl A B \<Longrightarrow> el B B"
    and "\<And>A B. el A B \<Longrightarrow> el B A"
    and "\<And>A B C. el A B \<Longrightarrow> el B C \<Longrightarrow> el A C"
    and "\<And>A B C. ep A B \<Longrightarrow> pl B C \<Longrightarrow> pl A C"
    and "\<And>A B C. pl A B \<Longrightarrow> el B C \<Longrightarrow> pl A C"
    and "\<And>A B C D E F G H I J K L M N O P Q.
           col A B C J \<Longrightarrow> col D E F K \<Longrightarrow> col B F G L \<Longrightarrow> col C E G M \<Longrightarrow>
           col B D H N \<Longrightarrow> col A E H O \<Longrightarrow> col C D I P \<Longrightarrow> col A F I Q \<Longrightarrow>
           (\<exists> R. col G H I R) \<or> el L M \<or> el N O \<or> el P Q"
    and "\<And>A B C D. pl C A \<Longrightarrow> pl C B \<Longrightarrow> pl D A \<Longrightarrow> pl D B \<Longrightarrow> ep C D \<or> el A B"
    and "\<And>A B C. ep A A \<Longrightarrow> ep B B \<Longrightarrow> \<exists>C. pl A C \<and> pl B C"
  shows goal using assms
  by coherent


subsection \<open>Preservation of the Diamond Property under reflexive closure\<close>

lemma diamond:
  assumes "reflexive_rewrite a b" "reflexive_rewrite a c"
    and "\<And>A. reflexive_rewrite b A \<Longrightarrow> reflexive_rewrite c A \<Longrightarrow> goal"
    and "\<And>A. equalish A A" 
    and "\<And>A B. equalish A B \<Longrightarrow> equalish B A"
    and "\<And>A B C. equalish A B \<Longrightarrow> reflexive_rewrite B C \<Longrightarrow> reflexive_rewrite A C"
    and "\<And>A B. equalish A B \<Longrightarrow> reflexive_rewrite A B"
    and "\<And>A B. rewrite A B \<Longrightarrow> reflexive_rewrite A B"
    and "\<And>A B. reflexive_rewrite A B \<Longrightarrow> equalish A B \<or> rewrite A B"
    and "\<And>A B C. rewrite A B \<Longrightarrow> rewrite A C \<Longrightarrow> \<exists>D. rewrite B D \<and> rewrite C D"
  shows goal using assms
  by coherent

end
