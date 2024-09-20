(*  Author:     Ning Zhang and Christian Urban

Example theory involving Unicode characters (UTF-8 encoding) -- both
formal and informal ones.
*)

section \<open>A Chinese theory\<close>

theory Chinese imports Main begin

text\<open>数学家能把咖啡变成理论,如今中国的数学家也可
       以在伊莎贝拉的帮助下把茶变成理论.  

       伊莎贝拉-世界数学家的新宠,现今能识别中文,成为
       中国数学家理论推导的得力助手.

\<close>

datatype shuzi =
    One   (\<open>一\<close>)
  | Two   (\<open>二\<close>)
  | Three (\<open>三\<close>) 
  | Four  (\<open>四\<close>)
  | Five  (\<open>五\<close>)
  | Six   (\<open>六\<close>)
  | Seven (\<open>七\<close>)
  | Eight (\<open>八\<close>)
  | Nine  (\<open>九\<close>)
  | Ten   (\<open>十\<close>)

primrec translate :: "shuzi \<Rightarrow> nat" (\<open>|_|\<close> [100] 100) where
 "|一| = 1"
|"|二| = 2"
|"|三| = 3"
|"|四| = 4"
|"|五| = 5"
|"|六| = 6"
|"|七| = 7"
|"|八| = 8"
|"|九| = 9"
|"|十| = 10"

thm translate.simps

lemma "|四| + |六| = |十|"
  by simp 

end
