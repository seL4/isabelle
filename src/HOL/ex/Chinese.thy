(* -*- coding: utf-8 -*-
    ID:         $Id$
    Author:     Ning Zhang and Christian Urban

Example theory involving Unicode characters (UTF-8 encoding) -- both
formal and informal ones.
*)

header {* A Chinese theory *}

theory Chinese = Main:

text{* 数学家能把咖啡变成理论,如今中国的数学家也可
       以在伊莎贝拉的帮助下把茶变成理论.  

       伊莎贝拉-世界数学家的新宠,现今能识别中文,成为
       中国数学家理论推导的得力助手.

    *}

datatype shuzi =
    One   ("一")
  | Two   ("二")
  | Three ("三") 
  | Four  ("四")
  | Five  ("五")
  | Six   ("六")
  | Seven ("七")
  | Eight ("八")
  | Nine  ("九")
  | Ten   ("十")

consts
  translate :: "shuzi \<Rightarrow> nat" ("|_|" [100] 100)

primrec
 "|一| = 1"
 "|二| = 2"
 "|三| = 3"
 "|四| = 4"
 "|五| = 5"
 "|六| = 6"
 "|七| = 7"
 "|八| = 8"
 "|九| = 9"
 "|十| = 10"

thm translate.simps

lemma "|四| + |六| = |十|"
  by simp 

end
