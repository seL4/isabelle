theory Array_Specs
imports Main
begin

text \<open>Array Specifications\<close>

locale Array =
fixes lookup :: "'ar \<Rightarrow> nat \<Rightarrow> 'a"
fixes update :: "nat \<Rightarrow> 'a \<Rightarrow> 'ar \<Rightarrow> 'ar"
fixes len :: "'ar \<Rightarrow> nat"
fixes array :: "'a list \<Rightarrow> 'ar"

fixes list :: "'ar \<Rightarrow> 'a list"
fixes invar :: "'ar \<Rightarrow> bool"

assumes lookup: "invar ar \<Longrightarrow> n < len ar \<Longrightarrow> lookup ar n = list ar ! n"
assumes update: "invar ar \<Longrightarrow> n < len ar \<Longrightarrow> list(update n x ar) = (list ar)[n:=x]"
assumes len_array: "invar ar \<Longrightarrow> len ar = length (list ar)"
assumes array: "list (array xs) = xs"

assumes invar_update: "invar ar \<Longrightarrow> n < len ar \<Longrightarrow> invar(update n x ar)"
assumes invar_array: "invar(array xs)"

locale Array_Flex = Array +
fixes add_lo :: "'a \<Rightarrow> 'ar \<Rightarrow> 'ar"
fixes del_lo :: "'ar \<Rightarrow> 'ar"
fixes add_hi :: "'a \<Rightarrow> 'ar \<Rightarrow> 'ar"
fixes del_hi :: "'ar \<Rightarrow> 'ar"

assumes add_lo: "invar ar \<Longrightarrow> list(add_lo a ar) = a # list ar"
assumes del_lo: "invar ar \<Longrightarrow> list(del_lo ar) = tl (list ar)"
assumes add_hi: "invar ar \<Longrightarrow> list(add_hi a ar) = list ar @ [a]"
assumes del_hi: "invar ar \<Longrightarrow> list(del_hi ar) = butlast (list ar)"

assumes invar_add_lo: "invar ar \<Longrightarrow> invar (add_lo a ar)"
assumes invar_del_lo: "invar ar \<Longrightarrow> invar (del_lo ar)"
assumes invar_add_hi: "invar ar \<Longrightarrow> invar (add_hi a ar)"
assumes invar_del_hi: "invar ar \<Longrightarrow> invar (del_hi ar)"

end