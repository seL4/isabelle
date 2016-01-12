theory All_Symmetric
imports Message
begin

text \<open>All keys are symmetric\<close>

overloading all_symmetric \<equiv> all_symmetric
begin
  definition "all_symmetric \<equiv> True"
end

lemma isSym_keys: "K \<in> symKeys"
  by (simp add: symKeys_def all_symmetric_def invKey_symmetric) 

end
