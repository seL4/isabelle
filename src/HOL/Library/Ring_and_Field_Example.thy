
header {* \title{}\subsection{Example: The ordered ring of integers} *}

theory Ring_and_Field_Example = Ring_and_Field:

instance int :: ordered_ring
proof
  fix i j k :: int
  show "(i + j) + k = i + (j + k)" by simp
  show "i + j = j + i" by simp
  show "0 + i = i" by simp
  show "- i + i = 0" by simp
  show "i - j = i + (-j)" by simp
  show "(i * j) * k = i * (j * k)" by simp
  show "i * j = j * i" by simp
  show "1 * i = i" by simp
  show "(i + j) * k = i * k + j * k" by (simp add: int_distrib)
  show "i \<le> j ==> k + i \<le> k + j" by simp
  show "i < j ==> 0 < k ==> k * i < k * j" by (simp add: zmult_zless_mono2)
  show "\<bar>i\<bar> = (if i < 0 then -i else i)" by (simp only: zabs_def)
qed

end
