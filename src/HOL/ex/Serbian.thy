(*  Author:     Filip Maric

Example theory involving Unicode characters (UTF-8 encoding) -- 
Conversion between Serbian cyrillic and latin letters (српска ћирилица и латиница).
*)

section \<open>A Serbian theory\<close>

theory Serbian
  imports Main
begin

text \<open>Serbian cyrillic letters.\<close>
datatype azbuka =
  azbA   (\<open>А\<close>)
| azbB   (\<open>Б\<close>)
| azbV   (\<open>В\<close>)
| azbG   (\<open>Г\<close>)
| azbD   (\<open>Д\<close>)
| azbDj  (\<open>Ђ\<close>)
| azbE   (\<open>Е\<close>)
| azbZv  (\<open>Ж\<close>)
| azbZ   (\<open>З\<close>)
| azbI   (\<open>И\<close>)
| azbJ   (\<open>Ј\<close>)
| azbK   (\<open>К\<close>)
| azbL   (\<open>Л\<close>)
| azbLj  (\<open>Љ\<close>)
| azbM   (\<open>М\<close>)
| azbN   (\<open>Н\<close>)
| azbNj  (\<open>Њ\<close>)
| azbO   (\<open>О\<close>)
| azbP   (\<open>П\<close>)
| azbR   (\<open>Р\<close>)
| azbS   (\<open>С\<close>)
| azbT   (\<open>Т\<close>)
| azbC'  (\<open>Ћ\<close>)
| azbU   (\<open>У\<close>)
| azbF   (\<open>Ф\<close>)
| azbH   (\<open>Х\<close>)
| azbC   (\<open>Ц\<close>)
| azbCv  (\<open>Ч\<close>)
| azbDzv (\<open>Џ\<close>)
| azbSv  (\<open>Ш\<close>)
| azbSpc

thm azbuka.induct

text \<open>Serbian latin letters.\<close>
datatype abeceda =
  abcA   (\<open>A\<close>)
| abcB   (\<open>B\<close>)
| abcC   (\<open>C\<close>)
| abcCv  (\<open>Č\<close>)
| abcC'  (\<open>Ć\<close>)
| abcD   (\<open>D\<close>)
| abcE   (\<open>E\<close>)
| abcF   (\<open>F\<close>)
| abcG   (\<open>G\<close>)
| abcH   (\<open>H\<close>)
| abcI   (\<open>I\<close>)
| abcJ   (\<open>J\<close>)
| abcK   (\<open>K\<close>)
| abcL   (\<open>L\<close>)
| abcM   (\<open>M\<close>)
| abcN   (\<open>N\<close>)
| abcO   (\<open>O\<close>)
| abcP   (\<open>P\<close>)
| abcR   (\<open>R\<close>)
| abcS   (\<open>S\<close>)
| abcSv  (\<open>Š\<close>)
| abcT   (\<open>T\<close>)
| abcU   (\<open>U\<close>)
| abcV   (\<open>V\<close>)
| abcZ   (\<open>Z\<close>)
| abcvZ  (\<open>Ž\<close>)
| abcSpc

thm abeceda.induct


text \<open>Conversion from cyrillic to latin -- this conversion is valid in all cases.\<close>
primrec azb2abc_aux :: "azbuka \<Rightarrow> abeceda list"
where
  "azb2abc_aux А = [A]"
| "azb2abc_aux Б = [B]"
| "azb2abc_aux В = [V]"
| "azb2abc_aux Г = [G]"
| "azb2abc_aux Д = [D]"
| "azb2abc_aux Ђ = [D, J]"
| "azb2abc_aux Е = [E]"
| "azb2abc_aux Ж = [Ž]"
| "azb2abc_aux З = [Z]"
| "azb2abc_aux И = [I]"
| "azb2abc_aux Ј = [J]"
| "azb2abc_aux К = [K]"
| "azb2abc_aux Л = [L]"
| "azb2abc_aux Љ = [L, J]"
| "azb2abc_aux М = [M]"
| "azb2abc_aux Н = [N]"
| "azb2abc_aux Њ = [N, J]"
| "azb2abc_aux О = [O]"
| "azb2abc_aux П = [P]"
| "azb2abc_aux Р = [R]"
| "azb2abc_aux С = [S]"
| "azb2abc_aux Т = [T]"
| "azb2abc_aux Ћ = [Ć]"
| "azb2abc_aux У = [U]"
| "azb2abc_aux Ф = [F]"
| "azb2abc_aux Х = [H]"
| "azb2abc_aux Ц = [C]"
| "azb2abc_aux Ч = [Č]"
| "azb2abc_aux Џ = [D, Ž]"
| "azb2abc_aux Ш = [Š]"
| "azb2abc_aux azbSpc = [abcSpc]"

primrec azb2abc :: "azbuka list \<Rightarrow> abeceda list"
where
  "azb2abc [] = []"
| "azb2abc (x # xs) = azb2abc_aux x @ azb2abc xs"

value "azb2abc [Д, О, Б, А, Р, azbSpc, Д, А, Н, azbSpc, С, В, И, М, А]"
value "azb2abc [Љ, У, Б, И, Ч, И, Ц, А, azbSpc, Н, А, azbSpc, П, О, Љ, У]"

text \<open>
  The conversion from latin to cyrillic --
  this conversion is valid in most cases but there are some exceptions.\<close>
primrec abc2azb_aux :: "abeceda \<Rightarrow> azbuka"
where
   "abc2azb_aux A = А"
|  "abc2azb_aux B = Б"
|  "abc2azb_aux C = Ц"
|  "abc2azb_aux Č = Ч"
|  "abc2azb_aux Ć = Ћ"
|  "abc2azb_aux D = Д"
|  "abc2azb_aux E = Е"
|  "abc2azb_aux F = Ф"
|  "abc2azb_aux G = Г"
|  "abc2azb_aux H = Х"
|  "abc2azb_aux I = И"
|  "abc2azb_aux J = Ј"
|  "abc2azb_aux K = К"
|  "abc2azb_aux L = Л"
|  "abc2azb_aux M = М"
|  "abc2azb_aux N = Н"
|  "abc2azb_aux O = О"
|  "abc2azb_aux P = П"
|  "abc2azb_aux R = Р"
|  "abc2azb_aux S = С"
|  "abc2azb_aux Š = Ш"
|  "abc2azb_aux T = Т"
|  "abc2azb_aux U = У"
|  "abc2azb_aux V = В"
|  "abc2azb_aux Z = З"
|  "abc2azb_aux Ž = Ж"
|  "abc2azb_aux abcSpc = azbSpc"

fun abc2azb :: "abeceda list \<Rightarrow> azbuka list"
where
  "abc2azb [] = []"
| "abc2azb [x] = [abc2azb_aux x]"
| "abc2azb (x1 # x2 # xs) = 
    (if x1 = D \<and> x2 = J then
        Ђ # abc2azb xs
     else if x1 = L \<and> x2 = J then
        Љ # abc2azb xs
     else if x1 = N \<and> x2 = J then
        Њ # abc2azb xs
     else if x1 = D \<and> x2 = Ž then
        Џ # abc2azb xs
     else
        abc2azb_aux x1 # abc2azb (x2 # xs))"

value "abc2azb [D, O, B, A, R, abcSpc, D, A, N, abcSpc, S, V, I, M, A]"
value "abc2azb [L, J, U, B, I, Č, I, C, A, abcSpc, N, A, abcSpc, P, O, L, J, U]"

text \<open>Here are some invalid conversions.\<close>
lemma "abc2azb [N, A, D, Ž, I, V, E, T, I] = [Н, А, Џ, И, В, Е, Т, И]"
  by simp
text \<open>but it should be: НАДЖИВЕТИ\<close>
lemma "abc2azb [I, N, J, E, K, C, I, J, A] = [И, Њ, Е, К, Ц, И, Ј, А]"
  by simp
text \<open>but it should be: ИНЈЕКЦИЈА\<close>

text \<open>The conversion fails for all cyrillic words that contain НЈ ЛЈ ДЈ ДЖ.\<close>


text \<open>Idempotency in one direction.\<close>
lemma [simp]: "azb2abc_aux (abc2azb_aux x) = [x]"
  by (cases x) auto

lemma [simp]: "abc2azb (Ž # xs) = Ж # abc2azb xs"
  by (cases xs) auto

lemma [simp]: "abc2azb (J # xs) = Ј # abc2azb xs"
  by (cases xs) auto

theorem "azb2abc (abc2azb x) = x"
proof (induct x)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case
  proof (cases xs)
    case Nil
    then show ?thesis by simp
  next
    case (Cons x2 xss)
    with \<open>azb2abc (abc2azb xs) = xs\<close> show ?thesis
      by auto
  qed
qed

text \<open>Idempotency in the other direction does not hold.\<close>
lemma "abc2azb (azb2abc [И, Н, Ј, Е, К, Ц, И, Ј, А]) \<noteq> [И, Н, Ј, Е, К, Ц, И, Ј, А]"
  by simp
text \<open>It fails for all cyrillic words that contain НЈ ЛЈ ДЈ ДЖ.\<close>

end
