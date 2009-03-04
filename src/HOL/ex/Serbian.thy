(* -*- coding: utf-8 -*- :encoding=utf-8:  
    Author:     Filip Maric

Example theory involving Unicode characters (UTF-8 encoding) -- 
Conversion between Serbian cyrillic and latin letters (српска ћирилица и латиница)
*)

header {* A Serbian theory *}

theory Serbian
imports Main
begin

text{* Serbian cyrillic letters *}
datatype azbuka =
  azbA   ("А")
| azbB   ("Б")
| azbV   ("В")
| azbG   ("Г")
| azbD   ("Д")
| azbDj  ("Ђ")
| azbE   ("Е")
| azbZv  ("Ж")
| azbZ   ("З")
| azbI   ("И")
| azbJ   ("Ј")
| azbK   ("К")
| azbL   ("Л")
| azbLj  ("Љ")
| azbM   ("М")
| azbN   ("Н")
| azbNj  ("Њ")
| azbO   ("О")
| azbP   ("П")
| azbR   ("Р")
| azbS   ("С")
| azbT   ("Т")
| azbC'  ("Ћ")
| azbU   ("У")
| azbF   ("Ф")
| azbH   ("Х")
| azbC   ("Ц")
| azbCv  ("Ч")
| azbDzv ("Џ")
| azbSv  ("Ш")
| azbSpc

thm azbuka.induct

text{* Serbian latin letters *}
datatype abeceda =
  abcA   ("A")
| abcB   ("B")
| abcC   ("C")
| abcCv  ("Č")
| abcC'  ("Ć")
| abcD   ("D")
| abcE   ("E")
| abcF   ("F")
| abcG   ("G")
| abcH   ("H")
| abcI   ("I")
| abcJ   ("J")
| abcK   ("K")
| abcL   ("L")
| abcM   ("M")
| abcN   ("N")
| abcO   ("O")
| abcP   ("P")
| abcR   ("R")
| abcS   ("S")
| abcSv  ("Š")
| abcT   ("T")
| abcU   ("U")
| abcV   ("V")
| abcZ   ("Z")
| abcvZ  ("Ž")
| abcSpc

thm abeceda.induct


text{* Conversion from cyrillic to latin - 
       this conversion is valid in all cases *}
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

text{* The conversion from latin to cyrillic - 
       this conversion is valid in most cases but there are some exceptions *}
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
           abc2azb_aux x1 # abc2azb (x2 # xs)
       )"

value "abc2azb [D, O, B, A, R, abcSpc, D, A, N, abcSpc, S, V, I, M, A]"
value "abc2azb [L, J, U, B, I, Č, I, C, A, abcSpc, N, A, abcSpc, P, O, L, J, U]"

text{* Here are some invalid conversions *}
lemma "abc2azb [N, A, D, Ž, I, V, E, T, I] = [Н, А, Џ, И, В, Е, Т, И]"
  by simp
text{* but it should be: НАДЖИВЕТИ *}
lemma "abc2azb [I, N, J, E, K, C, I, J, A] = [И, Њ, Е, К, Ц, И, Ј, А]"
  by simp
text{* but it should be: ИНЈЕКЦИЈА *}

text{* The conversion fails for all cyrrilic words that contain НЈ ЛЈ ДЈ ДЖ *}


text{* Idempotency in one direction *}
lemma [simp]: "azb2abc_aux (abc2azb_aux x) = [x]"
  by (cases x) auto

lemma [simp]: "abc2azb (Ž # xs) = Ж # abc2azb xs"
  by (cases xs) auto

lemma [simp]: "abc2azb (J # xs) = Ј # abc2azb xs"
  by (cases xs) auto

theorem "azb2abc (abc2azb x) = x"
proof (induct x)
  case (Cons x1 xs)
  thus ?case
  proof (cases xs)
    case (Cons x2 xss)
    thus ?thesis
      using `azb2abc (abc2azb xs) = xs`
      by auto
  qed simp
qed simp

text{* Idempotency in the other direction does not hold *}
lemma "abc2azb (azb2abc [И, Н, Ј, Е, К, Ц, И, Ј, А]) \<noteq> [И, Н, Ј, Е, К, Ц, И, Ј, А]"
  by simp
text{* It fails for all cyrrilic words that contain НЈ ЛЈ ДЈ ДЖ *}

end
