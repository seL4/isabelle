(*  Title:      HOL/Library/Suc_Notation.thy
    Author:     Manuel Eberl and Tobias Nipkow

Compact notation for nested \<open>Suc\<close> terms. Just notation. Use standard numerals for large numbers.
*)

theory Suc_Notation
imports Main
begin

text \<open>Nested \<open>Suc\<close> terms of depth \<open>2 \<le> n \<le> 9\<close> are abbreviated with new notations \<open>Suc\<^sup>n\<close>:\<close>

abbreviation (input) Suc2 where "Suc2 n \<equiv> Suc (Suc n)"
abbreviation (input) Suc3 where "Suc3 n \<equiv> Suc (Suc2 n)"
abbreviation (input) Suc4 where "Suc4 n \<equiv> Suc (Suc3 n)"
abbreviation (input) Suc5 where "Suc5 n \<equiv> Suc (Suc4 n)"
abbreviation (input) Suc6 where "Suc6 n \<equiv> Suc (Suc5 n)"
abbreviation (input) Suc7 where "Suc7 n \<equiv> Suc (Suc6 n)"
abbreviation (input) Suc8 where "Suc8 n \<equiv> Suc (Suc7 n)"
abbreviation (input) Suc9 where "Suc9 n \<equiv> Suc (Suc8 n)"

notation Suc2 ("Suc\<^sup>2")
notation Suc3 ("Suc\<^sup>3")
notation Suc4 ("Suc\<^sup>4")
notation Suc5 ("Suc\<^sup>5")
notation Suc6 ("Suc\<^sup>6")
notation Suc7 ("Suc\<^sup>7")
notation Suc8 ("Suc\<^sup>8")
notation Suc9 ("Suc\<^sup>9")

text \<open>Beyond 9, the syntax \<open>Suc\<^bsup>n\<^esup>\<close> kicks in:\<close>

syntax
  "_Suc_tower" :: "num_token \<Rightarrow> nat \<Rightarrow> nat"  ("Suc\<^bsup>_\<^esup>")

parse_translation \<open>
  let
    fun mk_sucs_aux 0 t = t
      | mk_sucs_aux n t = mk_sucs_aux (n - 1) (\<^const>\<open>Suc\<close> $ t)
    fun mk_sucs n = Abs("n", \<^typ>\<open>nat\<close>, mk_sucs_aux n (Bound 0))

    fun Suc_tr [Free (str, _)] = mk_sucs (the (Int.fromString str))

  in [(\<^syntax_const>\<open>_Suc_tower\<close>, K Suc_tr)] end
\<close>

print_translation \<open>
  let
    val digit_consts =
        [\<^const_syntax>\<open>Suc2\<close>, \<^const_syntax>\<open>Suc3\<close>, \<^const_syntax>\<open>Suc4\<close>, \<^const_syntax>\<open>Suc5\<close>,
         \<^const_syntax>\<open>Suc6\<close>, \<^const_syntax>\<open>Suc7\<close>, \<^const_syntax>\<open>Suc8\<close>, \<^const_syntax>\<open>Suc9\<close>]
    val num_token_T = Simple_Syntax.read_typ "num_token"
    val T = num_token_T --> HOLogic.natT --> HOLogic.natT
    fun mk_num_token n = Free (Int.toString n, num_token_T)
    fun dest_Suc_tower (Const (\<^const_syntax>\<open>Suc\<close>, _) $ t) acc =
          dest_Suc_tower t (acc + 1)
      | dest_Suc_tower t acc = (t, acc)

    fun Suc_tr' [t] =
      let
        val (t', n) = dest_Suc_tower t 1
      in
        if n > 9 then
          Const (\<^syntax_const>\<open>_Suc_tower\<close>, T) $ mk_num_token n $ t'
        else if n > 1 then
          Const (List.nth (digit_consts, n - 2), T) $ t'
        else
          raise Match
      end

  in [(\<^const_syntax>\<open>Suc\<close>, K Suc_tr')]
 end
\<close>

(* Tests

ML \<open>
local
  fun mk 0 = \<^term>\<open>x :: nat\<close>
    | mk n = \<^const>\<open>Suc\<close> $ mk (n - 1)
  val ctxt' = Variable.add_fixes_implicit @{term "x :: nat"} @{context}
in
  val _ =
    map_range (fn n => (n + 1, mk (n + 1))) 20
    |> map (fn (n, t) => 
         Pretty.block [Pretty.str (Int.toString n ^ ": "),
           Syntax.pretty_term ctxt' t] |> Pretty.writeln)
end
\<close>

(* test parsing *)
term "Suc x"
term "Suc\<^sup>2 x"
term "Suc\<^sup>3 x"
term "Suc\<^sup>4 x"
term "Suc\<^sup>5 x"
term "Suc\<^sup>6 x"
term "Suc\<^sup>7 x"
term "Suc\<^sup>8 x"
term "Suc\<^sup>9 x"

term "Suc\<^bsup>2\<^esup> x"
term "Suc\<^bsup>3\<^esup> x"
term "Suc\<^bsup>4\<^esup> x"
term "Suc\<^bsup>5\<^esup> x"
term "Suc\<^bsup>6\<^esup> x"
term "Suc\<^bsup>7\<^esup> x"
term "Suc\<^bsup>8\<^esup> x"
term "Suc\<^bsup>9\<^esup> x"
term "Suc\<^bsup>10\<^esup> x"
term "Suc\<^bsup>11\<^esup> x"
term "Suc\<^bsup>12\<^esup> x"
term "Suc\<^bsup>13\<^esup> x"
term "Suc\<^bsup>14\<^esup> x"
term "Suc\<^bsup>15\<^esup> x"
term "Suc\<^bsup>16\<^esup> x"
term "Suc\<^bsup>17\<^esup> x"
term "Suc\<^bsup>18\<^esup> x"
term "Suc\<^bsup>19\<^esup> x"
term "Suc\<^bsup>20\<^esup> x"

(* check that the notation really means the right thing *)
lemma "Suc\<^sup>2 n = n+2 \<and> Suc\<^sup>3 n = n+3 \<and> Suc\<^sup>4 n = n+4 \<and> Suc\<^sup>5 n = n+5
  \<and> Suc\<^sup>6 n = n+6 \<and> Suc\<^sup>7 n = n+7 \<and> Suc\<^sup>8 n = n+8 \<and> Suc\<^sup>9 n = n+9"
by simp

lemma "Suc\<^bsup>10\<^esup> n = n+10 \<and> Suc\<^bsup>11\<^esup> n = n+11 \<and> Suc\<^bsup>12\<^esup> n = n+12 \<and> Suc\<^bsup>13\<^esup> n = n+13
  \<and> Suc\<^bsup>14\<^esup> n = n+14 \<and> Suc\<^bsup>15\<^esup> n = n+15 \<and> Suc\<^bsup>16\<^esup> n = n+16 \<and> Suc\<^bsup>17\<^esup> n = n+17
  \<and> Suc\<^bsup>18\<^esup> n = n+18 \<and> Suc\<^bsup>19\<^esup> n = n+19 \<and> Suc\<^bsup>20\<^esup> n = n+20"
by simp

*)

end