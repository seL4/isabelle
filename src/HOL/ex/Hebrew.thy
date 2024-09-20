(*  Author:     Makarius

Example theory involving Unicode characters (UTF-8 encoding) -- both
formal and informal ones.
*)

section \<open>A Hebrew theory\<close>

theory Hebrew
imports Main
begin

text \<open>
  \<^bold>\<open>Warning:\<close> Bidirectional Unicode text may confuse display in browsers, editors, etc.!
\<close>

subsection \<open>The Hebrew Alef-Bet (א-ב).\<close>

datatype alef_bet =
    Alef    (\<open>א\<close>)
  | Bet     (\<open>ב\<close>)
  | Gimel   (\<open>ג\<close>)
  | Dalet   (\<open>ד\<close>)
  | He      (\<open>ה\<close>)
  | Vav     (\<open>ו\<close>)
  | Zayin   (\<open>ז\<close>)
  | Het     (\<open>ח\<close>)
  | Tet     (\<open>ט\<close>)
  | Yod     (\<open>י\<close>)
  | Kaf     (\<open>כ\<close>)
  | Lamed   (\<open>ל\<close>)
  | Mem     (\<open>מ\<close>)
  | Nun     (\<open>נ\<close>)
  | Samekh  (\<open>ס\<close>)
  | Ayin    (\<open>ע\<close>)
  | Pe      (\<open>פ\<close>)
  | Tsadi   (\<open>צ\<close>)
  | Qof     (\<open>ק\<close>)
  | Resh    (\<open>ר\<close>)
  | Shin    (\<open>ש\<close>)
  | Tav     (\<open>ת\<close>)

thm alef_bet.induct


subsection \<open>Interpreting Hebrew letters as numbers.\<close>

primrec mispar :: "alef_bet \<Rightarrow> nat"
where
  "mispar א = 1"
| "mispar ב = 2"
| "mispar ג = 3"
| "mispar ד = 4"
| "mispar ה = 5"
| "mispar ו = 6"
| "mispar ז = 7"
| "mispar ח = 8"
| "mispar ט = 9"
| "mispar י = 10"
| "mispar כ = 20"
| "mispar ל = 30"
| "mispar מ = 40"
| "mispar נ = 50"
| "mispar ס = 60"
| "mispar ע = 70"
| "mispar פ = 80"
| "mispar צ = 90"
| "mispar ק = 100"
| "mispar ר = 200"
| "mispar ש = 300"
| "mispar ת = 400"

thm mispar.simps

lemma "mispar ק + mispar ל + mispar ה = 135"
  by simp

end
