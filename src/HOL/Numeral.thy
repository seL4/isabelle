(*  Title:      HOL/Numeral.thy
    ID:         $Id$
    Author:     Larry Paulson and Markus Wenzel

Generic numerals represented as twos-complement bit strings.
*)

theory Numeral = Datatype
files "Tools/numeral_syntax.ML":

text{* The file @{text numeral_syntax.ML} hides the constructors Pls and Min.
   Only qualified access bin.Pls and bin.Min is allowed.
   We do not hide Bit because we need the BIT infix syntax.*}

text{*A number can have multiple representations, namely leading Falses with
sign @{term Pls} and leading Trues with sign @{term Min}.
See @{text "ZF/Integ/twos-compl.ML"}, function @{text int_of_binary},
for the numerical interpretation.

The representation expects that @{text "(m mod 2)"} is 0 or 1,
even if m is negative;
For instance, @{text "-5 div 2 = -3"} and @{text "-5 mod 2 = 1"}; thus
@{text "-5 = (-3)*2 + 1"}.
*}

datatype
  bin = Pls  --{*Plus: Stands for an infinite string of leading Falses*}
      | Min --{*Minus: Stands for an infinite string of leading Trues*}
      | Bit bin bool    (infixl "BIT" 90)

axclass
  number < type  -- {* for numeric types: nat, int, real, \dots *}

consts
  number_of :: "bin => 'a::number"

syntax
  "_Numeral" :: "num_const => 'a"    ("_")
  Numeral0 :: 'a
  Numeral1 :: 'a

translations
  "Numeral0" == "number_of bin.Pls"
  "Numeral1" == "number_of (bin.Pls BIT True)"


setup NumeralSyntax.setup

syntax (xsymbols)
  "_square" :: "'a => 'a"  ("(_\<twosuperior>)" [1000] 999)
syntax (HTML output)
  "_square" :: "'a => 'a"  ("(_\<twosuperior>)" [1000] 999)
syntax (output)
  "_square" :: "'a => 'a"  ("(_ ^/ 2)" [81] 80)
translations
  "x\<twosuperior>" == "x^2"
  "x\<twosuperior>" <= "x^(2::nat)"


lemma Let_number_of [simp]: "Let (number_of v) f == f (number_of v)"
  -- {* Unfold all @{text let}s involving constants *}
  by (simp add: Let_def)

lemma Let_0 [simp]: "Let 0 f == f 0"
  by (simp add: Let_def)

lemma Let_1 [simp]: "Let 1 f == f 1"
  by (simp add: Let_def)


consts
  NCons     :: "[bin,bool]=>bin"
  bin_succ  :: "bin=>bin"
  bin_pred  :: "bin=>bin"
  bin_minus :: "bin=>bin"
  bin_add   :: "[bin,bin]=>bin"
  bin_mult  :: "[bin,bin]=>bin"

text{*@{term NCons} inserts a bit, suppressing leading 0s and 1s*}
primrec
  NCons_Pls:  "NCons bin.Pls b = (if b then (bin.Pls BIT b) else bin.Pls)"
  NCons_Min:  "NCons bin.Min b = (if b then bin.Min else (bin.Min BIT b))"
  NCons_BIT:  "NCons (w BIT x) b = (w BIT x) BIT b"


primrec
  bin_succ_Pls: "bin_succ bin.Pls = bin.Pls BIT True"
  bin_succ_Min: "bin_succ bin.Min = bin.Pls"
  bin_succ_BIT: "bin_succ(w BIT x) =
  	            (if x then bin_succ w BIT False
	                  else NCons w True)"

primrec
  bin_pred_Pls: "bin_pred bin.Pls = bin.Min"
  bin_pred_Min: "bin_pred bin.Min = bin.Min BIT False"
  bin_pred_BIT: "bin_pred(w BIT x) =
	            (if x then NCons w False
		          else (bin_pred w) BIT True)"

primrec
  bin_minus_Pls: "bin_minus bin.Pls = bin.Pls"
  bin_minus_Min: "bin_minus bin.Min = bin.Pls BIT True"
  bin_minus_BIT: "bin_minus(w BIT x) =
	             (if x then bin_pred (NCons (bin_minus w) False)
		           else bin_minus w BIT False)"

primrec
  bin_add_Pls: "bin_add bin.Pls w = w"
  bin_add_Min: "bin_add bin.Min w = bin_pred w"
  bin_add_BIT:
    "bin_add (v BIT x) w =
       (case w of bin.Pls => v BIT x
                | bin.Min => bin_pred (v BIT x)
                | (w BIT y) =>
      	            NCons (bin_add v (if (x & y) then bin_succ w else w))
	                  (x~=y))"

primrec
  bin_mult_Pls: "bin_mult bin.Pls w = bin.Pls"
  bin_mult_Min: "bin_mult bin.Min w = bin_minus w"
  bin_mult_BIT: "bin_mult (v BIT x) w =
	            (if x then (bin_add (NCons (bin_mult v w) False) w)
	                  else (NCons (bin_mult v w) False))"


subsection{*Extra rules for @{term bin_succ}, @{term bin_pred}, 
  @{term bin_add} and @{term bin_mult}*}

lemma NCons_Pls_0: "NCons bin.Pls False = bin.Pls"
by simp

lemma NCons_Pls_1: "NCons bin.Pls True = bin.Pls BIT True"
by simp

lemma NCons_Min_0: "NCons bin.Min False = bin.Min BIT False"
by simp

lemma NCons_Min_1: "NCons bin.Min True = bin.Min"
by simp

lemma bin_succ_1: "bin_succ(w BIT True) = (bin_succ w) BIT False"
by simp

lemma bin_succ_0: "bin_succ(w BIT False) =  NCons w True"
by simp

lemma bin_pred_1: "bin_pred(w BIT True) = NCons w False"
by simp

lemma bin_pred_0: "bin_pred(w BIT False) = (bin_pred w) BIT True"
by simp

lemma bin_minus_1: "bin_minus(w BIT True) = bin_pred (NCons (bin_minus w) False)"
by simp

lemma bin_minus_0: "bin_minus(w BIT False) = (bin_minus w) BIT False"
by simp


subsection{*Binary Addition and Multiplication:
         @{term bin_add} and @{term bin_mult}*}

lemma bin_add_BIT_11:
     "bin_add (v BIT True) (w BIT True) =
     NCons (bin_add v (bin_succ w)) False"
by simp

lemma bin_add_BIT_10:
     "bin_add (v BIT True) (w BIT False) = NCons (bin_add v w) True"
by simp

lemma bin_add_BIT_0:
     "bin_add (v BIT False) (w BIT y) = NCons (bin_add v w) y"
by auto

lemma bin_add_Pls_right: "bin_add w bin.Pls = w"
by (induct_tac "w", auto)

lemma bin_add_Min_right: "bin_add w bin.Min = bin_pred w"
by (induct_tac "w", auto)

lemma bin_add_BIT_BIT:
     "bin_add (v BIT x) (w BIT y) =
     NCons(bin_add v (if x & y then (bin_succ w) else w)) (x~= y)"
by simp

lemma bin_mult_1:
     "bin_mult (v BIT True) w = bin_add (NCons (bin_mult v w) False) w"
by simp

lemma bin_mult_0: "bin_mult (v BIT False) w = NCons (bin_mult v w) False"
by simp


end
