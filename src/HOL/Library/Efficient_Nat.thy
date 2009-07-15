(*  Title:      HOL/Library/Efficient_Nat.thy
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen
*)

header {* Implementation of natural numbers by target-language integers *}

theory Efficient_Nat
imports Code_Integer Main
begin

text {*
  When generating code for functions on natural numbers, the
  canonical representation using @{term "0::nat"} and
  @{term "Suc"} is unsuitable for computations involving large
  numbers.  The efficiency of the generated code can be improved
  drastically by implementing natural numbers by target-language
  integers.  To do this, just include this theory.
*}

subsection {* Basic arithmetic *}

text {*
  Most standard arithmetic functions on natural numbers are implemented
  using their counterparts on the integers:
*}

code_datatype number_nat_inst.number_of_nat

lemma zero_nat_code [code, code_unfold_post]:
  "0 = (Numeral0 :: nat)"
  by simp

lemma one_nat_code [code, code_unfold_post]:
  "1 = (Numeral1 :: nat)"
  by simp

lemma Suc_code [code]:
  "Suc n = n + 1"
  by simp

lemma plus_nat_code [code]:
  "n + m = nat (of_nat n + of_nat m)"
  by simp

lemma minus_nat_code [code]:
  "n - m = nat (of_nat n - of_nat m)"
  by simp

lemma times_nat_code [code]:
  "n * m = nat (of_nat n * of_nat m)"
  unfolding of_nat_mult [symmetric] by simp

text {* Specialized @{term "op div \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"} 
  and @{term "op mod \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"} operations. *}

definition divmod_aux ::  "nat \<Rightarrow> nat \<Rightarrow> nat \<times> nat" where
  [code del]: "divmod_aux = Divides.divmod"

lemma [code]:
  "Divides.divmod n m = (if m = 0 then (0, n) else divmod_aux n m)"
  unfolding divmod_aux_def divmod_div_mod by simp

lemma divmod_aux_code [code]:
  "divmod_aux n m = (nat (of_nat n div of_nat m), nat (of_nat n mod of_nat m))"
  unfolding divmod_aux_def divmod_div_mod zdiv_int [symmetric] zmod_int [symmetric] by simp

lemma eq_nat_code [code]:
  "eq_class.eq n m \<longleftrightarrow> eq_class.eq (of_nat n \<Colon> int) (of_nat m)"
  by (simp add: eq)

lemma eq_nat_refl [code nbe]:
  "eq_class.eq (n::nat) n \<longleftrightarrow> True"
  by (rule HOL.eq_refl)

lemma less_eq_nat_code [code]:
  "n \<le> m \<longleftrightarrow> (of_nat n \<Colon> int) \<le> of_nat m"
  by simp

lemma less_nat_code [code]:
  "n < m \<longleftrightarrow> (of_nat n \<Colon> int) < of_nat m"
  by simp

subsection {* Case analysis *}

text {*
  Case analysis on natural numbers is rephrased using a conditional
  expression:
*}

lemma [code, code_unfold]:
  "nat_case = (\<lambda>f g n. if n = 0 then f else g (n - 1))"
  by (auto simp add: expand_fun_eq dest!: gr0_implies_Suc)


subsection {* Preprocessors *}

text {*
  In contrast to @{term "Suc n"}, the term @{term "n + (1::nat)"} is no longer
  a constructor term. Therefore, all occurrences of this term in a position
  where a pattern is expected (i.e.\ on the left-hand side of a recursion
  equation or in the arguments of an inductive relation in an introduction
  rule) must be eliminated.
  This can be accomplished by applying the following transformation rules:
*}

lemma Suc_if_eq: "(\<And>n. f (Suc n) \<equiv> h n) \<Longrightarrow> f 0 \<equiv> g \<Longrightarrow>
  f n \<equiv> if n = 0 then g else h (n - 1)"
  by (rule eq_reflection) (cases n, simp_all)

lemma Suc_clause: "(\<And>n. P n (Suc n)) \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> P (n - 1) n"
  by (cases n) simp_all

text {*
  The rules above are built into a preprocessor that is plugged into
  the code generator. Since the preprocessor for introduction rules
  does not know anything about modes, some of the modes that worked
  for the canonical representation of natural numbers may no longer work.
*}

(*<*)
setup {*
let

fun remove_suc thy thms =
  let
    val vname = Name.variant (map fst
      (fold (Term.add_var_names o Thm.full_prop_of) thms [])) "n";
    val cv = cterm_of thy (Var ((vname, 0), HOLogic.natT));
    fun lhs_of th = snd (Thm.dest_comb
      (fst (Thm.dest_comb (cprop_of th))));
    fun rhs_of th = snd (Thm.dest_comb (cprop_of th));
    fun find_vars ct = (case term_of ct of
        (Const (@{const_name Suc}, _) $ Var _) => [(cv, snd (Thm.dest_comb ct))]
      | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in 
          map (apfst (fn ct => Thm.capply ct ct2)) (find_vars ct1) @
          map (apfst (Thm.capply ct1)) (find_vars ct2)
        end
      | _ => []);
    val eqs = maps
      (fn th => map (pair th) (find_vars (lhs_of th))) thms;
    fun mk_thms (th, (ct, cv')) =
      let
        val th' =
          Thm.implies_elim
           (Conv.fconv_rule (Thm.beta_conversion true)
             (Drule.instantiate'
               [SOME (ctyp_of_term ct)] [SOME (Thm.cabs cv ct),
                 SOME (Thm.cabs cv' (rhs_of th)), NONE, SOME cv']
               @{thm Suc_if_eq})) (Thm.forall_intr cv' th)
      in
        case map_filter (fn th'' =>
            SOME (th'', singleton
              (Variable.trade (K (fn [th'''] => [th''' RS th'])) (Variable.thm_context th'')) th'')
          handle THM _ => NONE) thms of
            [] => NONE
          | thps =>
              let val (ths1, ths2) = split_list thps
              in SOME (subtract Thm.eq_thm (th :: ths1) thms @ ths2) end
      end
  in get_first mk_thms eqs end;

fun eqn_suc_preproc thy thms =
  let
    val dest = fst o Logic.dest_equals o prop_of;
    val contains_suc = exists_Const (fn (c, _) => c = @{const_name Suc});
  in
    if forall (can dest) thms andalso exists (contains_suc o dest) thms
      then perhaps_loop (remove_suc thy) thms
       else NONE
  end;

val eqn_suc_preproc1 = Code_Preproc.simple_functrans eqn_suc_preproc;

fun eqn_suc_preproc2 thy thms = eqn_suc_preproc thy thms
  |> the_default thms;

fun remove_suc_clause thy thms =
  let
    val vname = Name.variant (map fst
      (fold (Term.add_var_names o Thm.full_prop_of) thms [])) "x";
    fun find_var (t as Const (@{const_name Suc}, _) $ (v as Var _)) = SOME (t, v)
      | find_var (t $ u) = (case find_var t of NONE => find_var u | x => x)
      | find_var _ = NONE;
    fun find_thm th =
      let val th' = Conv.fconv_rule ObjectLogic.atomize th
      in Option.map (pair (th, th')) (find_var (prop_of th')) end
  in
    case get_first find_thm thms of
      NONE => thms
    | SOME ((th, th'), (Sucv, v)) =>
        let
          val cert = cterm_of (Thm.theory_of_thm th);
          val th'' = ObjectLogic.rulify (Thm.implies_elim
            (Conv.fconv_rule (Thm.beta_conversion true)
              (Drule.instantiate' []
                [SOME (cert (lambda v (Abs ("x", HOLogic.natT,
                   abstract_over (Sucv,
                     HOLogic.dest_Trueprop (prop_of th')))))),
                 SOME (cert v)] @{thm Suc_clause}))
            (Thm.forall_intr (cert v) th'))
        in
          remove_suc_clause thy (map (fn th''' =>
            if (op = o pairself prop_of) (th''', th) then th'' else th''') thms)
        end
  end;

fun clause_suc_preproc thy ths =
  let
    val dest = fst o HOLogic.dest_mem o HOLogic.dest_Trueprop
  in
    if forall (can (dest o concl_of)) ths andalso
      exists (fn th => exists (exists_Const (fn (c, _) => c = @{const_name Suc}))
        (map_filter (try dest) (concl_of th :: prems_of th))) ths
    then remove_suc_clause thy ths else ths
  end;
in

  Codegen.add_preprocessor eqn_suc_preproc2
  #> Codegen.add_preprocessor clause_suc_preproc
  #> Code_Preproc.add_functrans ("eqn_Suc", eqn_suc_preproc1)

end;
*}
(*>*)


subsection {* Target language setup *}

text {*
  For ML, we map @{typ nat} to target language integers, where we
  assert that values are always non-negative.
*}

code_type nat
  (SML "IntInf.int")
  (OCaml "Big'_int.big'_int")

types_code
  nat ("int")
attach (term_of) {*
val term_of_nat = HOLogic.mk_number HOLogic.natT;
*}
attach (test) {*
fun gen_nat i =
  let val n = random_range 0 i
  in (n, fn () => term_of_nat n) end;
*}

text {*
  For Haskell we define our own @{typ nat} type.  The reason
  is that we have to distinguish type class instances
  for @{typ nat} and @{typ int}.
*}

code_include Haskell "Nat" {*
newtype Nat = Nat Integer deriving (Show, Eq);

instance Num Nat where {
  fromInteger k = Nat (if k >= 0 then k else 0);
  Nat n + Nat m = Nat (n + m);
  Nat n - Nat m = fromInteger (n - m);
  Nat n * Nat m = Nat (n * m);
  abs n = n;
  signum _ = 1;
  negate n = error "negate Nat";
};

instance Ord Nat where {
  Nat n <= Nat m = n <= m;
  Nat n < Nat m = n < m;
};

instance Real Nat where {
  toRational (Nat n) = toRational n;
};

instance Enum Nat where {
  toEnum k = fromInteger (toEnum k);
  fromEnum (Nat n) = fromEnum n;
};

instance Integral Nat where {
  toInteger (Nat n) = n;
  divMod n m = quotRem n m;
  quotRem (Nat n) (Nat m) = (Nat k, Nat l) where (k, l) = quotRem n m;
};
*}

code_reserved Haskell Nat

code_type nat
  (Haskell "Nat.Nat")

code_instance nat :: eq
  (Haskell -)

text {*
  Natural numerals.
*}

lemma [code_unfold_post]:
  "nat (number_of i) = number_nat_inst.number_of_nat i"
  -- {* this interacts as desired with @{thm nat_number_of_def} *}
  by (simp add: number_nat_inst.number_of_nat)

setup {*
  fold (Numeral.add_code @{const_name number_nat_inst.number_of_nat}
    false true) ["SML", "OCaml", "Haskell"]
*}

text {*
  Since natural numbers are implemented
  using integers in ML, the coercion function @{const "of_nat"} of type
  @{typ "nat \<Rightarrow> int"} is simply implemented by the identity function.
  For the @{const "nat"} function for converting an integer to a natural
  number, we give a specific implementation using an ML function that
  returns its input value, provided that it is non-negative, and otherwise
  returns @{text "0"}.
*}

definition int :: "nat \<Rightarrow> int" where
  [code del]: "int = of_nat"

lemma int_code' [code]:
  "int (number_of l) = (if neg (number_of l \<Colon> int) then 0 else number_of l)"
  unfolding int_nat_number_of [folded int_def] ..

lemma nat_code' [code]:
  "nat (number_of l) = (if neg (number_of l \<Colon> int) then 0 else number_of l)"
  unfolding nat_number_of_def number_of_is_id neg_def by simp

lemma of_nat_int [code_unfold_post]:
  "of_nat = int" by (simp add: int_def)

lemma of_nat_aux_int [code_unfold]:
  "of_nat_aux (\<lambda>i. i + 1) k 0 = int k"
  by (simp add: int_def Nat.of_nat_code)

code_const int
  (SML "_")
  (OCaml "_")

consts_code
  int ("(_)")
  nat ("\<module>nat")
attach {*
fun nat i = if i < 0 then 0 else i;
*}

code_const nat
  (SML "IntInf.max/ (/0,/ _)")
  (OCaml "Big'_int.max'_big'_int/ Big'_int.zero'_big'_int")

text {* For Haskell, things are slightly different again. *}

code_const int and nat
  (Haskell "toInteger" and "fromInteger")

text {* Conversion from and to indices. *}

code_const Code_Numeral.of_nat
  (SML "IntInf.toInt")
  (OCaml "_")
  (Haskell "fromEnum")

code_const Code_Numeral.nat_of
  (SML "IntInf.fromInt")
  (OCaml "_")
  (Haskell "toEnum")

text {* Using target language arithmetic operations whenever appropriate *}

code_const "op + \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.+ ((_), (_))")
  (OCaml "Big'_int.add'_big'_int")
  (Haskell infixl 6 "+")

code_const "op * \<Colon> nat \<Rightarrow> nat \<Rightarrow> nat"
  (SML "IntInf.* ((_), (_))")
  (OCaml "Big'_int.mult'_big'_int")
  (Haskell infixl 7 "*")

code_const divmod_aux
  (SML "IntInf.divMod/ ((_),/ (_))")
  (OCaml "Big'_int.quomod'_big'_int")
  (Haskell "divMod")

code_const "eq_class.eq \<Colon> nat \<Rightarrow> nat \<Rightarrow> bool"
  (SML "!((_ : IntInf.int) = _)")
  (OCaml "Big'_int.eq'_big'_int")
  (Haskell infixl 4 "==")

code_const "op \<le> \<Colon> nat \<Rightarrow> nat \<Rightarrow> bool"
  (SML "IntInf.<= ((_), (_))")
  (OCaml "Big'_int.le'_big'_int")
  (Haskell infix 4 "<=")

code_const "op < \<Colon> nat \<Rightarrow> nat \<Rightarrow> bool"
  (SML "IntInf.< ((_), (_))")
  (OCaml "Big'_int.lt'_big'_int")
  (Haskell infix 4 "<")

consts_code
  "0::nat"                     ("0")
  "1::nat"                     ("1")
  Suc                          ("(_ +/ 1)")
  "op + \<Colon>  nat \<Rightarrow> nat \<Rightarrow> nat"   ("(_ +/ _)")
  "op * \<Colon>  nat \<Rightarrow> nat \<Rightarrow> nat"   ("(_ */ _)")
  "op \<le> \<Colon>  nat \<Rightarrow> nat \<Rightarrow> bool"  ("(_ <=/ _)")
  "op < \<Colon>  nat \<Rightarrow> nat \<Rightarrow> bool"  ("(_ </ _)")


text {* Evaluation *}

lemma [code, code del]:
  "(Code_Eval.term_of \<Colon> nat \<Rightarrow> term) = Code_Eval.term_of" ..

code_const "Code_Eval.term_of \<Colon> nat \<Rightarrow> term"
  (SML "HOLogic.mk'_number/ HOLogic.natT")


text {* Module names *}

code_modulename SML
  Nat Integer
  Divides Integer
  Ring_and_Field Integer
  Efficient_Nat Integer

code_modulename OCaml
  Nat Integer
  Divides Integer
  Ring_and_Field Integer
  Efficient_Nat Integer

code_modulename Haskell
  Nat Integer
  Divides Integer
  Ring_and_Field Integer
  Efficient_Nat Integer

hide const int

end
