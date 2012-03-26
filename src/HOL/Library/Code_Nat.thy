(*  Title:      HOL/Library/Code_Nat.thy
    Author:     Stefan Berghofer, Florian Haftmann, TU Muenchen
*)

header {* Implementation of natural numbers as binary numerals *}

theory Code_Nat
imports Main
begin

text {*
  When generating code for functions on natural numbers, the
  canonical representation using @{term "0::nat"} and
  @{term Suc} is unsuitable for computations involving large
  numbers.  This theory refines the representation of
  natural numbers for code generation to use binary
  numerals, which do not grow linear in size but logarithmic.
*}

subsection {* Representation *}

lemma [code_abbrev]:
  "nat_of_num = numeral"
  by (fact nat_of_num_numeral)

code_datatype "0::nat" nat_of_num

lemma [code]:
  "num_of_nat 0 = Num.One"
  "num_of_nat (nat_of_num k) = k"
  by (simp_all add: nat_of_num_inverse)

lemma [code]:
  "(1\<Colon>nat) = Numeral1"
  by simp

lemma [code_abbrev]: "Numeral1 = (1\<Colon>nat)"
  by simp

lemma [code]:
  "Suc n = n + 1"
  by simp


subsection {* Basic arithmetic *}

lemma [code, code del]:
  "(plus :: nat \<Rightarrow> _) = plus" ..

lemma plus_nat_code [code]:
  "nat_of_num k + nat_of_num l = nat_of_num (k + l)"
  "m + 0 = (m::nat)"
  "0 + n = (n::nat)"
  by (simp_all add: nat_of_num_numeral)

text {* Bounded subtraction needs some auxiliary *}

definition dup :: "nat \<Rightarrow> nat" where
  "dup n = n + n"

lemma dup_code [code]:
  "dup 0 = 0"
  "dup (nat_of_num k) = nat_of_num (Num.Bit0 k)"
  unfolding Num_def by (simp_all add: dup_def numeral_Bit0)

definition sub :: "num \<Rightarrow> num \<Rightarrow> nat option" where
  "sub k l = (if k \<ge> l then Some (numeral k - numeral l) else None)"

lemma sub_code [code]:
  "sub Num.One Num.One = Some 0"
  "sub (Num.Bit0 m) Num.One = Some (nat_of_num (Num.BitM m))"
  "sub (Num.Bit1 m) Num.One = Some (nat_of_num (Num.Bit0 m))"
  "sub Num.One (Num.Bit0 n) = None"
  "sub Num.One (Num.Bit1 n) = None"
  "sub (Num.Bit0 m) (Num.Bit0 n) = Option.map dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit1 n) = Option.map dup (sub m n)"
  "sub (Num.Bit1 m) (Num.Bit0 n) = Option.map (\<lambda>q. dup q + 1) (sub m n)"
  "sub (Num.Bit0 m) (Num.Bit1 n) = (case sub m n of None \<Rightarrow> None
     | Some q \<Rightarrow> if q = 0 then None else Some (dup q - 1))"
  apply (auto simp add: nat_of_num_numeral
    Num.dbl_def Num.dbl_inc_def Num.dbl_dec_def
    Let_def le_imp_diff_is_add BitM_plus_one sub_def dup_def)
  apply (simp_all add: sub_non_positive)
  apply (simp_all add: sub_non_negative [symmetric, where ?'a = int])
  done

lemma [code, code del]:
  "(minus :: nat \<Rightarrow> _) = minus" ..

lemma minus_nat_code [code]:
  "nat_of_num k - nat_of_num l = (case sub k l of None \<Rightarrow> 0 | Some j \<Rightarrow> j)"
  "m - 0 = (m::nat)"
  "0 - n = (0::nat)"
  by (simp_all add: nat_of_num_numeral sub_non_positive sub_def)

lemma [code, code del]:
  "(times :: nat \<Rightarrow> _) = times" ..

lemma times_nat_code [code]:
  "nat_of_num k * nat_of_num l = nat_of_num (k * l)"
  "m * 0 = (0::nat)"
  "0 * n = (0::nat)"
  by (simp_all add: nat_of_num_numeral)

lemma [code, code del]:
  "(HOL.equal :: nat \<Rightarrow> _) = HOL.equal" ..

lemma equal_nat_code [code]:
  "HOL.equal 0 (0::nat) \<longleftrightarrow> True"
  "HOL.equal 0 (nat_of_num l) \<longleftrightarrow> False"
  "HOL.equal (nat_of_num k) 0 \<longleftrightarrow> False"
  "HOL.equal (nat_of_num k) (nat_of_num l) \<longleftrightarrow> HOL.equal k l"
  by (simp_all add: nat_of_num_numeral equal)

lemma equal_nat_refl [code nbe]:
  "HOL.equal (n::nat) n \<longleftrightarrow> True"
  by (rule equal_refl)

lemma [code, code del]:
  "(less_eq :: nat \<Rightarrow> _) = less_eq" ..

lemma less_eq_nat_code [code]:
  "0 \<le> (n::nat) \<longleftrightarrow> True"
  "nat_of_num k \<le> 0 \<longleftrightarrow> False"
  "nat_of_num k \<le> nat_of_num l \<longleftrightarrow> k \<le> l"
  by (simp_all add: nat_of_num_numeral)

lemma [code, code del]:
  "(less :: nat \<Rightarrow> _) = less" ..

lemma less_nat_code [code]:
  "(m::nat) < 0 \<longleftrightarrow> False"
  "0 < nat_of_num l \<longleftrightarrow> True"
  "nat_of_num k < nat_of_num l \<longleftrightarrow> k < l"
  by (simp_all add: nat_of_num_numeral)


subsection {* Conversions *}

lemma [code, code del]:
  "of_nat = of_nat" ..

lemma of_nat_code [code]:
  "of_nat 0 = 0"
  "of_nat (nat_of_num k) = numeral k"
  by (simp_all add: nat_of_num_numeral)


subsection {* Case analysis *}

text {*
  Case analysis on natural numbers is rephrased using a conditional
  expression:
*}

lemma [code, code_unfold]:
  "nat_case = (\<lambda>f g n. if n = 0 then f else g (n - 1))"
  by (auto simp add: fun_eq_iff dest!: gr0_implies_Suc)


subsection {* Preprocessors *}

text {*
  The term @{term "Suc n"} is no longer a valid pattern.
  Therefore, all occurrences of this term in a position
  where a pattern is expected (i.e.~on the left-hand side of a recursion
  equation) must be eliminated.
  This can be accomplished by applying the following transformation rules:
*}

lemma Suc_if_eq: "(\<And>n. f (Suc n) \<equiv> h n) \<Longrightarrow> f 0 \<equiv> g \<Longrightarrow>
  f n \<equiv> if n = 0 then g else h (n - 1)"
  by (rule eq_reflection) (cases n, simp_all)

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
    val vname = singleton (Name.variant_list (map fst
      (fold (Term.add_var_names o Thm.full_prop_of) thms []))) "n";
    val cv = cterm_of thy (Var ((vname, 0), HOLogic.natT));
    fun lhs_of th = snd (Thm.dest_comb
      (fst (Thm.dest_comb (cprop_of th))));
    fun rhs_of th = snd (Thm.dest_comb (cprop_of th));
    fun find_vars ct = (case term_of ct of
        (Const (@{const_name Suc}, _) $ Var _) => [(cv, snd (Thm.dest_comb ct))]
      | _ $ _ =>
        let val (ct1, ct2) = Thm.dest_comb ct
        in 
          map (apfst (fn ct => Thm.apply ct ct2)) (find_vars ct1) @
          map (apfst (Thm.apply ct1)) (find_vars ct2)
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
               [SOME (ctyp_of_term ct)] [SOME (Thm.lambda cv ct),
                 SOME (Thm.lambda cv' (rhs_of th)), NONE, SOME cv']
               @{thm Suc_if_eq})) (Thm.forall_intr cv' th)
      in
        case map_filter (fn th'' =>
            SOME (th'', singleton
              (Variable.trade (K (fn [th'''] => [th''' RS th']))
                (Variable.global_thm_context th'')) th'')
          handle THM _ => NONE) thms of
            [] => NONE
          | thps =>
              let val (ths1, ths2) = split_list thps
              in SOME (subtract Thm.eq_thm (th :: ths1) thms @ ths2) end
      end
  in get_first mk_thms eqs end;

fun eqn_suc_base_preproc thy thms =
  let
    val dest = fst o Logic.dest_equals o prop_of;
    val contains_suc = exists_Const (fn (c, _) => c = @{const_name Suc});
  in
    if forall (can dest) thms andalso exists (contains_suc o dest) thms
      then thms |> perhaps_loop (remove_suc thy) |> (Option.map o map) Drule.zero_var_indexes
       else NONE
  end;

val eqn_suc_preproc = Code_Preproc.simple_functrans eqn_suc_base_preproc;

in

  Code_Preproc.add_functrans ("eqn_Suc", eqn_suc_preproc)

end;
*}
(*>*)

code_modulename SML
  Code_Nat Arith

code_modulename OCaml
  Code_Nat Arith

code_modulename Haskell
  Code_Nat Arith

hide_const (open) dup sub

end
