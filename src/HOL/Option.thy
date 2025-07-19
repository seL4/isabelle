(*  Title:      HOL/Option.thy
    Author:     Folklore
*)

section \<open>Datatype option\<close>

theory Option
  imports Lifting
begin

datatype 'a option =
    None
  | Some (the: 'a)

datatype_compat option

lemma [case_names None Some, cases type: option]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "(y = None \<Longrightarrow> P) \<Longrightarrow> (\<And>a. y = Some a \<Longrightarrow> P) \<Longrightarrow> P"
  by (rule option.exhaust)

lemma [case_names None Some, induct type: option]:
  \<comment> \<open>for backward compatibility -- names of variables differ\<close>
  "P None \<Longrightarrow> (\<And>option. P (Some option)) \<Longrightarrow> P option"
  by (rule option.induct)

text \<open>Compatibility:\<close>
setup \<open>Sign.mandatory_path "option"\<close>
lemmas inducts = option.induct
lemmas cases = option.case
setup \<open>Sign.parent_path\<close>

lemma not_None_eq [iff]: "x \<noteq> None \<longleftrightarrow> (\<exists>y. x = Some y)"
  by (induct x) auto

lemma not_Some_eq [iff]: "(\<forall>y. x \<noteq> Some y) \<longleftrightarrow> x = None"
  by (induct x) auto

lemma comp_the_Some[simp]: "the o Some = id"
by auto

text \<open>Although it may appear that both of these equalities are helpful
only when applied to assumptions, in practice it seems better to give
them the uniform iff attribute.\<close>

lemma inj_Some [simp]: "inj_on Some A"
  by (rule inj_onI) simp

lemma case_optionE:
  assumes c: "(case x of None \<Rightarrow> P | Some y \<Rightarrow> Q y)"
  obtains
    (None) "x = None" and P
  | (Some) y where "x = Some y" and "Q y"
  using c by (cases x) simp_all

lemma split_option_all: "(\<forall>x. P x) \<longleftrightarrow> P None \<and> (\<forall>x. P (Some x))"
  by (auto intro: option.induct)

lemma split_option_ex: "(\<exists>x. P x) \<longleftrightarrow> P None \<or> (\<exists>x. P (Some x))"
  using split_option_all[of "\<lambda>x. \<not> P x"] by blast

lemma UNIV_option_conv: "UNIV = insert None (range Some)"
  by (auto intro: classical)

lemma rel_option_None1 [simp]: "rel_option P None x \<longleftrightarrow> x = None"
  by (cases x) simp_all

lemma rel_option_None2 [simp]: "rel_option P x None \<longleftrightarrow> x = None"
  by (cases x) simp_all

lemma option_rel_Some1: "rel_option A (Some x) y \<longleftrightarrow> (\<exists>y'. y = Some y' \<and> A x y')" (* Option *)
by(cases y) simp_all

lemma option_rel_Some2: "rel_option A x (Some y) \<longleftrightarrow> (\<exists>x'. x = Some x' \<and> A x' y)" (* Option *)
by(cases x) simp_all

lemma rel_option_inf: "inf (rel_option A) (rel_option B) = rel_option (inf A B)"
  (is "?lhs = ?rhs")
proof (rule antisym)
  show "?lhs \<le> ?rhs" by (auto elim: option.rel_cases)
  show "?rhs \<le> ?lhs" by (auto elim: option.rel_mono_strong)
qed

lemma rel_option_reflI:
  "(\<And>x. x \<in> set_option y \<Longrightarrow> P x x) \<Longrightarrow> rel_option P y y"
  by (cases y) auto


subsubsection \<open>Operations\<close>

lemma ospec [dest]: "(\<forall>x\<in>set_option A. P x) \<Longrightarrow> A = Some x \<Longrightarrow> P x"
  by simp

setup \<open>map_theory_claset (fn ctxt => ctxt addSD2 ("ospec", @{thm ospec}))\<close>

lemma elem_set [iff]: "(x \<in> set_option xo) = (xo = Some x)"
  by (cases xo) auto

lemma set_empty_eq [simp]: "(set_option xo = {}) = (xo = None)"
  by (cases xo) auto

lemma map_option_case: "map_option f y = (case y of None \<Rightarrow> None | Some x \<Rightarrow> Some (f x))"
  by (auto split: option.split)

lemma map_option_is_None [iff]: "(map_option f opt = None) = (opt = None)"
  by (simp add: map_option_case split: option.split)

lemma None_eq_map_option_iff [iff]: "None = map_option f x \<longleftrightarrow> x = None"
by(cases x) simp_all

lemma map_option_eq_Some [iff]: "(map_option f xo = Some y) = (\<exists>z. xo = Some z \<and> f z = y)"
  by (simp add: map_option_case split: option.split)

lemma map_option_o_case_sum [simp]:
    "map_option f \<circ> case_sum g h = case_sum (map_option f \<circ> g) (map_option f \<circ> h)"
  by (rule o_case_sum)

lemma map_option_cong: "x = y \<Longrightarrow> (\<And>a. y = Some a \<Longrightarrow> f a = g a) \<Longrightarrow> map_option f x = map_option g y"
  by (cases x) auto

lemma map_option_idI: "(\<And>y. y \<in> set_option x \<Longrightarrow> f y = y) \<Longrightarrow> map_option f x = x"
by(cases x)(simp_all)

functor map_option: map_option
  by (simp_all add: option.map_comp fun_eq_iff option.map_id)

lemma case_map_option [simp]: "case_option g h (map_option f x) = case_option g (h \<circ> f) x"
  by (cases x) simp_all

lemma None_notin_image_Some [simp]: "None \<notin> Some ` A"
by auto

lemma notin_range_Some: "x \<notin> range Some \<longleftrightarrow> x = None"
by(cases x) auto

lemma rel_option_iff:
  "rel_option R x y = (case (x, y) of (None, None) \<Rightarrow> True
    | (Some x, Some y) \<Rightarrow> R x y
    | _ \<Rightarrow> False)"
  by (auto split: prod.split option.split)


definition combine_options :: "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> 'a option \<Rightarrow> 'a option \<Rightarrow> 'a option"
  where "combine_options f x y = 
           (case x of None \<Rightarrow> y | Some x \<Rightarrow> (case y of None \<Rightarrow> Some x | Some y \<Rightarrow> Some (f x y)))"

lemma combine_options_simps [simp]:
  "combine_options f None y = y"
  "combine_options f x None = x"
  "combine_options f (Some a) (Some b) = Some (f a b)"
  by (simp_all add: combine_options_def split: option.splits)
  
lemma combine_options_cases [case_names None1 None2 Some]:
  "(x = None \<Longrightarrow> P x y) \<Longrightarrow> (y = None \<Longrightarrow> P x y) \<Longrightarrow> 
     (\<And>a b. x = Some a \<Longrightarrow> y = Some b \<Longrightarrow> P x y) \<Longrightarrow> P x y"
  by (cases x; cases y) simp_all

lemma combine_options_commute: 
  "(\<And>x y. f x y = f y x) \<Longrightarrow> combine_options f x y = combine_options f y x"
  using combine_options_cases[of x ]
  by (induction x y rule: combine_options_cases) simp_all

lemma combine_options_assoc:
  "(\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow> 
     combine_options f (combine_options f x y) z =
     combine_options f x (combine_options f y z)"
  by (auto simp: combine_options_def split: option.splits)

lemma combine_options_left_commute:
  "(\<And>x y. f x y = f y x) \<Longrightarrow> (\<And>x y z. f (f x y) z = f x (f y z)) \<Longrightarrow> 
     combine_options f y (combine_options f x z) =
     combine_options f x (combine_options f y z)"
  by (auto simp: combine_options_def split: option.splits)

lemmas combine_options_ac = 
  combine_options_commute combine_options_assoc combine_options_left_commute


context
begin

qualified definition is_none :: "'a option \<Rightarrow> bool"
  where [code_post]: "is_none x \<longleftrightarrow> x = None"

lemma is_none_simps [simp]:
  "is_none None"
  "\<not> is_none (Some x)"
  by (simp_all add: is_none_def)

lemma is_none_code [code]:
  "is_none None \<longleftrightarrow> True"
  "is_none (Some x) \<longleftrightarrow> False"
  by simp_all

lemma rel_option_unfold:
  "rel_option R x y \<longleftrightarrow>
   (is_none x \<longleftrightarrow> is_none y) \<and> (\<not> is_none x \<longrightarrow> \<not> is_none y \<longrightarrow> R (the x) (the y))"
  by (simp add: rel_option_iff split: option.split)

lemma rel_optionI:
  "\<lbrakk> is_none x \<longleftrightarrow> is_none y; \<lbrakk> \<not> is_none x; \<not> is_none y \<rbrakk> \<Longrightarrow> P (the x) (the y) \<rbrakk>
  \<Longrightarrow> rel_option P x y"
  by (simp add: rel_option_unfold)

lemma is_none_map_option [simp]: "is_none (map_option f x) \<longleftrightarrow> is_none x"
  by (simp add: is_none_def)

lemma the_map_option: "\<not> is_none x \<Longrightarrow> the (map_option f x) = f (the x)"
  by (auto simp add: is_none_def)


qualified primrec bind :: "'a option \<Rightarrow> ('a \<Rightarrow> 'b option) \<Rightarrow> 'b option"
where
  bind_lzero: "bind None f = None"
| bind_lunit: "bind (Some x) f = f x"

lemma is_none_bind: "is_none (bind f g) \<longleftrightarrow> is_none f \<or> is_none (g (the f))"
  by (cases f) simp_all

lemma bind_runit[simp]: "bind x Some = x"
  by (cases x) auto

lemma bind_assoc[simp]: "bind (bind x f) g = bind x (\<lambda>y. bind (f y) g)"
  by (cases x) auto

lemma bind_rzero[simp]: "bind x (\<lambda>x. None) = None"
  by (cases x) auto

qualified lemma bind_cong: "x = y \<Longrightarrow> (\<And>a. y = Some a \<Longrightarrow> f a = g a) \<Longrightarrow> bind x f = bind y g"
  by (cases x) auto

lemma bind_split: "P (bind m f) \<longleftrightarrow> (m = None \<longrightarrow> P None) \<and> (\<forall>v. m = Some v \<longrightarrow> P (f v))"
  by (cases m) auto

lemma bind_split_asm: "P (bind m f) \<longleftrightarrow> \<not> (m = None \<and> \<not> P None \<or> (\<exists>x. m = Some x \<and> \<not> P (f x)))"
  by (cases m) auto

lemmas bind_splits = bind_split bind_split_asm

lemma bind_eq_Some_conv: "bind f g = Some x \<longleftrightarrow> (\<exists>y. f = Some y \<and> g y = Some x)"
  by (cases f) simp_all

lemma bind_eq_None_conv: "Option.bind a f = None \<longleftrightarrow> a = None \<or> f (the a) = None"
by(cases a) simp_all

lemma map_option_bind: "map_option f (bind x g) = bind x (map_option f \<circ> g)"
  by (cases x) simp_all

lemma bind_option_cong:
  "\<lbrakk> x = y; \<And>z. z \<in> set_option y \<Longrightarrow> f z = g z \<rbrakk> \<Longrightarrow> bind x f = bind y g"
  by (cases y) simp_all

lemma bind_option_cong_simp:
  "\<lbrakk> x = y; \<And>z. z \<in> set_option y =simp=> f z = g z \<rbrakk> \<Longrightarrow> bind x f = bind y g"
  unfolding simp_implies_def by (rule bind_option_cong)

lemma bind_option_cong_code: "x = y \<Longrightarrow> bind x f = bind y f"
  by simp

lemma bind_map_option: "bind (map_option f x) g = bind x (g \<circ> f)"
by(cases x) simp_all

lemma set_bind_option [simp]: "set_option (bind x f) = (\<Union>((set_option \<circ> f) ` set_option x))"
by(cases x) auto

lemma map_conv_bind_option: "map_option f x = Option.bind x (Some \<circ> f)"
by(cases x) simp_all

end

setup \<open>Code_Simp.map_ss (Simplifier.add_cong @{thm bind_option_cong_code})\<close>


context
begin

qualified definition these :: "'a option set \<Rightarrow> 'a set"
  where "these A = the ` {x \<in> A. x \<noteq> None}"

qualified lemma these_eq [code]:
  \<open>these A = the ` (Set.filter (Not \<circ> Option.is_none) A)\<close>
  by (simp add: these_def Option.is_none_def)

qualified lemma these_unfold:
  \<open>these A = {x. \<exists>y \<in> A. y = Some x}\<close>
  by (auto simp add: these_def set_eq_iff image_iff)

lemma these_empty [simp]: "these {} = {}"
  by (simp add: these_def)

lemma these_insert_None [simp]: "these (insert None A) = these A"
  by (auto simp add: these_def)

lemma these_insert_Some [simp]: "these (insert (Some x) A) = insert x (these A)"
proof -
  have "{y \<in> insert (Some x) A. y \<noteq> None} = insert (Some x) {y \<in> A. y \<noteq> None}"
    by auto
  then show ?thesis by (simp add: these_def)
qed

lemma in_these_eq: "x \<in> these A \<longleftrightarrow> Some x \<in> A"
proof
  assume "Some x \<in> A"
  then obtain B where "A = insert (Some x) B" by auto
  then show "x \<in> these A" by (auto simp add: these_def intro!: image_eqI)
next
  assume "x \<in> these A"
  then show "Some x \<in> A" by (auto simp add: these_def)
qed

lemma these_image_Some_eq [simp]: "these (Some ` A) = A"
  by (auto simp add: these_def intro!: image_eqI)

lemma Some_image_these_eq: "Some ` these A = {x\<in>A. x \<noteq> None}"
  by (auto simp add: these_def image_image intro!: image_eqI)

lemma these_empty_eq: "these B = {} \<longleftrightarrow> B = {} \<or> B = {None}"
  by (auto simp add: these_def)

lemma these_not_empty_eq: "these B \<noteq> {} \<longleftrightarrow> B \<noteq> {} \<and> B \<noteq> {None}"
  by (auto simp add: these_empty_eq)

qualified definition image_filter :: "('a \<Rightarrow> 'b option) \<Rightarrow> 'a set \<Rightarrow> 'b set"
  where image_filter_eq: "image_filter f A = these (f ` A)"

end

lemma finite_range_Some: "finite (range (Some :: 'a \<Rightarrow> 'a option)) = finite (UNIV :: 'a set)"
  by (auto dest: finite_imageD intro: inj_Some)


subsection \<open>Transfer rules for the Transfer package\<close>

context includes lifting_syntax
begin

lemma option_bind_transfer [transfer_rule]:
  "(rel_option A ===> (A ===> rel_option B) ===> rel_option B)
    Option.bind Option.bind"
  unfolding rel_fun_def split_option_all by simp

lemma pred_option_parametric [transfer_rule]:
  "((A ===> (=)) ===> rel_option A ===> (=)) pred_option pred_option"
  by (rule rel_funI)+ (auto simp add: rel_option_unfold Option.is_none_def dest: rel_funD)

end


subsubsection \<open>Interaction with finite sets\<close>

lemma finite_option_UNIV [simp]:
  "finite (UNIV :: 'a option set) = finite (UNIV :: 'a set)"
  by (auto simp add: UNIV_option_conv elim: finite_imageD intro: inj_Some)

instance option :: (finite) finite
  by standard (simp add: UNIV_option_conv)


subsubsection \<open>Code generator setup\<close>

lemma equal_None_code_unfold [code_unfold]:
  "HOL.equal x None \<longleftrightarrow> Option.is_none x"
  "HOL.equal None = Option.is_none"
  by (auto simp add: equal Option.is_none_def)

code_printing
  type_constructor option \<rightharpoonup>
    (SML) "_ option"
    and (OCaml) "_ option"
    and (Haskell) "Maybe _"
    and (Scala) "!Option[(_)]"
| constant None \<rightharpoonup>
    (SML) "NONE"
    and (OCaml) "None"
    and (Haskell) "Nothing"
    and (Scala) "!None"
| constant Some \<rightharpoonup>
    (SML) "SOME"
    and (OCaml) "Some _"
    and (Haskell) "Just"
    and (Scala) "Some"
| class_instance option :: equal \<rightharpoonup>
    (Haskell) -
| constant "HOL.equal :: 'a option \<Rightarrow> 'a option \<Rightarrow> bool" \<rightharpoonup>
    (Haskell) infix 4 "=="

code_reserved
  (SML) option NONE SOME
  and (OCaml) option None Some
  and (Scala) Option None Some

end
