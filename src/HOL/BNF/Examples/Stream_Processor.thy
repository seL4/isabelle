(*  Title:      HOL/BNF/Examples/Stream_Processor.thy
    Author:     Dmitriy Traytel, TU Muenchen
    Author:     Andrei Popescu, TU Muenchen
    Copyright   2014

Stream processors---a syntactic representation of continuous functions on streams
*)

header {* Stream Processors *}

theory Stream_Processor
imports Stream
begin

section {* Continuous Functions on Streams *}

datatype_new ('a, 'b, 'c) sp\<^sub>\<mu> = Get "'a \<Rightarrow> ('a, 'b, 'c) sp\<^sub>\<mu>" | Put "'b" "'c"
codatatype ('a, 'b) sp\<^sub>\<nu> = In (out: "('a, 'b, ('a, 'b) sp\<^sub>\<nu>) sp\<^sub>\<mu>")

primrec_new run\<^sub>\<mu> :: "('a, 'b, 'c) sp\<^sub>\<mu> \<Rightarrow> 'a stream \<Rightarrow> ('b \<times> 'c) \<times> 'a stream" where
  "run\<^sub>\<mu> (Get f) s = run\<^sub>\<mu> (f (shd s)) (stl s)"
| "run\<^sub>\<mu> (Put b sp) s = ((b, sp), s)"

primcorec run\<^sub>\<nu> :: "('a, 'b) sp\<^sub>\<nu> \<Rightarrow> 'a stream \<Rightarrow> 'b stream" where
  "run\<^sub>\<nu> sp s = (let ((h, sp), s) = run\<^sub>\<mu> (out sp) s in h ## run\<^sub>\<nu> sp s)"

primcorec copy :: "('a, 'a) sp\<^sub>\<nu>" where
  "copy = In (Get (\<lambda>a. Put a copy))"

lemma run\<^sub>\<nu>_copy: "run\<^sub>\<nu> copy s = s"
  by (coinduction arbitrary: s) simp

text {*
To use the function package for the definition of composition the
wellfoundedness of the subtree relation needs to be proved first.
*}

definition "sub \<equiv> {(f a, Get f) | a f. True}"

lemma subI[intro]: "(f a, Get f) \<in> sub"
  unfolding sub_def by blast

lemma wf_sub[simp, intro]: "wf sub"
proof (rule wfUNIVI)
  fix P  :: "('a, 'b, 'c) sp\<^sub>\<mu> \<Rightarrow> bool" and x
  assume "\<forall>x. (\<forall>y. (y, x) \<in> sub \<longrightarrow> P y) \<longrightarrow> P x"
  hence I: "\<And>x. (\<forall>y. (\<exists>a f. y = f a \<and> x = Get f) \<longrightarrow> P y) \<Longrightarrow> P x" unfolding sub_def by blast
  show "P x" by (induct x) (auto intro: I)
qed

function
  sp\<^sub>\<mu>_comp :: "('a, 'b, 'c) sp\<^sub>\<mu> \<Rightarrow> ('d, 'a, ('d, 'a) sp\<^sub>\<nu>) sp\<^sub>\<mu> \<Rightarrow> ('d, 'b, 'c \<times> ('d, 'a) sp\<^sub>\<nu>) sp\<^sub>\<mu>"
  (infixl "o\<^sub>\<mu>" 65)
where
  "Put b sp o\<^sub>\<mu> fsp = Put b (sp, In fsp)"
| "Get f o\<^sub>\<mu> Put b sp = f b o\<^sub>\<mu> out sp"
| "Get f o\<^sub>\<mu> Get g = Get (\<lambda>a. Get f o\<^sub>\<mu> g a)"
by pat_completeness auto
termination by (relation "lex_prod sub sub") auto

primcorec sp\<^sub>\<nu>_comp (infixl "o\<^sub>\<nu>" 65) where
  "out (sp o\<^sub>\<nu> sp') = map_sp\<^sub>\<mu> id (\<lambda>(sp, sp'). sp o\<^sub>\<nu> sp') (out sp o\<^sub>\<mu> out sp')"

lemma run\<^sub>\<nu>_sp\<^sub>\<nu>_comp: "run\<^sub>\<nu> (sp o\<^sub>\<nu> sp') = run\<^sub>\<nu> sp o run\<^sub>\<nu> sp'"
proof (rule ext, unfold comp_apply)
  fix s
  show "run\<^sub>\<nu> (sp o\<^sub>\<nu> sp') s = run\<^sub>\<nu> sp (run\<^sub>\<nu> sp' s)"
  proof (coinduction arbitrary: sp sp' s)
    case Eq_stream
    show ?case
    proof (induct "out sp" "out sp'" arbitrary: sp sp' s rule: sp\<^sub>\<mu>_comp.induct)
      case (1 b sp'')
      show ?case by (auto simp add: 1[symmetric])
    next
      case (2 f b sp'')
      from 2(1)[of "In (f b)" sp''] show ?case by (simp add: 2(2,3)[symmetric])
    next
      case (3 f h)
      from 3(1)[of _ "shd s" "In (h (shd s))", OF 3(2)] show ?case by (simp add: 3(2,3)[symmetric])
    qed
  qed
qed

text {* Alternative definition of composition using primrec_new instead of function *}

primrec_new sp\<^sub>\<mu>_comp2R  where
  "sp\<^sub>\<mu>_comp2R f (Put b sp) = f b (out sp)"
| "sp\<^sub>\<mu>_comp2R f (Get h) = Get (sp\<^sub>\<mu>_comp2R f o h)"

primrec_new sp\<^sub>\<mu>_comp2 (infixl "o\<^sup>*\<^sub>\<mu>" 65) where
  "Put b sp o\<^sup>*\<^sub>\<mu> fsp = Put b (sp, In fsp)"
| "Get f o\<^sup>*\<^sub>\<mu> fsp = sp\<^sub>\<mu>_comp2R (op o\<^sup>*\<^sub>\<mu> o f) fsp"

primcorec sp\<^sub>\<nu>_comp2 (infixl "o\<^sup>*\<^sub>\<nu>" 65) where
  "out (sp o\<^sup>*\<^sub>\<nu> sp') = map_sp\<^sub>\<mu> id (\<lambda>(sp, sp'). sp o\<^sup>*\<^sub>\<nu> sp') (out sp o\<^sup>*\<^sub>\<mu> out sp')"

lemma run\<^sub>\<nu>_sp\<^sub>\<nu>_comp2: "run\<^sub>\<nu> (sp o\<^sup>*\<^sub>\<nu> sp') = run\<^sub>\<nu> sp o run\<^sub>\<nu> sp'"
proof (rule ext, unfold comp_apply)
  fix s
  show "run\<^sub>\<nu> (sp o\<^sup>*\<^sub>\<nu> sp') s = run\<^sub>\<nu> sp (run\<^sub>\<nu> sp' s)"
  proof (coinduction arbitrary: sp sp' s)
    case Eq_stream
    show ?case
    proof (induct "out sp" arbitrary: sp sp' s)
      case (Put b sp'')
      show ?case by (auto simp add: Put[symmetric])
    next
      case (Get f)
      then show ?case
      proof (induct "out sp'" arbitrary: sp sp' s)
        case (Put b sp'')
        from Put(2)[of "In (f b)" sp''] show ?case by (simp add: Put(1,3)[symmetric])
      next
        case (Get h)
        from Get(1)[OF _ Get(3,4), of "In (h (shd s))"] show ?case by (simp add: Get(2,4)[symmetric])
      qed
    qed
  qed
qed

text {* The two definitions are equivalent *}

lemma sp\<^sub>\<mu>_comp_sp\<^sub>\<mu>_comp2[simp]: "sp o\<^sub>\<mu> sp' = sp o\<^sup>*\<^sub>\<mu> sp'"
  by (induct sp sp' rule: sp\<^sub>\<mu>_comp.induct) auto

(*will be provided by the package*)
lemma sp\<^sub>\<mu>_rel_map_map[unfolded vimage2p_def, simp]:
  "rel_sp\<^sub>\<mu> R1 R2 (map_sp\<^sub>\<mu> f1 f2 sp) (map_sp\<^sub>\<mu> g1 g2 sp') =
  rel_sp\<^sub>\<mu> (BNF_Def.vimage2p f1 g1 R1) (BNF_Def.vimage2p f2 g2 R2) sp sp'"
by (tactic {*
  let val ks = 1 upto 2;
  in
    BNF_Tactics.unfold_thms_tac @{context}
      @{thms sp\<^sub>\<mu>.rel_compp sp\<^sub>\<mu>.rel_conversep sp\<^sub>\<mu>.rel_Grp vimage2p_Grp} THEN
    HEADGOAL (EVERY' [rtac iffI, rtac @{thm relcomppI}, rtac @{thm GrpI}, rtac refl, rtac CollectI,
      BNF_Util.CONJ_WRAP' (K (rtac @{thm subset_UNIV})) ks, rtac @{thm relcomppI}, atac,
      rtac @{thm conversepI}, rtac @{thm GrpI}, rtac refl, rtac CollectI,
      BNF_Util.CONJ_WRAP' (K (rtac @{thm subset_UNIV})) ks,
      REPEAT_DETERM o eresolve_tac @{thms relcomppE conversepE GrpE},
      hyp_subst_tac @{context}, atac])
  end
*})

lemma sp\<^sub>\<mu>_rel_self: "\<lbrakk>op = \<le> R1; op = \<le> R2\<rbrakk> \<Longrightarrow> rel_sp\<^sub>\<mu> R1 R2 x x"
  by (erule (1) predicate2D[OF sp\<^sub>\<mu>.rel_mono]) (simp only: sp\<^sub>\<mu>.rel_eq)

lemma sp\<^sub>\<nu>_comp_sp\<^sub>\<nu>_comp2: "sp o\<^sub>\<nu> sp' = sp o\<^sup>*\<^sub>\<nu> sp'"
  by (coinduction arbitrary: sp sp') (auto intro!: sp\<^sub>\<mu>_rel_self)


section {* Generalization to an Arbitrary BNF as Codomain *}

bnf_decl ('a, 'b) F (map: F)

definition \<theta> :: "('p,'a) F * 'b \<Rightarrow> ('p,'a * 'b) F" where
   "\<theta> xb = F id <id, \<lambda> a. (snd xb)> (fst xb)"

(* The strength laws for \<theta>: *)
lemma \<theta>_natural: "F id (map_pair f g) o \<theta> = \<theta> o map_pair (F id f) g"
  unfolding \<theta>_def F.map_comp comp_def id_apply convol_def map_pair_def split_beta fst_conv snd_conv ..

definition assl :: "'a * ('b * 'c) \<Rightarrow> ('a * 'b) * 'c" where
  "assl abc = ((fst abc, fst (snd abc)), snd (snd abc))"

lemma \<theta>_rid: "F id fst o \<theta> = fst"
  unfolding \<theta>_def F.map_comp F.map_id comp_def id_apply convol_def fst_conv sym[OF id_def] ..

lemma \<theta>_assl: "F id assl o \<theta> = \<theta> o map_pair \<theta> id o assl"
  unfolding assl_def \<theta>_def F.map_comp comp_def id_apply convol_def map_pair_def split fst_conv snd_conv ..

datatype_new ('a, 'b, 'c) spF\<^sub>\<mu> = GetF "'a \<Rightarrow> ('a, 'b, 'c) spF\<^sub>\<mu>" | PutF "('b,'c) F"
codatatype ('a, 'b) spF\<^sub>\<nu> = InF (outF: "('a, 'b, ('a, 'b) spF\<^sub>\<nu>) spF\<^sub>\<mu>")

codatatype 'b JF = Ctor (dtor: "('b, 'b JF) F")

(* Definition of run for an arbitrary final coalgebra as codomain: *)

primrec_new
  runF\<^sub>\<mu> :: "('a, 'b, ('a, 'b) spF\<^sub>\<nu>) spF\<^sub>\<mu> \<Rightarrow> 'a stream \<Rightarrow> (('b, ('a, 'b) spF\<^sub>\<nu>) F) \<times> 'a stream" 
where
  "runF\<^sub>\<mu> (GetF f) s = (runF\<^sub>\<mu> o f) (shd s) (stl s)"
| "runF\<^sub>\<mu> (PutF x) s = (x, s)"

primcorec runF\<^sub>\<nu> :: "('a, 'b) spF\<^sub>\<nu> \<Rightarrow> 'a stream \<Rightarrow> 'b JF" where
  "runF\<^sub>\<nu> sp s = (let (x, s) = runF\<^sub>\<mu> (outF sp) s in Ctor (F id (\<lambda> sp. runF\<^sub>\<nu> sp s) x))"

end
