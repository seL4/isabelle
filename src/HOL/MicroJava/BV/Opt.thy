(*  Title:      HOL/BCV/Opt.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

More about options
*)

header "More about Options"

theory Opt = Err:

constdefs
 le :: "'a ord => 'a option ord"
"le r o1 o2 == case o2 of None => o1=None |
                              Some y => (case o1 of None => True |
                                                    Some x => x <=_r y)"

 opt :: "'a set => 'a option set"
"opt A == insert None {x . ? y:A. x = Some y}"

 sup :: "'a ebinop => 'a option ebinop"
"sup f o1 o2 ==  
 case o1 of None => OK o2 | Some x => (case o2 of None => OK o1
                                              | Some y => (case f x y of Err => Err | OK z => OK (Some z)))"

 esl :: "'a esl => 'a option esl"
"esl == %(A,r,f). (opt A, le r, sup f)"

lemma unfold_le_opt:
  "o1 <=_(le r) o2 = 
  (case o2 of None => o1=None | 
              Some y => (case o1 of None => True | Some x => x <=_r y))"
apply (unfold lesub_def le_def)
apply (rule refl)
done

lemma le_opt_refl:
  "order r ==> o1 <=_(le r) o1"
by (simp add: unfold_le_opt split: option.split)

lemma le_opt_trans [rule_format]:
  "order r ==> 
   o1 <=_(le r) o2 --> o2 <=_(le r) o3 --> o1 <=_(le r) o3"
apply (simp add: unfold_le_opt split: option.split)
apply (blast intro: order_trans)
done

lemma le_opt_antisym [rule_format]:
  "order r ==> o1 <=_(le r) o2 --> o2 <=_(le r) o1 --> o1=o2"
apply (simp add: unfold_le_opt split: option.split)
apply (blast intro: order_antisym)
done

lemma order_le_opt [intro!,simp]:
  "order r ==> order(le r)"
apply (subst order_def)
apply (blast intro: le_opt_refl le_opt_trans le_opt_antisym)
done 

lemma None_bot [iff]: 
  "None <=_(le r) ox"
apply (unfold lesub_def le_def)
apply (simp split: option.split)
done 

lemma Some_le [iff]:
  "(Some x <=_(le r) ox) = (? y. ox = Some y & x <=_r y)"
apply (unfold lesub_def le_def)
apply (simp split: option.split)
done 

lemma le_None [iff]:
  "(ox <=_(le r) None) = (ox = None)";
apply (unfold lesub_def le_def)
apply (simp split: option.split)
done 


lemma OK_None_bot [iff]:
  "OK None <=_(Err.le (le r)) x"
  by (simp add: lesub_def Err.le_def le_def split: option.split err.split)

lemma sup_None1 [iff]:
  "x +_(sup f) None = OK x"
  by (simp add: plussub_def sup_def split: option.split)

lemma sup_None2 [iff]:
  "None +_(sup f) x = OK x"
  by (simp add: plussub_def sup_def split: option.split)


lemma None_in_opt [iff]:
  "None : opt A"
by (simp add: opt_def)

lemma Some_in_opt [iff]:
  "(Some x : opt A) = (x:A)"
apply (unfold opt_def)
apply auto
done 


lemma semilat_opt:
  "!!L. err_semilat L ==> err_semilat (Opt.esl L)"
proof (unfold Opt.esl_def Err.sl_def, simp add: split_tupled_all)
  
  fix A r f
  assume s: "semilat (err A, Err.le r, lift2 f)"
 
  let ?A0 = "err A"
  let ?r0 = "Err.le r"
  let ?f0 = "lift2 f"

  from s
  obtain
    ord: "order ?r0" and
    clo: "closed ?A0 ?f0" and
    ub1: "\<forall>x\<in>?A0. \<forall>y\<in>?A0. x <=_?r0 x +_?f0 y" and
    ub2: "\<forall>x\<in>?A0. \<forall>y\<in>?A0. y <=_?r0 x +_?f0 y" and
    lub: "\<forall>x\<in>?A0. \<forall>y\<in>?A0. \<forall>z\<in>?A0. x <=_?r0 z \<and> y <=_?r0 z \<longrightarrow> x +_?f0 y <=_?r0 z"
    by (unfold semilat_def) simp

  let ?A = "err (opt A)" 
  let ?r = "Err.le (Opt.le r)"
  let ?f = "lift2 (Opt.sup f)"

  from ord
  have "order ?r"
    by simp

  moreover

  have "closed ?A ?f"
  proof (unfold closed_def, intro strip)
    fix x y    
    assume x: "x : ?A" 
    assume y: "y : ?A" 

    { fix a b
      assume ab: "x = OK a" "y = OK b"
      
      with x 
      have a: "!!c. a = Some c ==> c : A"
        by (clarsimp simp add: opt_def)

      from ab y
      have b: "!!d. b = Some d ==> d : A"
        by (clarsimp simp add: opt_def)
      
      { fix c d assume "a = Some c" "b = Some d"
        with ab x y
        have "c:A & d:A"
          by (simp add: err_def opt_def Bex_def)
        with clo
        have "f c d : err A"
          by (simp add: closed_def plussub_def err_def lift2_def)
        moreover
        fix z assume "f c d = OK z"
        ultimately
        have "z : A" by simp
      } note f_closed = this    

      have "sup f a b : ?A"
      proof (cases a)
        case None
        thus ?thesis
          by (simp add: sup_def opt_def) (cases b, simp, simp add: b Bex_def)
      next
        case Some
        thus ?thesis
          by (auto simp add: sup_def opt_def Bex_def a b f_closed split: err.split option.split)
      qed
    }

    thus "x +_?f y : ?A"
      by (simp add: plussub_def lift2_def split: err.split)
  qed
    
  moreover

  { fix a b c 
    assume "a \<in> opt A" "b \<in> opt A" "a +_(sup f) b = OK c" 
    moreover
    from ord have "order r" by simp
    moreover
    { fix x y z
      assume "x \<in> A" "y \<in> A" 
      hence "OK x \<in> err A \<and> OK y \<in> err A" by simp
      with ub1 ub2
      have "(OK x) <=_(Err.le r) (OK x) +_(lift2 f) (OK y) \<and>
            (OK y) <=_(Err.le r) (OK x) +_(lift2 f) (OK y)"
        by blast
      moreover
      assume "x +_f y = OK z"
      ultimately
      have "x <=_r z \<and> y <=_r z"
        by (auto simp add: plussub_def lift2_def Err.le_def lesub_def)
    }
    ultimately
    have "a <=_(le r) c \<and> b <=_(le r) c"
      by (auto simp add: sup_def le_def lesub_def plussub_def 
               dest: order_refl split: option.splits err.splits)
  }
     
  hence "(\<forall>x\<in>?A. \<forall>y\<in>?A. x <=_?r x +_?f y) \<and> (\<forall>x\<in>?A. \<forall>y\<in>?A. y <=_?r x +_?f y)"
    by (auto simp add: lesub_def plussub_def Err.le_def lift2_def split: err.split)

  moreover

  have "\<forall>x\<in>?A. \<forall>y\<in>?A. \<forall>z\<in>?A. x <=_?r z \<and> y <=_?r z \<longrightarrow> x +_?f y <=_?r z"
  proof (intro strip, elim conjE)
    fix x y z
    assume xyz: "x : ?A" "y : ?A" "z : ?A"
    assume xz: "x <=_?r z"
    assume yz: "y <=_?r z"

    { fix a b c
      assume ok: "x = OK a" "y = OK b" "z = OK c"

      { fix d e g
        assume some: "a = Some d" "b = Some e" "c = Some g"
        
        with ok xyz
        obtain "OK d:err A" "OK e:err A" "OK g:err A"
          by simp
        with lub
        have "[| (OK d) <=_(Err.le r) (OK g); (OK e) <=_(Err.le r) (OK g) |]
          ==> (OK d) +_(lift2 f) (OK e) <=_(Err.le r) (OK g)"
          by blast
        hence "[| d <=_r g; e <=_r g |] ==> \<exists>y. d +_f e = OK y \<and> y <=_r g"
          by simp

        with ok some xyz xz yz
        have "x +_?f y <=_?r z"
          by (auto simp add: sup_def le_def lesub_def lift2_def plussub_def Err.le_def)
      } note this [intro!]

      from ok xyz xz yz
      have "x +_?f y <=_?r z"
        by - (cases a, simp, cases b, simp, cases c, simp, blast)
    }
    
    with xyz xz yz
    show "x +_?f y <=_?r z"
      by - (cases x, simp, cases y, simp, cases z, simp+)
  qed

  ultimately

  show "semilat (?A,?r,?f)"
    by (unfold semilat_def) simp
qed 

lemma top_le_opt_Some [iff]: 
  "top (le r) (Some T) = top r T"
apply (unfold top_def)
apply (rule iffI)
 apply blast
apply (rule allI)
apply (case_tac "x")
apply simp+
done 

lemma Top_le_conv:
  "[| order r; top r T |] ==> (T <=_r x) = (x = T)"
apply (unfold top_def)
apply (blast intro: order_antisym)
done 


lemma acc_le_optI [intro!]:
  "acc r ==> acc(le r)"
apply (unfold acc_def lesub_def le_def lesssub_def)
apply (simp add: wf_eq_minimal split: option.split)
apply clarify
apply (case_tac "? a. Some a : Q")
 apply (erule_tac x = "{a . Some a : Q}" in allE)
 apply blast
apply (case_tac "x")
 apply blast
apply blast
done 

lemma option_map_in_optionI:
  "[| ox : opt S; !x:S. ox = Some x --> f x : S |] 
  ==> option_map f ox : opt S";
apply (unfold option_map_def)
apply (simp split: option.split)
apply blast
done 

end
