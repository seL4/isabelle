(*  Title:      HOL/Hoare/HoareAbort.thy
    ID:         $Id$
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   2003 TUM

Like Hoare.thy, but with an Abort statement for modelling run time errors.
*)

theory HoareAbort  imports Main
begin

types
    'a bexp = "'a set"
    'a assn = "'a set"

datatype
 'a com = Basic "'a \<Rightarrow> 'a"
   | Abort
   | Seq "'a com" "'a com"               ("(_;/ _)"      [61,60] 60)
   | Cond "'a bexp" "'a com" "'a com"    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
   | While "'a bexp" "'a assn" "'a com"  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)
  
syntax
  "@assign"  :: "id => 'b => 'a com"        ("(2_ :=/ _)" [70,65] 61)
  "@annskip" :: "'a com"                    ("SKIP")

translations
            "SKIP" == "Basic id"

types 'a sem = "'a option => 'a option => bool"

consts iter :: "nat => 'a bexp => 'a sem => 'a sem"
primrec
"iter 0 b S = (\<lambda>s s'. s \<notin> Some ` b \<and> s=s')"
"iter (Suc n) b S =
  (\<lambda>s s'. s \<in> Some ` b \<and> (\<exists>s''. S s s'' \<and> iter n b S s'' s'))"

consts Sem :: "'a com => 'a sem"
primrec
"Sem(Basic f) s s' = (case s of None \<Rightarrow> s' = None | Some t \<Rightarrow> s' = Some(f t))"
"Sem Abort s s' = (s' = None)"
"Sem(c1;c2) s s' = (\<exists>s''. Sem c1 s s'' \<and> Sem c2 s'' s')"
"Sem(IF b THEN c1 ELSE c2 FI) s s' =
 (case s of None \<Rightarrow> s' = None
  | Some t \<Rightarrow> ((t \<in> b \<longrightarrow> Sem c1 s s') \<and> (t \<notin> b \<longrightarrow> Sem c2 s s')))"
"Sem(While b x c) s s' =
 (if s = None then s' = None else \<exists>n. iter n b (Sem c) s s')"

constdefs Valid :: "'a bexp \<Rightarrow> 'a com \<Rightarrow> 'a bexp \<Rightarrow> bool"
  "Valid p c q == \<forall>s s'. Sem c s s' \<longrightarrow> s : Some ` p \<longrightarrow> s' : Some ` q"


syntax
 "@hoare_vars" :: "[idts, 'a assn,'a com,'a assn] => bool"
                 ("VARS _// {_} // _ // {_}" [0,0,55,0] 50)
syntax ("" output)
 "@hoare"      :: "['a assn,'a com,'a assn] => bool"
                 ("{_} // _ // {_}" [0,55,0] 50)

(** parse translations **)

ML{*

local
fun free a = Free(a,dummyT)
fun abs((a,T),body) =
  let val a = absfree(a, dummyT, body)
  in if T = Bound 0 then a else Const(Syntax.constrainAbsC,dummyT) $ a $ T end
in

fun mk_abstuple [x] body = abs (x, body)
  | mk_abstuple (x::xs) body =
      Syntax.const "split" $ abs (x, mk_abstuple xs body);

fun mk_fbody a e [x as (b,_)] = if a=b then e else free b
  | mk_fbody a e ((b,_)::xs) =
      Syntax.const "Pair" $ (if a=b then e else free b) $ mk_fbody a e xs;

fun mk_fexp a e xs = mk_abstuple xs (mk_fbody a e xs)
end
*}

(* bexp_tr & assn_tr *)
(*all meta-variables for bexp except for TRUE are translated as if they
  were boolean expressions*)
ML{*
fun bexp_tr (Const ("TRUE", _)) xs = Syntax.const "TRUE"
  | bexp_tr b xs = Syntax.const "Collect" $ mk_abstuple xs b;
  
fun assn_tr r xs = Syntax.const "Collect" $ mk_abstuple xs r;
*}
(* com_tr *)
ML{*
fun com_tr (Const("@assign",_) $ Free (a,_) $ e) xs =
      Syntax.const "Basic" $ mk_fexp a e xs
  | com_tr (Const ("Basic",_) $ f) xs = Syntax.const "Basic" $ f
  | com_tr (Const ("Seq",_) $ c1 $ c2) xs =
      Syntax.const "Seq" $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const ("Cond",_) $ b $ c1 $ c2) xs =
      Syntax.const "Cond" $ bexp_tr b xs $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const ("While",_) $ b $ I $ c) xs =
      Syntax.const "While" $ bexp_tr b xs $ assn_tr I xs $ com_tr c xs
  | com_tr t _ = t (* if t is just a Free/Var *)
*}

(* triple_tr *)  (* FIXME does not handle "_idtdummy" *)
ML{*
local

fun var_tr(Free(a,_)) = (a,Bound 0) (* Bound 0 = dummy term *)
  | var_tr(Const ("_constrain", _) $ (Free (a,_)) $ T) = (a,T);

fun vars_tr (Const ("_idts", _) $ idt $ vars) = var_tr idt :: vars_tr vars
  | vars_tr t = [var_tr t]

in
fun hoare_vars_tr [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in Syntax.const "Valid" $
         assn_tr pre xs $ com_tr prg xs $ assn_tr post xs
      end
  | hoare_vars_tr ts = raise TERM ("hoare_vars_tr", ts);
end
*}

parse_translation {* [("@hoare_vars", hoare_vars_tr)] *}


(*****************************************************************************)

(*** print translations ***)
ML{*
fun dest_abstuple (Const ("split",_) $ (Abs(v,_, body))) =
                            subst_bound (Syntax.free v, dest_abstuple body)
  | dest_abstuple (Abs(v,_, body)) = subst_bound (Syntax.free v, body)
  | dest_abstuple trm = trm;

fun abs2list (Const ("split",_) $ (Abs(x,T,t))) = Free (x, T)::abs2list t
  | abs2list (Abs(x,T,t)) = [Free (x, T)]
  | abs2list _ = [];

fun mk_ts (Const ("split",_) $ (Abs(x,_,t))) = mk_ts t
  | mk_ts (Abs(x,_,t)) = mk_ts t
  | mk_ts (Const ("Pair",_) $ a $ b) = a::(mk_ts b)
  | mk_ts t = [t];

fun mk_vts (Const ("split",_) $ (Abs(x,_,t))) = 
           ((Syntax.free x)::(abs2list t), mk_ts t)
  | mk_vts (Abs(x,_,t)) = ([Syntax.free x], [t])
  | mk_vts t = raise Match;
  
fun find_ch [] i xs = (false, (Syntax.free "not_ch",Syntax.free "not_ch" ))
  | find_ch ((v,t)::vts) i xs = if t=(Bound i) then find_ch vts (i-1) xs
              else (true, (v, subst_bounds (xs,t)));
  
fun is_f (Const ("split",_) $ (Abs(x,_,t))) = true
  | is_f (Abs(x,_,t)) = true
  | is_f t = false;
*}

(* assn_tr' & bexp_tr'*)
ML{*  
fun assn_tr' (Const ("Collect",_) $ T) = dest_abstuple T
  | assn_tr' (Const ("op Int",_) $ (Const ("Collect",_) $ T1) $ 
                                   (Const ("Collect",_) $ T2)) =  
            Syntax.const "op Int" $ dest_abstuple T1 $ dest_abstuple T2
  | assn_tr' t = t;

fun bexp_tr' (Const ("Collect",_) $ T) = dest_abstuple T 
  | bexp_tr' t = t;
*}

(*com_tr' *)
ML{*
fun mk_assign f =
  let val (vs, ts) = mk_vts f;
      val (ch, which) = find_ch (vs~~ts) ((length vs)-1) (rev vs)
  in if ch then Syntax.const "@assign" $ fst(which) $ snd(which)
     else Syntax.const "@skip" end;

fun com_tr' (Const ("Basic",_) $ f) = if is_f f then mk_assign f
                                           else Syntax.const "Basic" $ f
  | com_tr' (Const ("Seq",_) $ c1 $ c2) = Syntax.const "Seq" $
                                                 com_tr' c1 $ com_tr' c2
  | com_tr' (Const ("Cond",_) $ b $ c1 $ c2) = Syntax.const "Cond" $
                                           bexp_tr' b $ com_tr' c1 $ com_tr' c2
  | com_tr' (Const ("While",_) $ b $ I $ c) = Syntax.const "While" $
                                               bexp_tr' b $ assn_tr' I $ com_tr' c
  | com_tr' t = t;


fun spec_tr' [p, c, q] =
  Syntax.const "@hoare" $ assn_tr' p $ com_tr' c $ assn_tr' q
*}

print_translation {* [("Valid", spec_tr')] *}

(*** The proof rules ***)

lemma SkipRule: "p \<subseteq> q \<Longrightarrow> Valid p (Basic id) q"
by (auto simp:Valid_def)

lemma BasicRule: "p \<subseteq> {s. f s \<in> q} \<Longrightarrow> Valid p (Basic f) q"
by (auto simp:Valid_def)

lemma SeqRule: "Valid P c1 Q \<Longrightarrow> Valid Q c2 R \<Longrightarrow> Valid P (c1;c2) R"
by (auto simp:Valid_def)

lemma CondRule:
 "p \<subseteq> {s. (s \<in> b \<longrightarrow> s \<in> w) \<and> (s \<notin> b \<longrightarrow> s \<in> w')}
  \<Longrightarrow> Valid w c1 q \<Longrightarrow> Valid w' c2 q \<Longrightarrow> Valid p (Cond b c1 c2) q"
by (fastsimp simp:Valid_def image_def)

lemma iter_aux:
 "! s s'. Sem c s s' \<longrightarrow> s \<in> Some ` (I \<inter> b) \<longrightarrow> s' \<in> Some ` I \<Longrightarrow>
  (\<And>s s'. s \<in> Some ` I \<Longrightarrow> iter n b (Sem c) s s' \<Longrightarrow> s' \<in> Some ` (I \<inter> -b))";
apply(unfold image_def)
apply(induct n)
 apply clarsimp
apply(simp (no_asm_use))
apply blast
done

lemma WhileRule:
 "p \<subseteq> i \<Longrightarrow> Valid (i \<inter> b) c i \<Longrightarrow> i \<inter> (-b) \<subseteq> q \<Longrightarrow> Valid p (While b i c) q"
apply(simp add:Valid_def)
apply(simp (no_asm) add:image_def)
apply clarify
apply(drule iter_aux)
  prefer 2 apply assumption
 apply blast
apply blast
done

lemma AbortRule: "p \<subseteq> {s. False} \<Longrightarrow> Valid p Abort q"
by(auto simp:Valid_def)


subsection {* Derivation of the proof rules and, most importantly, the VCG tactic *}

ML {*
(*** The tactics ***)

(*****************************************************************************)
(** The function Mset makes the theorem                                     **)
(** "?Mset <= {(x1,...,xn). ?P (x1,...,xn)} ==> ?Mset <= {s. ?P s}",        **)
(** where (x1,...,xn) are the variables of the particular program we are    **)
(** working on at the moment of the call                                    **)
(*****************************************************************************)

local open HOLogic in

(** maps (%x1 ... xn. t) to [x1,...,xn] **)
fun abs2list (Const ("split",_) $ (Abs(x,T,t))) = Free (x, T)::abs2list t
  | abs2list (Abs(x,T,t)) = [Free (x, T)]
  | abs2list _ = [];

(** maps {(x1,...,xn). t} to [x1,...,xn] **)
fun mk_vars (Const ("Collect",_) $ T) = abs2list T
  | mk_vars _ = [];

(** abstraction of body over a tuple formed from a list of free variables. 
Types are also built **)
fun mk_abstupleC []     body = absfree ("x", unitT, body)
  | mk_abstupleC (v::w) body = let val (n,T) = dest_Free v
                               in if w=[] then absfree (n, T, body)
        else let val z  = mk_abstupleC w body;
                 val T2 = case z of Abs(_,T,_) => T
                        | Const (_, Type (_,[_, Type (_,[T,_])])) $ _ => T;
       in Const ("split", (T --> T2 --> boolT) --> mk_prodT (T,T2) --> boolT) 
          $ absfree (n, T, z) end end;

(** maps [x1,...,xn] to (x1,...,xn) and types**)
fun mk_bodyC []      = HOLogic.unit
  | mk_bodyC (x::xs) = if xs=[] then x 
               else let val (n, T) = dest_Free x ;
                        val z = mk_bodyC xs;
                        val T2 = case z of Free(_, T) => T
                                         | Const ("Pair", Type ("fun", [_, Type
                                            ("fun", [_, T])])) $ _ $ _ => T;
                 in Const ("Pair", [T, T2] ---> mk_prodT (T, T2)) $ x $ z end;

(** maps a goal of the form:
        1. [| P |] ==> VARS x1 ... xn {._.} _ {._.} or to [x1,...,xn]**) 
fun get_vars thm = let  val c = Logic.unprotect (concl_of (thm));
                        val d = Logic.strip_assums_concl c;
                        val Const _ $ pre $ _ $ _ = dest_Trueprop d;
      in mk_vars pre end;


(** Makes Collect with type **)
fun mk_CollectC trm = let val T as Type ("fun",[t,_]) = fastype_of trm 
                      in Collect_const t $ trm end;

fun inclt ty = Const (@{const_name HOL.less_eq}, [ty,ty] ---> boolT);

(** Makes "Mset <= t" **)
fun Mset_incl t = let val MsetT = fastype_of t 
                 in mk_Trueprop ((inclt MsetT) $ Free ("Mset", MsetT) $ t) end;


fun Mset thm = let val vars = get_vars(thm);
                   val varsT = fastype_of (mk_bodyC vars);
                   val big_Collect = mk_CollectC (mk_abstupleC vars 
                         (Free ("P",varsT --> boolT) $ mk_bodyC vars));
                   val small_Collect = mk_CollectC (Abs("x",varsT,
                           Free ("P",varsT --> boolT) $ Bound 0));
                   val impl = implies $ (Mset_incl big_Collect) $ 
                                          (Mset_incl small_Collect);
   in Goal.prove (ProofContext.init (Thm.theory_of_thm thm)) ["Mset", "P"] [] impl (K (CLASET' blast_tac 1)) end;

end;
*}

(*****************************************************************************)
(** Simplifying:                                                            **)
(** Some useful lemmata, lists and simplification tactics to control which  **)
(** theorems are used to simplify at each moment, so that the original      **)
(** input does not suffer any unexpected transformation                     **)
(*****************************************************************************)

lemma Compl_Collect: "-(Collect b) = {x. ~(b x)}"
  by blast


ML {*
(**Simp_tacs**)

val before_set2pred_simp_tac =
  (simp_tac (HOL_basic_ss addsimps [@{thm Collect_conj_eq} RS sym, @{thm Compl_Collect}]));

val split_simp_tac = (simp_tac (HOL_basic_ss addsimps [split_conv]));

(*****************************************************************************)
(** set2pred transforms sets inclusion into predicates implication,         **)
(** maintaining the original variable names.                                **)
(** Ex. "{x. x=0} <= {x. x <= 1}" -set2pred-> "x=0 --> x <= 1"              **)
(** Subgoals containing intersections (A Int B) or complement sets (-A)     **)
(** are first simplified by "before_set2pred_simp_tac", that returns only   **)
(** subgoals of the form "{x. P x} <= {x. Q x}", which are easily           **)
(** transformed.                                                            **)
(** This transformation may solve very easy subgoals due to a ligth         **)
(** simplification done by (split_all_tac)                                  **)
(*****************************************************************************)

fun set2pred i thm =
  let val var_names = map (fst o dest_Free) (get_vars thm) in
    ((before_set2pred_simp_tac i) THEN_MAYBE
      (EVERY [rtac subsetI i, 
              rtac CollectI i,
              dtac CollectD i,
              (TRY(split_all_tac i)) THEN_MAYBE
              ((rename_tac var_names i) THEN
               (full_simp_tac (HOL_basic_ss addsimps [split_conv]) i)) ])) thm
  end;

(*****************************************************************************)
(** BasicSimpTac is called to simplify all verification conditions. It does **)
(** a light simplification by applying "mem_Collect_eq", then it calls      **)
(** MaxSimpTac, which solves subgoals of the form "A <= A",                 **)
(** and transforms any other into predicates, applying then                 **)
(** the tactic chosen by the user, which may solve the subgoal completely.  **)
(*****************************************************************************)

fun MaxSimpTac tac = FIRST'[rtac subset_refl, set2pred THEN_MAYBE' tac];

fun BasicSimpTac tac =
  simp_tac
    (HOL_basic_ss addsimps [mem_Collect_eq,split_conv] addsimprocs [record_simproc])
  THEN_MAYBE' MaxSimpTac tac;

(** HoareRuleTac **)

fun WlpTac Mlem tac i =
  rtac @{thm SeqRule} i THEN  HoareRuleTac Mlem tac false (i+1)
and HoareRuleTac Mlem tac pre_cond i st = st |>
        (*abstraction over st prevents looping*)
    ( (WlpTac Mlem tac i THEN HoareRuleTac Mlem tac pre_cond i)
      ORELSE
      (FIRST[rtac @{thm SkipRule} i,
             rtac @{thm AbortRule} i,
             EVERY[rtac @{thm BasicRule} i,
                   rtac Mlem i,
                   split_simp_tac i],
             EVERY[rtac @{thm CondRule} i,
                   HoareRuleTac Mlem tac false (i+2),
                   HoareRuleTac Mlem tac false (i+1)],
             EVERY[rtac @{thm WhileRule} i,
                   BasicSimpTac tac (i+2),
                   HoareRuleTac Mlem tac true (i+1)] ] 
       THEN (if pre_cond then (BasicSimpTac tac i) else rtac subset_refl i) ));


(** tac:(int -> tactic) is the tactic the user chooses to solve or simplify **)
(** the final verification conditions                                       **)
 
fun hoare_tac tac i thm =
  let val Mlem = Mset(thm)
  in SELECT_GOAL(EVERY[HoareRuleTac Mlem tac true 1]) i thm end;
*}

method_setup vcg = {*
  Method.no_args (Method.SIMPLE_METHOD' (hoare_tac (K all_tac))) *}
  "verification condition generator"

method_setup vcg_simp = {*
  Method.ctxt_args (fn ctxt =>
    Method.SIMPLE_METHOD' (hoare_tac (asm_full_simp_tac (local_simpset_of ctxt)))) *}
  "verification condition generator plus simplification"

(* Special syntax for guarded statements and guarded array updates: *)

syntax
  guarded_com :: "bool \<Rightarrow> 'a com \<Rightarrow> 'a com"  ("(2_ \<rightarrow>/ _)" 71)
  array_update :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a com"  ("(2_[_] :=/ _)" [70,65] 61)
translations
  "P \<rightarrow> c" == "IF P THEN c ELSE Abort FI"
  "a[i] := v" => "(i < CONST length a) \<rightarrow> (a := list_update a i v)"
  (* reverse translation not possible because of duplicate "a" *)

text{* Note: there is no special syntax for guarded array access. Thus
you must write @{text"j < length a \<rightarrow> a[i] := a!j"}. *}

end
