(*  Title:      HOL/Hoare/Hoare.ML
    ID:         $Id$
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   1998 TUM

Derivation of the proof rules and, most importantly, the VCG tactic.
*)

(*** The proof rules ***)

Goalw [Valid_def] "p <= q ==> Valid p SKIP q";
by (Auto_tac);
qed "SkipRule";

Goalw [Valid_def] "p <= {s. (f s):q} ==> Valid p (Basic f) q";
by (Auto_tac);
qed "BasicRule";

Goalw [Valid_def] "[| Valid P c1 Q; Valid Q c2 R |] ==> Valid P (c1;c2) R";
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "SeqRule";

Goalw [Valid_def]
 "[| p <= {s. (s:b --> s:w) & (s~:b --> s:w')}; \
\    Valid w c1 q; Valid w' c2 q |] \
\ ==> Valid p (IF b THEN c1 ELSE c2 FI) q";
by (Asm_simp_tac 1);
by (Blast_tac 1);
qed "CondRule";

Goal "! s s'. Sem c s s' --> s : I Int b --> s' : I ==> \
\     ! s s'. s : I --> iter n b (Sem c) s s' --> s' : I & s' ~: b";
by (induct_tac "n" 1);
 by (Asm_simp_tac 1);
by (Simp_tac 1);
by (Blast_tac 1);
val lemma = result() RS spec RS spec RS mp RS mp;

Goalw [Valid_def]
 "[| p <= i; Valid (i Int b) c i;  i Int (-b) <= q |] \
\ ==> Valid p (WHILE b INV {i} DO c OD) q";
by (Asm_simp_tac 1);
by (Clarify_tac 1);
by (dtac lemma 1);
by (assume_tac 2);
by (Blast_tac 1);
by (Blast_tac 1);
qed "WhileRule";

(*** The tactics ***)

(*****************************************************************************)
(** The function Mset makes the theorem                                     **)
(** "?Mset <= {(x1,...,xn). ?P (x1,...,xn)} ==> ?Mset <= {s. ?P s}",        **)
(** where (x1,...,xn) are the variables of the particular program we are    **)
(** working on at the moment of the call. For instance, (found,x,y) are     **)
(** the variables of the Zero Search program.                               **)
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
fun mk_bodyC []      = Const ("()", unitT) 
  | mk_bodyC (x::xs) = if xs=[] then x 
               else let val (n, T) = dest_Free x ;
                        val z = mk_bodyC xs;
                        val T2 = case z of Free(_, T) => T
                                         | Const ("Pair", Type ("fun", [_, Type
                                            ("fun", [_, T])])) $ _ $ _ => T;
                 in Const ("Pair", [T, T2] ---> mk_prodT (T, T2)) $ x $ z end;

fun dest_Goal (Const ("Goal", _) $ P) = P;

(** maps a goal of the form:
        1. [| P |] ==> |- VARS x1 ... xn. {._.} _ {._.} or to [x1,...,xn]**) 
fun get_vars thm = let  val c = dest_Goal (concl_of (thm));
                        val d = Logic.strip_assums_concl c;
                        val Const _ $ pre $ _ $ _ = dest_Trueprop d;
      in mk_vars pre end;


(** Makes Collect with type **)
fun mk_CollectC trm = let val T as Type ("fun",[t,_]) = fastype_of trm 
                      in Collect_const t $ trm end;

fun inclt ty = Const ("op <=", [ty,ty] ---> boolT);

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
                   val cimpl = cterm_of (#sign (rep_thm thm)) impl
   in  prove_goalw_cterm [] cimpl (fn prems => 
                              [cut_facts_tac prems 1,Blast_tac 1]) end;

end;


(*****************************************************************************)
(** Simplifying:                                                            **)
(** Some useful lemmata, lists and simplification tactics to control which  **)
(** theorems are used to simplify at each moment, so that the original      **)
(** input does not suffer any unexpected transformation                     **)
(*****************************************************************************)

val Compl_Collect = prove_goal thy "-(Collect b) = {x. ~(b x)}"
    (fn _ => [Fast_tac 1]);

(**Simp_tacs**)

val before_set2pred_simp_tac =
  (simp_tac (HOL_basic_ss addsimps [Collect_conj_eq RS sym,Compl_Collect]));

val split_simp_tac = (simp_tac (HOL_basic_ss addsimps [split]));

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

fun set2pred i thm = let fun mk_string [] = ""
                           | mk_string (x::xs) = x^" "^mk_string xs;
                         val vars=get_vars(thm);
                         val var_string = mk_string (map (fst o dest_Free) vars);
      in ((before_set2pred_simp_tac i) THEN_MAYBE
          (EVERY [rtac subsetI i, 
                  rtac CollectI i,
                  dtac CollectD i,
                  (TRY(split_all_tac i)) THEN_MAYBE 
                  ((rename_tac var_string i) THEN
                   (full_simp_tac (HOL_basic_ss addsimps [split]) i)) ])) thm
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
  simp_tac (HOL_basic_ss addsimps [mem_Collect_eq,split])
  THEN_MAYBE' MaxSimpTac tac;

(** HoareRuleTac **)

fun WlpTac Mlem tac i = rtac SeqRule i THEN  HoareRuleTac Mlem tac false (i+1)
and HoareRuleTac Mlem tac pre_cond i st = st |>
        (*abstraction over st prevents looping*)
    ( (WlpTac Mlem tac i THEN HoareRuleTac Mlem tac pre_cond i)
      ORELSE
      (FIRST[rtac SkipRule i,
             EVERY[rtac BasicRule i,
                   rtac Mlem i,
                   split_simp_tac i],
             EVERY[rtac CondRule i,
                   HoareRuleTac Mlem tac false (i+2),
                   HoareRuleTac Mlem tac false (i+1)],
             EVERY[rtac WhileRule i,
                   BasicSimpTac tac (i+2),
                   HoareRuleTac Mlem tac true (i+1)] ] 
       THEN (if pre_cond then (BasicSimpTac tac i) else (rtac subset_refl i)) ));


(** tac:(int -> tactic) is the tactic the user chooses to solve or simplify **)
(** the final verification conditions                                       **)
 
fun hoare_tac tac i thm =
  let val Mlem = Mset(thm)
  in SELECT_GOAL(EVERY[HoareRuleTac Mlem tac true 1]) i thm end;
