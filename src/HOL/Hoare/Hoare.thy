(*  Title:      HOL/Hoare/Hoare.thy
    ID:         $Id$
    Author:     Leonor Prensa Nieto & Tobias Nipkow
    Copyright   1998 TUM

Sugared semantic embedding of Hoare logic.
Strictly speaking a shallow embedding (as implemented by Norbert Galm
following Mike Gordon) would suffice. Maybe the datatype com comes in useful
later.
*)

Hoare  = Main +

types
    'a bexp = 'a set
    'a assn = 'a set
    'a fexp = 'a =>'a

datatype
 'a com = Basic ('a fexp)         
   | Seq ('a com) ('a com)               ("(_;/ _)"      [61,60] 60)
   | Cond ('a bexp) ('a com) ('a com)    ("(1IF _/ THEN _ / ELSE _/ FI)"  [0,0,0] 61)
   | While ('a bexp) ('a assn) ('a com)  ("(1WHILE _/ INV {_} //DO _ /OD)"  [0,0,0] 61)
  
syntax
  "@assign"  :: id => 'b => 'a com        ("(2_ :=/ _)" [70,65] 61)
  "@annskip" :: 'a com                    ("SKIP")

translations
            "SKIP" == "Basic id"

types 'a sem = 'a => 'a => bool

consts iter :: nat => 'a bexp => 'a sem => 'a sem
primrec
"iter 0 b S = (%s s'. s ~: b & (s=s'))"
"iter (Suc n) b S = (%s s'. s : b & (? s''. S s s'' & iter n b S s'' s'))"

consts Sem :: 'a com => 'a sem
primrec
"Sem(Basic f) s s' = (s' = f s)"
"Sem(c1;c2) s s' = (? s''. Sem c1 s s'' & Sem c2 s'' s')"
"Sem(IF b THEN c1 ELSE c2 FI) s s' = ((s  : b --> Sem c1 s s') &
                                      (s ~: b --> Sem c2 s s'))"
"Sem(While b x c) s s' = (? n. iter n b (Sem c) s s')"

constdefs Valid :: ['a bexp, 'a com, 'a bexp] => bool
  "Valid p c q == !s s'. Sem c s s' --> s : p --> s' : q"


nonterminals
  vars

syntax
  ""		     :: "id => vars"		       ("_")
  "_vars" 	     :: "[id, vars] => vars"	       ("_ _")

syntax
 "@hoare_vars" :: [vars, 'a assn,'a com,'a assn] => bool
                 ("|- VARS _.// {_} // _ // {_}" [0,0,55,0] 50)
syntax ("" output)
 "@hoare"      :: ['a assn,'a com,'a assn] => bool
                 ("|- {_} // _ // {_}" [0,55,0] 50)

end

ML

(** parse translations **)

fun mk_abstuple []     body = absfree ("x", dummyT, body)
  | mk_abstuple [v]    body = absfree ((fst o dest_Free) v, dummyT, body)
  | mk_abstuple (v::w) body = Syntax.const "split" $
                              absfree ((fst o dest_Free) v, dummyT, mk_abstuple w body);

  
fun mk_fbody v e []      = Syntax.const "Unity"
  | mk_fbody v e [x]     = if v=x then e else x
  | mk_fbody v e (x::xs) = Syntax.const "Pair" $ (if v=x then e else x) $
                           mk_fbody v e xs;

fun mk_fexp v e xs = mk_abstuple xs (mk_fbody v e xs);


(* bexp_tr & assn_tr *)
(*all meta-variables for bexp except for TRUE are translated as if they
  were boolean expressions*)
  
fun bexp_tr (Const ("TRUE", _)) xs = Syntax.const "TRUE"
  | bexp_tr b xs = Syntax.const "Collect" $ mk_abstuple xs b;
  
fun assn_tr r xs = Syntax.const "Collect" $ mk_abstuple xs r;

(* com_tr *)
  
fun assign_tr [Free (V,_),E] xs = Syntax.const "Basic" $
                                      mk_fexp (Free(V,dummyT)) E xs
  | assign_tr ts _ = raise TERM ("assign_tr", ts);

fun com_tr (Const("@assign",_) $ Free (V,_) $ E) xs =
               assign_tr [Free (V,dummyT),E] xs
  | com_tr (Const ("Basic",_) $ f) xs = Syntax.const "Basic" $ f
  | com_tr (Const ("Seq",_) $ c1 $ c2) xs = Syntax.const "Seq" $
                                                 com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const ("Cond",_) $ b $ c1 $ c2) xs = Syntax.const "Cond" $
                                  bexp_tr b xs $ com_tr c1 xs $ com_tr c2 xs
  | com_tr (Const ("While",_) $ b $ I $ c) xs = Syntax.const "While" $
                                         bexp_tr b xs $ assn_tr I xs $ com_tr c xs
  | com_tr trm _ = trm;

(* triple_tr *)

fun vars_tr (x as Free _) = [x]
  | vars_tr (Const ("_vars", _) $ (x as Free _) $ vars) = x :: vars_tr vars
  | vars_tr t = raise TERM ("vars_tr", [t]);

fun hoare_vars_tr [vars, pre, prg, post] =
      let val xs = vars_tr vars
      in Syntax.const "Valid" $
           assn_tr pre xs $ com_tr prg xs $ assn_tr post xs
      end
  | hoare_vars_tr ts = raise TERM ("hoare_vars_tr", ts);
  


val parse_translation = [("@hoare_vars", hoare_vars_tr)];


(*****************************************************************************)

(*** print translations ***)

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
  
(* assn_tr' & bexp_tr'*)
  
fun assn_tr' (Const ("Collect",_) $ T) = dest_abstuple T
  | assn_tr' (Const ("op Int",_) $ (Const ("Collect",_) $ T1) $ 
                                   (Const ("Collect",_) $ T2)) =  
            Syntax.const "op Int" $ dest_abstuple T1 $ dest_abstuple T2
  | assn_tr' t = t;

fun bexp_tr' (Const ("Collect",_) $ T) = dest_abstuple T 
  | bexp_tr' t = t;

(*com_tr' *)

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
 
val print_translation = [("Valid", spec_tr')];
