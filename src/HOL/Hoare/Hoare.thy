(*  Title: 	HOL/Hoare/Hoare.thy
    ID:         $Id$
    Author: 	Norbert Galm & Tobias Nipkow
    Copyright   1995 TUM

Sugared semantic embedding of Hoare logic.
*)

Hoare = Arith +

types
  'a prog			(* program syntax *)
  pvar = "nat"			(* encoding of program variables ( < 26! ) *)
  'a state = "pvar => 'a"	(* program state *)
  'a exp ="'a state => 'a"	(* denotation of expressions *)
  'a bexp = "'a state => bool"  (* denotation of boolean expressions *)
  'a com = "'a state => 'a state => bool" (* denotation of programs *)

syntax
  "@Skip"       :: 'a prog				("SKIP")
  "@Assign"	:: [id, 'a] => 'a prog		("_ := _")
  "@Seq"	:: ['a prog, 'a prog] => 'a prog	("_;//_" [0,1000] 999)
  "@If"		:: [bool, 'a prog, 'a prog] => 'a prog
                   ("IF _//THEN//  (_)//ELSE//  (_)//END")
  "@While"	:: [bool, bool, 'a prog] => 'a prog
                   ("WHILE _//DO {_}//  (_)//END")

  "@Spec"	:: [bool, 'a prog, bool] => bool	("{_}//_//{_}")

consts
  (* semantics *)

  Skip		:: 'a com
  Assign	:: [pvar, 'a exp] => 'a com
  Seq		:: ['a com, 'a com] => 'a com
  Cond		:: ['a bexp, 'a com, 'a com] => 'a com
  While		:: ['a bexp, 'a bexp, 'a com] => 'a com
  Iter		:: [nat, 'a bexp, 'a com] => 'a com

  Spec		:: ['a bexp, 'a com, 'a bexp] => bool

defs
  (* denotational semantics *)

  SkipDef	"Skip s s' == (s=s')"
  AssignDef	"Assign v e s s' == (s' = (%x.if x=v then e(s) else s(x)))"
  SeqDef	"Seq c c' s s' == ? s''. c s s'' & c' s'' s'"
  CondDef	"Cond b c c' s s' == (b(s) --> c s s') & (~b s --> c' s s')"
  WhileDef	"While b inv c s s' == ? n. Iter n b c s s'"

  IterDef	"Iter n b c == nat_rec n (%s s'.~b(s) & (s=s'))
		           (%n_rec iter_rec.%s s'.b(s) & Seq c iter_rec s s')"

  SpecDef	"Spec p c q == !s s'. c s s' --> p s --> q s'"

end

ML


(*** term manipulation ***)

(* name_in_term:bool (name:string,trm:term) bestimmt, ob in trm der Name name als Konstante,
   freie Var., scheme-Variable oder als Name fuer eine Lambda-Abstraktion vorkommt *)

fun name_in_term (name,Const (s,t))	=(name=s)
  | name_in_term (name,Free (s,t))	=(name=s)
  | name_in_term (name,Var ((s,i),t))	=(name=s ^ makestring i)
  | name_in_term (name,Abs (s,t,trm))	=(name=s) orelse (name_in_term (name,trm))
  | name_in_term (name,trm1 $ trm2)	=(name_in_term (name,trm1)) orelse (name_in_term (name,trm2))
  | name_in_term (_,_)			=false;

(* variant_name:string (name:string,trm:term) liefert einen von name abgewandelten Namen (durch Anhaengen
   von genuegend vielen "_"), der nicht in trm vorkommt. Im Gegensatz zu variant_abs beruecktsichtigt es
   auch Namen von scheme-Variablen und von Lambda-Abstraktionen in trm *)

fun variant_name (name,trm)	=if name_in_term (name,trm)
					then variant_name (name ^ "_",trm)
					else name;

(* subst_term:term (von:term,nach:term,trm:term) liefert den Term, der aus
trm entsteht, wenn alle Teilterme, die gleich von sind, durch nach ersetzt
wurden *)

fun subst_term (von,nach,Abs (s,t,trm))	=if von=Abs (s,t,trm)
						then nach
						else Abs (s,t,subst_term (von,nach,trm))
  | subst_term (von,nach,trm1 $ trm2)	=if von=trm1 $ trm2
						then nach
						else subst_term (von,nach,trm1) $ subst_term (von,nach,trm2)
  | subst_term (von,nach,trm)		=if von=trm
						then nach
						else trm;


(* Translation between program vars ("a" - "z") and their encoding as
   natural numbers: "a" <==> 0, "b" <==> Suc(0), ..., "z" <==> 25 *)

fun is_pvarID s	= size s=1 andalso "a"<=s andalso s<="z";

fun pvarID2pvar s =
  let fun rest2pvar (i,arg) =
            if i=0 then arg else rest2pvar(i-1, Syntax.const "Suc" $ arg)
  in rest2pvar(ord s - ord "a", Syntax.const "0") end;

fun pvar2pvarID trm	=
	let
		fun rest2pvarID (Const("0",_),i)		=chr (i + ord "a")
		  | rest2pvarID (Const("Suc",_) $ trm,i)	=rest2pvarID (trm,i+1)
	in
		rest2pvarID (trm,0)
	end;


(*** parse translations: syntax -> semantics ***)

(* term_tr:term (name:string,trm:term) ersetzt in trm alle freien Variablen, die eine pvarID
   darstellen, durch name $ pvarID2pvar(pvarID). Beispiel:
   bei name="s" und dem Term "a=b & a=X" wird der Term "s(0)=s(Suc(0)) & s(0)=X" geliefert *)

fun term_tr (name,Free (s,t)) = if is_pvarID s
				then Syntax.free name $ pvarID2pvar s
				else Free (s,t)
  | term_tr (name,Abs (s,t,trm)) = Abs (s,t,term_tr (name,trm))
  | term_tr (name,trm1 $ trm2)	= term_tr (name,trm1) $ term_tr (name,trm2)
  | term_tr (name,trm) = trm;

fun bool_tr B =
  let val name = variant_name("s",B)
  in Abs (name,dummyT,abstract_over (Syntax.free name,term_tr (name,B))) end;

fun exp_tr E =
  let val name = variant_name("s",E)
  in Abs (name,dummyT,abstract_over (Syntax.free name,term_tr (name,E))) end;

fun prog_tr (Const ("@Skip",_))	= Syntax.const "Skip"
  | prog_tr (Const ("@Assign",_) $ Free (V,_) $ E) =
      if is_pvarID V
      then Syntax.const "Assign" $ pvarID2pvar V $ exp_tr E
      else error("Not a valid program variable: " ^ quote V)
  | prog_tr (Const ("@Seq",_) $ C $ C')	=
      Syntax.const "Seq" $ prog_tr C $ prog_tr C'
  | prog_tr (Const ("@If",_) $ B $ C $ C') =
      Syntax.const "Cond" $ bool_tr B $ prog_tr C $ prog_tr C'
  | prog_tr (Const ("@While",_) $ B $ INV $ C) =
      Syntax.const "While" $ bool_tr B $ bool_tr INV $ prog_tr C;

fun spec_tr [P,C,Q] = Syntax.const "Spec" $ bool_tr P $ prog_tr C $ bool_tr Q;

val parse_translation = [("@Spec",spec_tr)];


(*** print translations: semantics -> syntax ***)

(* term_tr':term (name:string,trm:term) ersetzt in trm alle Vorkommen von name $ pvar durch
   entsprechende freie Variablen, welche die pvarID zu pvar darstellen. Beispiel:
	bei name="s" und dem Term "s(0)=s(Suc(0)) & s(0)=X" wird der Term "a=b & a=X" geliefert *)

fun term_tr' (name,Free (s,t) $ trm)	=if name=s
						then Syntax.free (pvar2pvarID trm)
						else Free (s,t) $ term_tr' (name,trm)
  | term_tr' (name,Abs (s,t,trm))	=Abs (s,t,term_tr' (name,trm))
  | term_tr' (name,trm1 $ trm2)		=term_tr' (name,trm1) $ term_tr' (name,trm2)
  | term_tr' (name,trm)			=trm;

fun bexp_tr' (Abs(_,_,b))	=term_tr' (variant_abs ("s",dummyT,b));

fun exp_tr' (Abs(_,_,e))	=term_tr' (variant_abs ("s",dummyT,e));

fun com_tr' (Const ("Skip",_))			=Syntax.const "@Skip"
  | com_tr' (Const ("Assign",_) $ v $ e)		=Syntax.const "@Assign" $ Syntax.free (pvar2pvarID v) $ exp_tr' e
  | com_tr' (Const ("Seq",_) $ c $ c')		=Syntax.const "@Seq" $ com_tr' c $ com_tr' c'
  | com_tr' (Const ("Cond",_) $ b $ c $ c')		=Syntax.const "@If" $ bexp_tr' b $ com_tr' c $ com_tr' c'
  | com_tr' (Const ("While",_) $ b $ inv $ c)	=Syntax.const "@While" $ bexp_tr' b $ bexp_tr' inv $ com_tr' c;

fun spec_tr' [p,c,q]		=Syntax.const "@Spec" $ bexp_tr' p $ com_tr' c $ bexp_tr' q;

val print_translation	=[("Spec",spec_tr')];
