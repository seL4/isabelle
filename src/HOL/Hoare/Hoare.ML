(*  Title:      HOL/Hoare/Hoare.ML
    ID:         $Id$
    Author:     Norbert Galm & Tobias Nipkow
    Copyright   1995 TUM

The verification condition generation tactics.
*)

open Hoare;

(*** Hoare rules ***)

val SkipRule = prove_goalw thy [Spec_def,Skip_def]
  "(!!s. p(s) ==> q(s)) ==> Spec p Skip q"
  (fn prems => [fast_tac (!claset addIs prems) 1]);

val AssignRule = prove_goalw thy [Spec_def,Assign_def]
  "(!!s. p s ==> q(%x. if x=v then e s else s x)) ==> Spec p (Assign v e) q"
  (fn prems => [fast_tac (!claset addIs prems) 1]);

val SeqRule = prove_goalw thy [Spec_def,Seq_def]
  "[| Spec p c (%s. q s); Spec (%s. q s) c' r |] ==> Spec p (Seq c c') r"
  (fn prems => [cut_facts_tac prems 1, Fast_tac 1]);

val IfRule = prove_goalw thy [Spec_def,Cond_def]
  "[| !!s. p s ==> (b s --> q s) & (~b s --> q' s); \
\     Spec (%s. q s) c r; Spec (%s. q' s) c' r |] \
\  ==> Spec p (Cond b c c') r"
  (fn [prem1,prem2,prem3] =>
     [REPEAT (rtac allI 1),
      REPEAT (rtac impI 1),
      dtac prem1 1,
      cut_facts_tac [prem2,prem3] 1,
      fast_tac (!claset addIs [prem1]) 1]);

val strenthen_pre = prove_goalw thy [Spec_def]
  "[| !!s. p s ==> p' s; Spec p' c q |] ==> Spec p c q"
  (fn [prem1,prem2] =>[cut_facts_tac [prem2] 1,
                       fast_tac (!claset addIs [prem1]) 1]);

val lemma = prove_goalw thy [Spec_def,While_def]
  "[| Spec (%s. I s & b s) c I; !!s. [| I s; ~b s |] ==> q s |] \
\  ==> Spec I (While b I c) q"
  (fn [prem1,prem2] =>
     [REPEAT(rtac allI 1), rtac impI 1, etac exE 1, rtac mp 1, atac 2,
      etac thin_rl 1, res_inst_tac[("x","s")]spec 1,
      res_inst_tac[("x","s'")]spec 1, nat_ind_tac "n" 1,
      Simp_tac 1,
      fast_tac (!claset addIs [prem2]) 1,
      simp_tac (!simpset addsimps [Seq_def]) 1,
      cut_facts_tac [prem1] 1, fast_tac (!claset addIs [prem2]) 1]);

val WhileRule = lemma RSN (2,strenthen_pre);


(*** meta_spec used in StateElimTac ***)

val meta_spec = prove_goal HOL.thy
  "(!!s x. PROP P s x) ==> (!!s. PROP P s (x s))"
  (fn prems => [resolve_tac prems 1]);


(**************************************************************************************************)
(*** Funktion zum Generieren eines Theorems durch Umbennenen von Namen von Lambda-Abstraktionen ***)
(*** in einem bestehenden Theorem. Bsp.: "!a.?P(a) ==> ?P(?x)" aus "!x.?P(x) ==> ?P(?x)"        ***)
(**************************************************************************************************)

(* rename_abs:term (von:string,nach:string,trm:term) benennt in trm alle Lambda-Abstraktionen
   mit Namen von in nach um *)

fun rename_abs (von,nach,Abs (s,t,trm)) =
    if von=s
	then Abs (nach,t,rename_abs (von,nach,trm))
        else Abs (s,t,rename_abs (von,nach,trm))
  | rename_abs (von,nach,trm1 $ trm2)   =rename_abs (von,nach,trm1) $ rename_abs (von,nach,trm2)
  | rename_abs (_,_,trm)                =trm;

(* ren_abs_thm:thm (von:string,nach:string,theorem:thm) benennt in theorem alle Lambda-Abstraktionen
   mit Namen von in nach um. Vorgehen:
        - Term t zu thoerem bestimmen
        - Term t' zu t durch Umbenennen der Namen generieren
        - Certified Term ct' zu t' erstellen
        - Thoerem ct'==ct' anlegen
        - Nach der Regel "[|P==Q; P|] ==> Q" wird aus "ct'==ct'" und theorem das Theorem zu ct'
          abgeleitet (ist moeglich, da t' mit t unifiziert werden kann, da nur Umnbenennungen) *)

fun ren_abs_thm (von,nach,theorem)      =
        equal_elim
                (reflexive (cterm_of (#sign (rep_thm theorem))
			    (rename_abs (von,nach,#prop (rep_thm theorem)))))
                theorem;


(****************************************************************************)
(*** Taktik zum Anwenden eines Theorems theorem auf ein Subgoal i durch   ***)
(***  - Umbenennen von Lambda-Abstraktionen im Theorem                    ***)
(***  - Instanziieren von freien Variablen im Theorem                     ***)
(***  - Composing des Subgoals mit dem Theorem                            ***)
(****************************************************************************)

(* - rens:(string*string) list, d.h. es koennen verschiedene Lambda-Abstraktionen umbenannt werden
   - insts:(cterm*cterm) list, d.h. es koennen verschiedene Variablen instanziiert werden *)

fun comp_inst_ren_tac rens insts theorem i      =
        let fun compose_inst_ren_tac [] insts theorem i                     =
	      compose_tac (false,
			   cterm_instantiate insts theorem,nprems_of theorem) i
	      | compose_inst_ren_tac ((von,nach)::rl) insts theorem i       =
                        compose_inst_ren_tac rl insts 
			  (ren_abs_thm (von,nach,theorem)) i
        in  compose_inst_ren_tac rens insts theorem i  end;


(***************************************************************    *********)
(*** Taktik zum Eliminieren des Zustandes waehrend Hoare-Beweisen                               ***)
(***    Bsp.: "!!s. s(Suc(0))=0 --> s(Suc(0))+1=1" wird zu "!!s b. b=0 --> b+1=1"               ***)
(****************************************************************************)

(* pvars_of_term:term list (name:string,trm:term) gibt die Liste aller Programm-Variablen
   aus trm zurueck. name gibt dabei den Namen der Zustandsvariablen an.
        Bsp.: bei name="s" und dem Term "s(Suc(Suc(0)))=s(0)" (entspricht "c=a")
              wird [0,Suc(Suc(0))] geliefert (Liste ist i.A. unsortiert) *)

fun pvars_of_term (name,trm)    =
  let fun add_vars (name,Free (s,t) $ trm,vl) =
            if name=s then if trm mem vl then vl else trm::vl
                      else add_vars (name,trm,vl)
	| add_vars (name,Abs (s,t,trm),vl)    =add_vars (name,trm,vl)
	| add_vars (name,trm1 $ trm2,vl)      =add_vars (name,trm2,add_vars (name,trm1,vl))
	| add_vars (_,_,vl)                   =vl
  in add_vars (name,trm,[]) end;


(* VarsElimTac: Taktik zum Eliminieren von bestimmten Programmvariablen aus dem Subgoal i
 - v::vl:(term) list  Liste der zu eliminierenden Programmvariablen
 - meta_spec:thm      Theorem, welches zur Entfernung der Variablen benutzt wird
		      z.B.: "(!!s x. PROP P(s,x)) ==> (!!s. PROP P(s,x(s)))"
 - namexAll:string    Name von    ^                                  (hier "x")
 - varx:term          Term zu                                      ^ (hier Var(("x",0),...))
 - varP:term          Term zu                                  ^     (hier Var(("P",0),...))
 - type_pvar:typ      Typ der Programmvariablen (d.h. 'a bei 'a prog, z.B.: nat, bool, ...)

 Vorgehen:
      - eliminiere jede pvar durch Anwendung von comp_inst_ren_tac. Dazu:
      - Unbenennung in meta_spec: namexAll wird in den Namen der Prog.-Var. umbenannt
	z.B.: fuer die Prog.-Var. mit Namen "a" ergibt sich
	      meta_spec zu "(!! s a. PROP P(s,a)) ==> (!! s. PROP P(s,x(s)))"
      - Instanziierungen in meta_spec:
	      varx wird mit "%s:(type_pvar) state. s(pvar)" instanziiert
	      varP wird entsprechend instanziiert. Beispiel fuer Prog.-Var. "a":
	 - zu Subgoal "!!s. s(Suc(0)) = s(0) ==> s(0) = 1" bestimme Term ohne "!!s.":
		trm0 = "s(Suc(0)) = s(0) ==> s(0) = 1" (s ist hier freie Variable)
	 - substituiere alle Vorkommen von s(pvar) durch eine freie Var. xs:
		trm1 = "s(Suc(0)) = xs ==> xs = 1"
	 - abstrahiere ueber xs:
		trm2 = "%xs. s(Suc(0)) = xs ==> xs = 1"
	 - abstrahiere ueber restliche Vorkommen von s:
		trm3 = "%s xs. s(Suc(0)) = xs ==> xs = 1"
	 - instanziiere varP mit trm3
*)

(* StateElimTac: tactic to eliminate all program variable from subgoal i
    - applies to subgoals of the form "!!s:('a) state. P(s)",
        i.e. the term  Const("all",_) $ Abs ("s",pvar --> 'a,_)
    -   meta_spec has the form "(!!s x. PROP P(s,x)) ==> (!!s. PROP P(s,x(s)))"
*)

val StateElimTac = SUBGOAL (fn (Bi,i) =>
  let val Const _ $ Abs (_,Type ("fun",[_,type_pvar]),trm) = Bi
      val _ $ (_ $ Abs (_,_,_ $ Abs (namexAll,_,_))) $
			    (_ $ Abs (_,_,varP $ _ $ (varx $ _))) = 
			    #prop (rep_thm meta_spec)
      fun vtac v i st = st |>
	  let val cterm = cterm_of (#sign (rep_thm st))
	      val (_,_,_ $ Abs (_,_,trm),_) = dest_state (st,i);
	      val (sname,trm0) = variant_abs ("s",dummyT,trm);
	      val xsname = variant_name ("xs",trm0);
	      val trm1 = subst_term (Free (sname,dummyT) $ v,
				     Syntax.free xsname,trm0)
	      val trm2 = Abs ("xs", type_pvar,
			      abstract_over (Syntax.free xsname,trm1))
	  in
	      comp_inst_ren_tac
		[(namexAll,pvar2pvarID v)]
		[(cterm varx,
		  cterm (Abs  ("s",Type ("nat",[]) --> type_pvar,
			       Bound 0 $ v))),
		 (cterm varP,
		  cterm (Abs ("s", Type ("nat",[]) --> type_pvar,
			      abstract_over (Free (sname,dummyT),trm2))))]
		meta_spec i
	  end
      fun vars_tac [] i      = all_tac
	| vars_tac (v::vl) i = vtac v i THEN vars_tac vl i
  in
      vars_tac (pvars_of_term (variant_abs ("s",dummyT,trm))) i
  end);


(*** tactics for verification condition generation ***)

(* pre_cond:bool gibt an, ob das Subgoal von der Form Spec(?Q,c,p) ist oder nicht. Im Fall
   von pre_cond=false besteht die Vorbedingung nur nur aus einer scheme-Variable. Die dann
   generierte Verifikationsbedingung hat die Form "!!s.?Q --> ...". "?Q" kann deshalb zu gegebenen
   Zeitpunkt mittels "rtac impI" und "atac" gebunden werden, die Bedingung loest sich dadurch auf. *)

fun WlpTac i = (rtac SeqRule i) THEN (HoareRuleTac (i+1) false)
and HoareRuleTac i pre_cond st = st |>  
	(*abstraction over st prevents looping*)
    ( (WlpTac i THEN HoareRuleTac i pre_cond)
      ORELSE
      (FIRST[rtac SkipRule i,
	     rtac AssignRule i,
	     EVERY[rtac IfRule i,
		   HoareRuleTac (i+2) false,
		   HoareRuleTac (i+1) false],
	     EVERY[rtac WhileRule i,
		   Asm_full_simp_tac (i+2),
		   HoareRuleTac (i+1) true]]
       THEN
       (if pre_cond then (Asm_full_simp_tac i) else (atac i))) );

val hoare_tac = 
  SELECT_GOAL
    (EVERY[HoareRuleTac 1 true, ALLGOALS StateElimTac, prune_params_tac]);

