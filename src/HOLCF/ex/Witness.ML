open Witness;

(* -------------------------------------------------------------------- *)
(* classes cplus, cminus, ctimes, cdiv introduce 
   characteristic constants  o+ o- o* o/

	"circ":: "one -> one -> one"

   is the witness for o+ o- o* o/	

   No characteristic axioms are to be checked
*)

(* -------------------------------------------------------------------- *)
(* classes per and qpo introduce characteristic constants
	".="	:: "'a::per -> 'a -> tr"		(cinfixl 55)
	".<="	:: "'a::qpo -> 'a -> tr"		(cinfixl 55)

   The witness for these is 

	"bullet":: "one -> one -> tr"			(cinfixl 55)

   the classes equiv, eq, impose additional axioms
*)

(* -------------------------------------------------------------------- *)
(* 

characteristic axioms of class per:

strict_per	"(UU .= x) = UU & (x .= UU) = UU"
total_per	"[|x ~= UU; y ~= UU|] ==> (x .= y) ~= UU"
flat_per	"flat (UU::'a::per)"

sym_per		"(x .= y) = (y .= x)"
trans_per	"[|(x .= y)=TT; (y .= z)=TT |] ==> (x .= z)=TT"

   --------------------------------------------------------------------

characteristic axioms of class equiv:

refl_per	"[|(x::'a::equiv) ~= UU|] ==> (x .= x)=TT"

   --------------------------------------------------------------------

characteristic axioms of class eq:

weq	"[|(x::'a::eq)~=UU; y~=UU|] ==> (x=y --> (x.=y)=TT) & (x~=y --> Çx.=yÈ)"


   --------------------------------------------------------------------

*)

(* strict_per, strict_qpo *)
goalw thy [bullet_def] "(UU bullet x) = UU & (x bullet UU) = UU";
by (simp_tac (!simpset addsimps [flift1_def,flift2_def,o_def]) 1);
by (lift.induct_tac "x" 1);
auto();
result();

(* total_per, total_qpo *)
val prems = goal thy "[|x~=UU; y~=UU|] ==> (x bullet y) ~= UU";
by (subgoal_tac "x~=UU&y~=UU-->(x bullet y) ~= UU" 1);
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
by (simp_tac (!simpset addsimps [bullet_def,flift1_def,flift2_def,o_def]) 1);
by (lift.induct_tac "x" 1);
by (fast_tac HOL_cs 1);
by (lift.induct_tac "y" 1);
auto();
result();

(* flat_per *)

goal thy "flat (x::one)";
by (rtac flat_flat 1);
result();

(* sym_per *)  
goalw thy [bullet_def] "(x bullet y) = (y bullet x)";
by (simp_tac (!simpset addsimps [bullet_def,flift1_def,flift2_def,o_def]) 1);
by (lift.induct_tac "x" 1);
by (lift.induct_tac "y" 2);
by (lift.induct_tac "y" 1);
auto();
result();

(* trans_per, trans_qpo *)
val prems = goal thy "[|(x bullet y)=TT; (y bullet z)=TT|] ==>(x bullet z)=TT";
by (subgoal_tac "(x bullet y)=TT&(y bullet z)=TT-->(x bullet z)=TT" 1);
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
by (simp_tac (!simpset addsimps [bullet_def,flift1_def,flift2_def,o_def]) 1);
by (lift.induct_tac "x" 1);
by (lift.induct_tac "y" 2);
by (lift.induct_tac "y" 1);
by (lift.induct_tac "z" 4);
by (lift.induct_tac "z" 3);
by (lift.induct_tac "z" 2);
by (lift.induct_tac "z" 1);
auto();
result();

(* refl_per *)
val prems = goal thy "x ~= UU ==> (x bullet x)=TT";
by (subgoal_tac "x ~= UU --> (x bullet x)=TT" 1);
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
by (simp_tac (!simpset addsimps [bullet_def,flift1_def,flift2_def,o_def]) 1);
by (lift.induct_tac "x" 1);
auto();
qed "refl_per_one";

(* weq *)
val prems = goal thy 
	"[|x~=UU; y~=UU|]==>(x=y-->(x bullet y)=TT)&(x~=y-->(x bullet y)=FF)";
by(subgoal_tac"x~=UU&y~=UU-->(x=y-->(x bullet y)=TT)&(x~=y-->(x bullet y)=FF)"1);
by (cut_facts_tac prems 1);
by (fast_tac HOL_cs 1);
by (lift.induct_tac "x" 1);
by (lift.induct_tac "y" 2);
by (lift.induct_tac "y" 1);
auto();
br refl_per_one 1;
auto();
by (simp_tac (!simpset addsimps [bullet_def,flift1_def,flift2_def,o_def]) 1);
result();

