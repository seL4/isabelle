open Witness;

(* -------------------------------------------------------------------- *)
(* classes cplus, cminus, ctimes, cdiv introduce 
   characteristic constants  o+ o- o* o/

	"bullet":: "void -> void -> void"

   is the witness for o+ o- o* o/	

   No characteristic axioms are to be checked
*)

(* -------------------------------------------------------------------- *)
(* classes per and qpo introduce characteristic constants
	".="	:: "'a::per -> 'a -> tr"		(cinfixl 55)
	".<="	:: "'a::qpo -> 'a -> tr"		(cinfixl 55)

   The witness for these is 

	"cric"	:: "void -> void -> tr"			(cinfixl 55)

   the classes equiv, eq, qlinear impose additional axioms
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

weq	"[|(x::'a::eq) ~= UU; y ~= UU|] ==> (x = y --> (x .= y)=TT) & (x ~= y --> «x .= y»)"


   --------------------------------------------------------------------

characteristic axioms of class qpo:

strict_qpo	"(UU .<= x) = UU & (x .<= UU) = UU"
total_qpo	"[|x ~= UU; y ~= UU|] ==> (x .<= y) ~= UU"

refl_qpo	"[|x ~= UU|] ==> (x .<= x)=TT"
antisym_qpo	"[|(x .<= y)=TT; (y .<= x)=TT |] ==> (x .= y)=TT"
trans_qpo	"[|(x .<= y)=TT; (y .<= z)=TT |] ==> (x .<= z)=TT"
antisym_qpo_rev	" (x .= y)=TT ==> (x .<= y)=TT & (y .<= x)=TT" 

   --------------------------------------------------------------------

characteristic axioms of class qlinear:

qlinear	"[|(x::'a::qlinear) ~= UU; y ~= UU|] ==> (x .<= y)=TT | (y .<= x)=TT "

*)

(* strict_per, strict_qpo *)
val prems = goal thy "(UU circ x) = UU & (x circ UU) = UU";
by (simp_tac (HOLCF_ss addsimps [circ_def]) 1);
result();

(* total_per, total_qpo *)
val prems = goal thy "[|x ~= UU; y ~= UU|] ==> (x circ y) ~= UU";
by (cut_facts_tac prems 1);
by (etac notE 1);
by (rtac unique_void2 1);
result();

(* flat_per *)

val prems = goal thy "flat (UU::void)";
by (rtac flat_void 1);
result();

(* sym_per *)  
val prems = goal thy "(x circ y) = (y circ x)";
by (simp_tac (HOLCF_ss addsimps [circ_def]) 1);
result();

(* trans_per, trans_qpo *)
val prems = goal thy "[|(x bullet y)=TT; (y bullet z)=TT |] ==> (x bullet z)=TT";
by (cut_facts_tac prems 1);
by (asm_full_simp_tac (HOLCF_ss addsimps [bullet_def]) 1);
result();

(* refl_per *)
val prems = goal thy "[|(x::void) ~= UU|] ==> (x bullet x)=TT";
by (cut_facts_tac prems 1);
by (etac notE 1);
by (rtac unique_void2 1);
result();

(* weq *)
val prems = goal thy 
	"[|(x::void) ~= UU; y ~= UU|] ==> (x = y --> (x bullet y)=TT) & (x ~= y --> (x bullet y)=FF)";
by (cut_facts_tac prems 1);
by (etac notE 1);
by (rtac unique_void2 1);
result();

(* antisym_qpo *)
val prems = goal thy "[|(x bullet y)=TT; (y bullet x)=TT |] ==> (x bullet y)=TT";
by (cut_facts_tac prems 1);
by (asm_full_simp_tac (HOLCF_ss addsimps [bullet_def]) 1);
result();

(* antisym_qpo_rev *)
val prems = goal thy "(x bullet y)=TT ==> (x bullet y)=TT & (y bullet x)=TT";
by (cut_facts_tac prems 1);
by (asm_full_simp_tac (HOLCF_ss addsimps [bullet_def]) 1);

(* qlinear *)
val prems = goal thy 
	"[|(x::void) ~= UU; y ~= UU|] ==> (x bullet y)=TT | (y bullet x)=TT ";
by (cut_facts_tac prems 1);
by (etac notE 1);
by (rtac unique_void2 1);
result();
