(* $Id$ *)

theory Class 
imports "../Nominal" 
begin

section {* Term-Calculus from Urban's PhD *}

atom_decl name coname

nominal_datatype trm = 
    Ax   "name" "coname"
  | Cut  "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"            ("Cut <_>._ [_]._" [100,100,100,100] 100)
  | NotR "\<guillemotleft>name\<guillemotright>trm" "coname"                 ("NotR [_]._ _" [100,100,100] 100)
  | NotL "\<guillemotleft>coname\<guillemotright>trm" "name"                 ("NotL <_>._ _" [100,100,100] 100)
  | AndR "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>coname\<guillemotright>trm" "coname" ("AndR <_>._ <_>._ _" [100,100,100,100,100] 100)
  | AndL1 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL1 [_]._ _" [100,100,100] 100)
  | AndL2 "\<guillemotleft>name\<guillemotright>trm" "name"                  ("AndL2 [_]._ _" [100,100,100] 100)
  | OrR1 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR1 <_>._ _" [100,100,100] 100)
  | OrR2 "\<guillemotleft>coname\<guillemotright>trm" "coname"               ("OrR2 <_>._ _" [100,100,100] 100)
  | OrL "\<guillemotleft>name\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"        ("OrL [_]._ [_]._ _" [100,100,100,100,100] 100)
  | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"       ("ImpR [_].<_>._ _" [100,100,100,100] 100)
  | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"     ("ImpL <_>._ [_]._ _" [100,100,100,100,100] 100)


text {* Induction principles *}

thm trm.induct_weak --"weak"
thm trm.induct      --"strong"
thm trm.induct'     --"strong with explicit context (rarely needed)"

text {* named terms *}

nominal_datatype ntrm = N "\<guillemotleft>name\<guillemotright>trm" ("N (_)._" [100,100] 100)

text {* conamed terms *}

nominal_datatype ctrm = C "\<guillemotleft>coname\<guillemotright>trm" ("C <_>._" [100,100] 100)

text {* We should now define the two forms of substitition :o( *}

consts
  substn :: "trm \<Rightarrow> name   \<Rightarrow> ctrm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100) 
  substc :: "trm \<Rightarrow> coname \<Rightarrow> ntrm \<Rightarrow> trm" ("_[_::=_]" [100,100,100] 100)

text {* does not work yet *}


end

