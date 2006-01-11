
theory Class 
imports "../nominal" 
begin

atom_decl name coname

section {* Term-Calculus from my PHD *}

nominal_datatype trm = Ax  "name" "coname"
                 | ImpR "\<guillemotleft>name\<guillemotright>(\<guillemotleft>coname\<guillemotright>trm)" "coname"  ("ImpR [_].[_]._ _" [100,100,100,100] 100)
                 | ImpL "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm" "name"("ImpL [_]._ [_]._ _" [100,100,100,100,100] 100)
                 | Cut "\<guillemotleft>coname\<guillemotright>trm" "\<guillemotleft>name\<guillemotright>trm"        ("Cut [_]._ [_]._" [100,100,100,100] 100)

thm trm.induct
thm trm.inducts
thm trm.induct'

