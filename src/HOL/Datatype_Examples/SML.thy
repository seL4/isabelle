(*  Title:      HOL/Datatype_Benchmark/SML.thy

Example from Myra: part of the syntax of SML.
*)

theory SML imports Main begin

datatype
  string = EMPTY_STRING | CONS_STRING nat string

datatype
   strid = STRID string

datatype
   var = VAR string

datatype
   con = CON string

datatype
   scon = SCINT nat | SCSTR string

datatype
   excon = EXCON string

datatype
   label = LABEL string

datatype
  'a nonemptylist = Head_and_tail 'a "'a list"

datatype
  'a long = BASE 'a | QUALIFIED strid "'a long"

datatype
   atpat_e = WILDCARDatpat_e
           | SCONatpat_e scon
           | VARatpat_e var
           | CONatpat_e "con long"
           | EXCONatpat_e "excon long"
           | RECORDatpat_e "patrow_e option"
           | PARatpat_e pat_e
and
   patrow_e = DOTDOTDOT_e
            | PATROW_e label pat_e "patrow_e option"
and
   pat_e = ATPATpat_e atpat_e
         | CONpat_e "con long" atpat_e
         | EXCONpat_e "excon long" atpat_e
         | LAYEREDpat_e var pat_e
and
   conbind_e = CONBIND_e con "conbind_e option"
and
   datbind_e = DATBIND_e conbind_e "datbind_e option"
and
   exbind_e = EXBIND1_e excon "exbind_e option"
            | EXBIND2_e excon "excon long" "exbind_e option"
and
   atexp_e = SCONatexp_e scon
           | VARatexp_e "var long"
           | CONatexp_e "con long"
           | EXCONatexp_e "excon long"
           | RECORDatexp_e "exprow_e option"
           | LETatexp_e dec_e exp_e
           | PARatexp_e exp_e
and
   exprow_e = EXPROW_e label exp_e "exprow_e option"
and
   exp_e = ATEXPexp_e atexp_e
         | APPexp_e exp_e atexp_e
         | HANDLEexp_e exp_e match_e
         | RAISEexp_e exp_e
         | FNexp_e match_e
and
   match_e = MATCH_e mrule_e "match_e option"
and
   mrule_e = MRULE_e pat_e exp_e
and
   dec_e = VALdec_e valbind_e
         | DATATYPEdec_e datbind_e
         | ABSTYPEdec_e datbind_e dec_e
         | EXCEPTdec_e exbind_e
         | LOCALdec_e dec_e dec_e
         | OPENdec_e "strid long nonemptylist"
         | EMPTYdec_e
         | SEQdec_e dec_e dec_e
and
   valbind_e = PLAINvalbind_e pat_e exp_e "valbind_e option"
             | RECvalbind_e valbind_e

end
