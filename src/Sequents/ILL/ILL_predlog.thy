(* 
    File:	 /Nfs/toton/usr20/sk/isa_files/ll/NEW/pred_log.thy
    Theory Name: pred_log
    Logic Image: HOL
*)

ILL_predlog  =  ILL +

types
    plf
    
consts

  "&"   :: "[plf,plf] => plf"   (infixr 35)
  "|"   :: "[plf,plf] => plf"   (infixr 35)
  ">"   :: "[plf,plf] => plf"   (infixr 35)
  "="   :: "[plf,plf] => plf"   (infixr 35)
  "@NG" :: "plf => plf"   ("- _ " [50] 55)
  ff    :: "plf"
  
  PL    :: "plf => o"      ("[* / _ / *]" [] 100)


translations

  "[* A & B *]" == "[*A*] && [*B*]" 
  "[* A | B *]" == "![*A*] ++ ![*B*]"
  "[* - A *]"   == "[*A > ff*]"
  "[* ff *]"    == "0"
  "[* A = B *]" => "[* (A > B) & (B > A) *]"
  
  "[* A > B *]" == "![*A*] -o [*B*]"
  
(* another translations for linear implication:
  "[* A > B *]" == "!([*A*] -o [*B*])" *)

end
