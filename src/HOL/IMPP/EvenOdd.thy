(*  Title:      HOL/IMPP/EvenOdd.thy
    ID:         $Id$
    Author:     David von Oheimb
    Copyright   1999 TUM

Example of mutually recursive procedures verified with Hoare logic
*)

EvenOdd = Misc +

constdefs even :: nat => bool
  "even n == #2 dvd n"

consts
  Even, Odd :: pname
rules 
  Even_neq_Odd "Even ~= Odd"
  Arg_neq_Res  "Arg  ~= Res"

constdefs
  evn :: com
 "evn == IF (%s. s<Arg>=0)
         THEN Loc Res:==(%s. 0)
         ELSE(Loc Res:=CALL Odd(%s. s<Arg> - 1);;
              Loc Arg:=CALL Odd(%s. s<Arg> - 1);;
              Loc Res:==(%s. s<Res> * s<Arg>))"
  odd :: com
 "odd == IF (%s. s<Arg>=0)
         THEN Loc Res:==(%s. 1)
         ELSE(Loc Res:=CALL Even (%s. s<Arg> -1))"

defs
  bodies_def "bodies == [(Even,evn),(Odd,odd)]"
  
consts
  Z_eq_Arg_plus   :: nat => nat assn ("Z=Arg+_" [50]50)
 "even_Z=(Res=0)" ::        nat assn ("Res'_ok")
defs
  Z_eq_Arg_plus_def "Z=Arg+n == %Z s.      Z =  s<Arg>+n"
  Res_ok_def       "Res_ok   == %Z s. even Z = (s<Res>=0)"

end
