(*  Title:      HOL/BCV/JVM.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   2000 TUM

A micro-JVM
*)

JVM = Kildall + JType + Opt + Product +

types mname
arities mname :: term

datatype instr =
    Load nat | Store nat | AConst_Null | IConst int
  | IAdd | Getfield ty cname | Putfield ty cname
  | New cname
  | Invoke cname mname ty ty
  | CmpEq nat
  | Return

types mdict = "cname => (mname * ty ~=> ty)"

constdefs
 wfi :: subclass => mdict => nat => instr => bool
"wfi S md maxr i == case i of
   Load n => n < maxr
 | Store n => n < maxr
 | AConst_Null => True
 | IConst j => True
 | IAdd => True
 | Getfield T C => is_type S T & is_type S (Class C)
 | Putfield T C => is_type S T & is_type S (Class C)
 | New C => is_type S (Class C)
 | Invoke C m pT rT => md C (m,pT) = Some(rT)
 | CmpEq n => True
 | Return => True"

 wfis :: subclass => mdict => nat => instr list => bool
"wfis S md maxr ins == !i : set ins. wfi S md maxr i"

types config = "ty list * ty err list"
      state  = config err option

constdefs
 stk_esl :: subclass => nat => ty list esl
"stk_esl S maxs == upto_esl maxs (JType.esl S)"

 reg_sl :: subclass => nat => ty err list sl
"reg_sl S maxr == Listn.sl maxr (Err.sl (JType.esl S))"

 sl :: subclass => nat => nat => state sl
"sl S maxs maxr ==
 Opt.sl(Err.sl(Product.esl (stk_esl S maxs) (Err.esl(reg_sl S maxr))))"

 states :: subclass => nat => nat => state set
"states S maxs maxr == fst(sl S maxs maxr)"

 le :: subclass => nat => nat => state ord
"le S maxs maxr == fst(snd(sl S maxs maxr))"

 sup :: subclass => nat => nat => state binop
"sup S maxs maxr == snd(snd(sl S maxs maxr))"

syntax "@lle" :: state => subclass => state => bool
       ("(_ /<<='__ _)" [50, 1000, 51] 50)

translations
"x <<=_S y" => "x <=_(le S arbitrary arbitrary) y"

constdefs

 wf_mdict :: subclass => mdict => bool
"wf_mdict S md ==
 !C mpT rT. md C mpT = Some(rT)
    --> is_type S rT &
        (!C'. (C',C) : S^*
            --> (EX rT'. md C' mpT = Some(rT') & rT' [=_S rT))"

 wti :: subclass => nat => ty => instr list => state list => nat => bool
"wti S maxs rT bs ss p ==
 case ss!p of
   None => True
 | Some e =>
 (case e of
   Err => False
 | OK (st,reg) =>
 (case bs!p of
   Load n => size st < maxs &
             (? T. reg!n = OK T & Some(OK(T#st,reg)) <<=_S ss!(p+1))
 | Store n => (? T Ts. st = T#Ts & Some(OK(Ts,reg[n := OK T])) <<=_S ss!(p+1))
 | AConst_Null => size st < maxs & Some(OK(NullT#st,reg)) <<=_S ss!(p+1)
 | IConst i => size st < maxs & Some(OK(Integer#st,reg)) <<=_S ss!(p+1)
 | IAdd => (? Ts. st = Integer#Integer#Ts &
                  Some(OK(Integer#Ts,reg)) <<=_S ss!(p+1))
 | Getfield fT C => (? T Ts. st = T#Ts & T [=_S Class(C) &
                            Some(OK(fT#Ts,reg)) <<=_S ss!(p+1))
 | Putfield fT C => (? vT oT Ts. st = vT#oT#Ts & vT [=_S fT & oT [=_S Class C &
                                 Some(OK(Ts,reg)) <<=_S ss!(p+1))
 | New C => (size st < maxs & Some(OK((Class C)#st,reg)) <<=_S ss!(p+1))
 | Invoke C m pT rT =>
   (? aT oT Ts. st = aT#oT#Ts & oT [=_S Class C & aT [=_S pT &
                Some(OK(rT#Ts,reg)) <<=_S ss!(p+1))
 | CmpEq q => (? T1 T2 Ts. st = T1#T2#Ts & (T1=T2 | is_ref T1 & is_ref T2) &
                           Some(OK(Ts,reg)) <<=_S ss!(p+1) &
                           Some(OK(Ts,reg)) <<=_S ss!q)
 | Return => (? T Ts. st = T#Ts & T [=_S rT)))"

 succs :: "instr list => nat => nat list"
"succs bs p ==
  case bs!p of
    Load n       => [p+1]
  | Store n      => [p+1]
  | AConst_Null  => [p+1]
  | IConst i     => [p+1]
  | IAdd         => [p+1]
  | Getfield x C => [p+1]
  | Putfield x C => [p+1]
  | New C        => [p+1]
  | Invoke C m pT rT => [p+1]
  | CmpEq q      => [p+1,q]
  | Return       => [p]"

 exec :: "subclass => nat => ty => instr => config => config err"
"exec S maxs rT instr == %(st,reg).
  case instr of
    Load n => if size st < maxs
              then case reg!n of Err => Err | OK T => OK(T#st,reg)
              else Err
  | Store n => (case st of [] => Err | T#Ts => OK(Ts,reg[n := OK T]))
  | AConst_Null => if size st < maxs then OK(NullT#st,reg) else Err
  | IConst i => if size st < maxs then OK(Integer#st,reg) else Err
  | IAdd =>
      (case st of [] => Err | T1#st1 =>
      (case st1 of [] => Err | T2#st2 =>
       if T1 = Integer & T2 = Integer then OK(st1,reg) else Err))
  | Getfield fT C =>
      (case st of [] => Err | oT#st' =>
      (if oT [=_S Class(C) then OK(fT#st',reg) else Err))
  | Putfield fT C =>
      (case st of [] => Err | vT#st1 =>
      (case st1 of [] => Err | oT#st2 =>
       if vT [=_S fT & oT [=_S Class C then OK(st2,reg) else Err))
  | New C => if size st < maxs then OK((Class C)#st,reg) else Err
  | Invoke C m pT rT =>
      (case st of [] => Err | aT#st1 =>
      (case st1 of [] => Err | oT#st2 =>
       if oT [=_S Class C & aT [=_S pT then OK(rT#st2,reg) else Err))
  | CmpEq q =>
      (case st of [] => Err | T1#st1 =>
      (case st1 of [] => Err | T2#st2 =>
       if T1=T2 | is_ref T1 & is_ref T2 then OK(st2,reg) else Err))
  | Return =>
      (case st of [] => Err | T#Ts =>
       if T [=_S rT then OK(st,reg) else Err)"

 step :: "subclass => nat => ty => instr list => nat => state => state"
"step S maxs rT bs p == option_map (lift (exec S maxs rT (bs!p)))"

 kiljvm ::
    "subclass => nat => nat => ty => instr list => state list => state list"
"kiljvm S maxs maxr rT bs ==
 kildall (sl S maxs maxr) (step S maxs rT bs) (succs bs)"

end
