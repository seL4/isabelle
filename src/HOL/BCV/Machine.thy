(*  Title:      HOL/BCV/Machine.thy
    ID:         $Id$
    Author:     Tobias Nipkow
    Copyright   1999 TUM

A register machine.
*)

Machine = Types + DFAimpl +

datatype ('a,'b,'c)instr =
    Move nat nat
  | Aload 'a nat | Bload 'b nat | Cload 'c nat
  | Aop nat nat nat | Bop nat nat nat | Cop nat nat nat
  | Comp nat nat nat
  | Halt

consts maxreg :: ('a,'b,'c)instr => nat
       maxregs :: ('a,'b,'c)instr list => nat
primrec
"maxreg(Move m n) = max m n"
"maxreg(Aload x n) = n"
"maxreg(Bload x n) = n"
"maxreg(Cload x n) = n"
"maxreg(Aop i j k) = max i (max j k)"
"maxreg(Bop i j k) = max i (max j k)"
"maxreg(Cop i j k) = max i (max j k)"
"maxreg(Comp i j l) = max i j"
"maxreg Halt = 0"

primrec
"maxregs [] = 0"
"maxregs (x#xs) = max (maxreg x+1) (maxregs xs)"

constdefs

 wt_instr :: ('a,'b,'c)instr => nat => typ list option list => bool
"wt_instr b p T ==
 case T!p of
   None => True
 | Some ts =>
 case b of
   Move i j  => Some(ts[j:=ts!i]) <= T!(p+1)
 | Aload x i => Some(ts[i:=Atyp]) <= T!(p+1)
 | Bload x i => Some(ts[i:=Btyp]) <= T!(p+1)
 | Cload x i => Some(ts[i:=Ctyp]) <= T!(p+1)
 | Aop i j k => ts!i <= Atyp & ts!j <= Atyp & Some(ts[k:=Atyp]) <= T!(p+1)
 | Bop i j k => ts!i <= Btyp & ts!j <= Btyp & Some(ts[k:=Btyp]) <= T!(p+1)
 | Cop i j k => ts!i <= Ctyp & ts!j <= Ctyp & Some(ts[k:=Ctyp]) <= T!(p+1)
 | Comp i j q => (ts!i <= ts!j & ts!j ~= Top | ts!j <= ts!i & ts!i ~= Top) &
                 T!p <= T!(p+1) & T!p <= T!q
 | Halt =>      True"

 stype :: ('a,'b,'c)instr list => typ list set
"stype bs == listsn (maxregs bs) UNIV"

constdefs
 succs :: "('a,'b,'c)instr => nat => nat list"
"succs instr p ==
  case instr of
    Move i j  => [p+1]
  | Aload x i => [p+1]
  | Bload x i => [p+1]
  | Cload x i => [p+1]
  | Aop i j k => [p+1]
  | Bop i j k => [p+1]
  | Cop i j k => [p+1]
  | Comp i j q => [p+1,q]
  | Halt       => []"

 exec :: "('a,'b,'c)instr => typ list => typ list option"
"exec instr ts ==
  case instr of
    Move i j  => Some(ts[j := ts!i])
  | Aload x i => Some(ts[i := Atyp])
  | Bload x i => Some(ts[i := Btyp])
  | Cload x i => Some(ts[i := Ctyp])
  | Aop i j k => if ts!i <= Atyp & ts!j <= Atyp
                 then Some(ts[k := Atyp])
                 else None
  | Bop i j k => if ts!i <= Btyp & ts!j <= Btyp
                 then Some(ts[k := Btyp])
                 else None
  | Cop i j k => if ts!i <= Ctyp & ts!j <= Ctyp
                 then Some(ts[k := Ctyp])
                 else None
  | Comp i j q => if ts!i <= ts!j & ts!j ~= Top | ts!j <= ts!i & ts!i ~= Top
                  then Some ts
                  else None
  | Halt       => Some ts"
(*
  | Bop i j k => if ts!i <= Btyp & ts!j <= Btyp
                 then Some(ts[k := ts!i+ts!j])
                 else None
*)
end
