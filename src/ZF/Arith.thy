(*  Title:      ZF/arith.thy
    ID:         $Id$
    Author:     Lawrence C Paulson, Cambridge University Computer Laboratory
    Copyright   1992  University of Cambridge

Arithmetic operators and their definitions
*)

Arith = Epsilon + 
consts
    rec  :: [i, i, [i,i]=>i]=>i
    "#*" :: [i,i]=>i                    (infixl 70)
    div  :: [i,i]=>i                    (infixl 70) 
    mod  :: [i,i]=>i                    (infixl 70)
    "#+" :: [i,i]=>i                    (infixl 65)
    "#-" :: [i,i]=>i                    (infixl 65)

defs
    rec_def  "rec(k,a,b) ==  transrec(k, %n f. nat_case(a, %m. b(m, f`m), n))"

    add_def  "m#+n == rec(m, n, %u v. succ(v))"
    diff_def "m#-n == rec(n, m, %u v. rec(v, 0, %x y. x))"
    mult_def "m#*n == rec(m, 0, %u v. n #+ v)"
    mod_def  "m mod n == transrec(m, %j f. if(j<n, j, f`(j#-n)))"
    div_def  "m div n == transrec(m, %j f. if(j<n, 0, succ(f`(j#-n))))"
end
