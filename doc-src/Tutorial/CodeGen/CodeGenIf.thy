CodeGenIf = List +
types 'v binop = 'v => 'v => 'v
      'v test = 'v => bool
datatype ('a,'v) expr = Vex 'a 
                      | Cex 'v
                      | Bex ('v binop) (('a,'v) expr) (('a,'v) expr)
                      | Ifex ('v test) (('a,'v)expr) (('a,'v)expr) (('a,'v)expr)
consts value :: ('a => 'v) => ('a,'v)expr => 'v
primrec value expr
"value env (Vex a) = env a"
"value env (Cex v) = v"
"value env (Bex f e1 e2) = f (value env e1) (value env e2)"
"value env (Ifex t b e1 e2) =
   (if t(value env b) then value env e1 else value env e2)"
datatype ('a,'v) instr = Load 'a
                       | Const 'v
                       | Apply ('v binop)
                       | Jump nat
                       | Test ('v test) nat
consts exec :: "('a => 'v) * 'v list * (('a,'v) instr) list => 'v list"
recdef exec "measure(%(s,vs,is).length is)"
simpset "simpset() addsimps [diff_less_Suc]"
"exec(s, vs, []) = vs"
"exec(s, vs, i#is) = (case i of
    Load a   => exec(s,(s a)#vs,is)
  | Const v  => exec(s,v#vs,is)
  | Apply f  => exec(s, (f (hd vs) (hd(tl vs)))#(tl(tl vs)), is)
  | Jump n   => exec(s, vs, drop n is)
  | Test t n => (if t(hd vs) then exec(s,tl vs, drop n is)
                             else exec(s,tl vs, is)))"
consts comp :: ('a,'v) expr => (('a,'v) instr) list
primrec comp expr
"comp (Vex a) = [Load a]"
"comp (Cex v) = [Const v]"
"comp (Bex f e1 e2) = (comp e2)@(comp e1)@[Apply f]"
"comp (Ifex t b e1 e2) = (let is1 = comp e1; is2 = comp e2
                          in comp b @ [Test t (Suc(length is2))] @
                             is2 @ [Jump (length is1)] @ is1)"

consts wf :: ('a,'v)instr list => bool
primrec wf list
"wf [] = True"
"wf (i#is) = (wf is & (case i of Load a => True | Const v => True
  | Apply f  => True | Jump n => n <= length is | Test t n => n <= length is))"

end
