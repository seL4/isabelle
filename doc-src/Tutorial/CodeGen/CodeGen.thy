CodeGen = Main +
types 'v binop = 'v => 'v => 'v
datatype ('a,'v) expr = Cex 'v
                      | Vex 'a
                      | Bex ('v binop)  (('a,'v) expr) (('a,'v) expr)
consts value :: ('a => 'v) => ('a,'v)expr => 'v
primrec
"value env (Cex v) = v"
"value env (Vex a) = env a"
"value env (Bex f e1 e2) = f (value env e1) (value env e2)"
datatype ('a,'v) instr = Const 'v
                       | Load 'a
                       | Apply ('v binop)
consts exec :: ('a => 'v) => 'v list => (('a,'v) instr) list => 'v list
primrec
"exec s vs [] = vs"
"exec s vs (i#is) = (case i of
    Const v  => exec s (v#vs) is
  | Load a   => exec s ((s a)#vs) is
  | Apply f  => exec s ( (f (hd vs) (hd(tl vs)))#(tl(tl vs)) ) is)"
consts comp :: ('a,'v) expr => (('a,'v) instr) list
primrec
"comp (Cex v)       = [Const v]"
"comp (Vex a)       = [Load a]"
"comp (Bex f e1 e2) = (comp e2) @ (comp e1) @ [Apply f]"
end
