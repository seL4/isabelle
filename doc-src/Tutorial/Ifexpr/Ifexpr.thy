Ifexpr = Main +
datatype boolex = Const bool | Var nat
                | Neg boolex | And boolex boolex
consts value :: boolex => (nat => bool) => bool
primrec
"value (Const b) env = b"
"value (Var x)   env = env x"
"value (Neg b)   env = (~ value b env)"
"value (And b c) env = (value b env & value c env)"
datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex
consts valif :: ifex => (nat => bool) => bool
primrec
"valif (CIF b)    env = b"
"valif (VIF x)    env = env x"
"valif (IF b t e) env = (if valif b env then valif t env
                                        else valif e env)"
consts bool2if :: boolex => ifex
primrec
"bool2if (Const b) = CIF b"
"bool2if (Var x)   = VIF x"
"bool2if (Neg b)   = IF (bool2if b) (CIF False) (CIF True)"
"bool2if (And b c) = IF (bool2if b) (bool2if c) (CIF False)"
consts normif :: ifex => ifex => ifex => ifex
primrec
"normif (CIF b)    t e = IF (CIF b) t e"
"normif (VIF x)    t e = IF (VIF x) t e"
"normif (IF b t e) u f = normif b (normif t u f) (normif e u f)"
consts norm :: ifex => ifex
primrec
"norm (CIF b)    = CIF b"
"norm (VIF x)    = VIF x"
"norm (IF b t e) = normif b (norm t) (norm e)"
consts normal :: ifex => bool
primrec
"normal(CIF b) = True"
"normal(VIF x) = True"
"normal(IF b t e) = (normal t & normal e &
      (case b of CIF b => True | VIF x => True | IF x y z => False))"
end
