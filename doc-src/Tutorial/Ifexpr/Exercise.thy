Exercise = Main +
datatype ifex = CIF bool | VIF nat | IF ifex ifex ifex
consts valif :: ifex => (nat => bool) => bool
primrec valif ifex
"valif (CIF b)    env = b"
"valif (VIF x)    env = env x"
"valif (IF b t e) env = (if valif b env then valif t env
                                        else valif e env)"
consts normif :: ifex => ifex => ifex => ifex
primrec normif ifex
"normif (CIF b)    t e = (if b then t else e)"
"normif (VIF x)    t e = IF (VIF x) t e"
"normif (IF b t e) u f = normif b (normif t u f) (normif e u f)"
consts norm :: ifex => ifex
primrec norm ifex
"norm (CIF b)    = CIF b"
"norm (VIF x)    = VIF x"
"norm (IF b t e) = normif b (norm t) (norm e)"
consts normal :: ifex => bool
primrec normal ifex
"normal(CIF b) = True"
"normal(VIF x) = True"
"normal(IF b t e) = (normal t & normal e &
      (case b of CIF b => False | VIF x => True | IF x y z => False))"
end
