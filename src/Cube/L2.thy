
L2 = Base +

rules
  pi_bs         "[| A:[]; !!x. x:A ==> B(x):* |] ==> Prod(A,B):*"
  lam_bs        "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):* |]
                   ==> Abs(A,f) : Prod(A,B)"

end
