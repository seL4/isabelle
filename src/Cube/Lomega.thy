
Lomega = Base +

rules
  pi_bb         "[| A:[]; !!x. x:A ==> B(x):[] |] ==> Prod(A,B):[]"
  lam_bb        "[| A:[]; !!x. x:A ==> f(x):B(x); !!x. x:A ==> B(x):[] |]
                   ==> Abs(A,f) : Prod(A,B)"

end
