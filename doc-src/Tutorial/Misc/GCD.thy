GCD = WF_Rel +
consts gcd :: "nat*nat => nat"
recdef gcd "measure ((%(m,n).n))"
  simpset "simpset() addsimps [mod_less_divisor]"
    "gcd (m, n) = (if n=0 then m else gcd(n, m mod n))"
end
