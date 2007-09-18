module Classes where {


data Nat = Suc Classes.Nat | Zero_nat;

data Bit = B1 | B0;

nat_aux :: Integer -> Classes.Nat -> Classes.Nat;
nat_aux i n =
  (if i <= 0 then n else Classes.nat_aux (i - 1) (Classes.Suc n));

nat :: Integer -> Classes.Nat;
nat i = Classes.nat_aux i Classes.Zero_nat;

class Semigroup a where {
  mult :: a -> a -> a;
};

class (Classes.Semigroup a) => Monoidl a where {
  neutral :: a;
};

class (Classes.Monoidl a) => Group a where {
  inverse :: a -> a;
};

inverse_int :: Integer -> Integer;
inverse_int i = negate i;

neutral_int :: Integer;
neutral_int = 0;

mult_int :: Integer -> Integer -> Integer;
mult_int i j = i + j;

instance Classes.Semigroup Integer where {
  mult = Classes.mult_int;
};

instance Classes.Monoidl Integer where {
  neutral = Classes.neutral_int;
};

instance Classes.Group Integer where {
  inverse = Classes.inverse_int;
};

pow_nat :: (Classes.Group b) => Classes.Nat -> b -> b;
pow_nat (Classes.Suc n) x = Classes.mult x (Classes.pow_nat n x);
pow_nat Classes.Zero_nat x = Classes.neutral;

pow_int :: (Classes.Group a) => Integer -> a -> a;
pow_int k x =
  (if 0 <= k then Classes.pow_nat (Classes.nat k) x
    else Classes.inverse (Classes.pow_nat (Classes.nat (negate k)) x));

example :: Integer;
example = Classes.pow_int 10 (-2);

}
