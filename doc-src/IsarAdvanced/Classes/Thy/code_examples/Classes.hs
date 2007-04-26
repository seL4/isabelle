module Classes where {

import qualified Integer;
import qualified Nat;

class Semigroup a where {
  mult :: a -> a -> a;
};

class (Classes.Semigroup a) => Monoidl a where {
  neutral :: a;
};

class (Classes.Monoidl a) => Group a where {
  inverse :: a -> a;
};

inverse_int :: Integer.Inta -> Integer.Inta;
inverse_int i = Integer.uminus_int i;

neutral_int :: Integer.Inta;
neutral_int = Integer.Number_of_int Integer.Pls;

mult_int :: Integer.Inta -> Integer.Inta -> Integer.Inta;
mult_int i j = Integer.plus_int i j;

instance Classes.Semigroup Integer.Inta where {
  mult = Classes.mult_int;
};

instance Classes.Monoidl Integer.Inta where {
  neutral = Classes.neutral_int;
};

instance Classes.Group Integer.Inta where {
  inverse = Classes.inverse_int;
};

pow_nat :: (Classes.Monoidl b) => Nat.Nat -> b -> b;
pow_nat (Nat.Suc n) x = Classes.mult x (Classes.pow_nat n x);
pow_nat Nat.Zero_nat x = Classes.neutral;

pow_int :: (Classes.Group a) => Integer.Inta -> a -> a;
pow_int k x =
  (if Integer.less_eq_int (Integer.Number_of_int Integer.Pls) k
    then Classes.pow_nat (Integer.nat k) x
    else Classes.inverse
           (Classes.pow_nat (Integer.nat (Integer.uminus_int k)) x));

example :: Integer.Inta;
example =
  Classes.pow_int
    (Integer.Number_of_int
      (Integer.Bit
        (Integer.Bit
          (Integer.Bit (Integer.Bit Integer.Pls Integer.B1) Integer.B0)
          Integer.B1)
        Integer.B0))
    (Integer.Number_of_int (Integer.Bit Integer.Min Integer.B0));

}
