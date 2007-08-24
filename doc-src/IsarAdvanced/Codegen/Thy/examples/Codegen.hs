module Codegen where {

import qualified Nat;

class Null a where {
  nulla :: a;
};

heada :: (Codegen.Null b) => [b] -> b;
heada (x : xs) = x;
heada [] = Codegen.nulla;

instance Codegen.Null (Maybe b) where {
  nulla = Nothing;
};

dummy :: Maybe Nat.Nat;
dummy = Codegen.heada [Just (Nat.Suc Nat.Zero_nat), Nothing];

}
