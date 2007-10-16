module Codegen where {

import qualified Nat;

class Null a where {
  nulla :: a;
};

heada :: (Codegen.Null b) => [b] -> b;
heada (x : xs) = x;
heada [] = Codegen.nulla;

null_option :: Maybe a;
null_option = Nothing;

instance Codegen.Null (Maybe a) where {
  nulla = Codegen.null_option;
};

dummy :: Maybe Nat.Nat;
dummy = Codegen.heada [Just (Nat.Suc Nat.Zero_nat), Nothing];

}
