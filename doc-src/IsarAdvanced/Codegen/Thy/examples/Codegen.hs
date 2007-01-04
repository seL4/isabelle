module Codegen where
import qualified Nat

class Null a where
  nulla :: a

heada :: (Codegen.Null a) => ([a] -> a)
heada (y : xs) = y

null_option :: Maybe b
null_option = Nothing

instance Codegen.Null (Maybe b) where
  null = Codegen.null_option

dummy :: Maybe Nat.Nat
dummy = Codegen.heada [Just (Nat.Suc Nat.Zero_nat), Nothing]
