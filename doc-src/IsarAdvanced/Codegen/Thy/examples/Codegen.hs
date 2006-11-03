module Codegen where
import qualified IntDef

class Null a where
  null :: a

head :: (Codegen.Null a_1) => [a_1] -> a_1
head (y : xs) = y
head [] = Codegen.null

null_option :: Maybe b
null_option = Nothing

instance Codegen.Null (Maybe b) where
  null = Codegen.null_option

dummy :: Maybe IntDef.Nat
dummy = Codegen.head [Just (IntDef.Succ_nat IntDef.Zero_nat), Nothing]
