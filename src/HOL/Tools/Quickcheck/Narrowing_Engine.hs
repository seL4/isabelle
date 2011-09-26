module Narrowing_Engine where {

import Monad;
import Control.Exception;
import System.IO;
import System.Exit;
import qualified Generated_Code;

type Pos = [Int];

-- Term refinement

new :: Pos -> [[Generated_Code.Narrowing_type]] -> [Generated_Code.Narrowing_term];
new p ps = [ Generated_Code.Ctr c (zipWith (\i t -> Generated_Code.Var (p++[i]) t) [0..] ts)
           | (c, ts) <- zip [0..] ps ];

refine :: Generated_Code.Narrowing_term -> Pos -> [Generated_Code.Narrowing_term];
refine (Generated_Code.Var p (Generated_Code.SumOfProd ss)) [] = new p ss;
refine (Generated_Code.Ctr c xs) p = map (Generated_Code.Ctr c) (refineList xs p);

refineList :: [Generated_Code.Narrowing_term] -> Pos -> [[Generated_Code.Narrowing_term]];
refineList xs (i:is) = let (ls, x:rs) = splitAt i xs in [ls ++ y:rs | y <- refine x is];

-- Find total instantiations of a partial value

total :: Generated_Code.Narrowing_term -> [Generated_Code.Narrowing_term];
total (Generated_Code.Ctr c xs) = [Generated_Code.Ctr c ys | ys <- mapM total xs];
total (Generated_Code.Var p (Generated_Code.SumOfProd ss)) = [y | x <- new p ss, y <- total x];

-- Answers

answeri :: a -> (a -> IO b) -> (Pos -> IO b) -> IO b;
answeri a known unknown =
  try (evaluate a) >>= (\res ->
     case res of
       Right b -> known b
       Left (ErrorCall ('\0':p)) -> unknown (map fromEnum p)
       Left e -> throw e);

answer :: Bool -> (Bool -> IO b) -> (Pos -> IO b) -> IO b;
answer a known unknown =
  Control.Exception.catch (answeri a known unknown) 
    (\ (PatternMatchFail _) -> known True);

-- Refute

str_of_list [] = "[]";
str_of_list (x:xs) = "(" ++ x ++ " :: " ++ str_of_list xs ++ ")";

report :: Result -> [Generated_Code.Narrowing_term] -> IO Int;
report r xs = putStrLn ("SOME (" ++ (str_of_list $ zipWith ($) (showArgs r) xs) ++ ")") >> hFlush stdout >> exitWith ExitSuccess;

eval :: Bool -> (Bool -> IO a) -> (Pos -> IO a) -> IO a;
eval p k u = answer p (\p -> answer p k u) u;

ref :: Result -> [Generated_Code.Narrowing_term] -> IO Int;
ref r xs = eval (apply_fun r xs) (\res -> if res then return 1 else report r xs) (\p -> sumMapM (ref r) 1 (refineList xs p));
          
refute :: Result -> IO Int;
refute r = ref r (args r);

sumMapM :: (a -> IO Int) -> Int -> [a] -> IO Int;
sumMapM f n [] = return n;
sumMapM f n (a:as) = seq n (do m <- f a ; sumMapM f (n+m) as);

-- Testable

instance Show Generated_Code.Typerep where {
  show (Generated_Code.Typerep c ts) = "Type (\"" ++ c ++ "\", " ++ show ts ++ ")";
};

instance Show Generated_Code.Term where {
  show (Generated_Code.Const c t) = "Const (\"" ++ c ++ "\", " ++ show t ++ ")";
  show (Generated_Code.App s t) = "(" ++ show s ++ ") $ (" ++ show t ++ ")";
  show (Generated_Code.Abs s ty t) = "Abs (\"" ++ s ++ "\", " ++ show ty ++ ", " ++ show t ++ ")";
  show (Generated_Code.Free s ty) = "Free (\"" ++ s ++  "\", " ++ show ty ++ ")";
};

data Result =
  Result { args     :: [Generated_Code.Narrowing_term]
         , showArgs :: [Generated_Code.Narrowing_term -> String]
         , apply_fun    :: [Generated_Code.Narrowing_term] -> Bool
         };

data P = P (Int -> Int -> Result);

run :: Testable a => ([Generated_Code.Narrowing_term] -> a) -> Int -> Int -> Result;
run a = let P f = property a in f;

class Testable a where {
  property :: ([Generated_Code.Narrowing_term] -> a) -> P;
};

instance Testable Bool where {
  property app = P $ \n d -> Result [] [] (app . reverse);
};

instance (Generated_Code.Partial_term_of a, Generated_Code.Narrowing a, Testable b) => Testable (a -> b) where {
  property f = P $ \n d ->
    let Generated_Code.C t c = Generated_Code.narrowing d
        c' = Generated_Code.conv c
        r = run (\(x:xs) -> f xs (c' x)) (n+1) d
    in  r { args = Generated_Code.Var [n] t : args r,
      showArgs = (show . Generated_Code.partial_term_of (Generated_Code.Type :: Generated_Code.Itself a)) : showArgs r };
};

-- Top-level interface

depthCheck :: Testable a => Int -> a -> IO ();
depthCheck d p =
  (refute $ run (const p) 0 d) >> putStrLn ("NONE") >> hFlush stdout;

smallCheck :: Testable a => Int -> a -> IO ();
smallCheck d p = mapM_ (`depthCheck` p) [0..d] >> putStrLn ("NONE") >> hFlush stdout;

}

