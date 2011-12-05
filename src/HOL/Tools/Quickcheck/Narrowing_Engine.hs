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

answeri :: a -> (Bool -> a -> IO b) -> (Pos -> IO b) -> IO b;
answeri a known unknown =
  try (evaluate a) >>= (\res ->
     case res of
       Right b -> known True b
       Left (ErrorCall ('\0':p)) -> unknown (map fromEnum p)
       Left e -> throw e);

answer :: Bool -> Bool -> (Bool -> Bool -> IO b) -> (Pos -> IO b) -> IO b;
answer potential a known unknown =
  Control.Exception.catch (answeri a known unknown) 
    (\ (PatternMatchFail _) -> known False (not potential));

-- Refute

str_of_list [] = "[]";
str_of_list (x:xs) = "(" ++ x ++ " :: " ++ str_of_list xs ++ ")";

report :: Bool -> Result -> [Generated_Code.Narrowing_term] -> IO Int;
report genuine r xs = putStrLn ("SOME (" ++ (if genuine then "true" else "false") ++
  ", " ++ (str_of_list $ zipWith ($) (showArgs r) xs) ++ ")") >> hFlush stdout >> exitWith ExitSuccess;

eval :: Bool -> Bool -> (Bool -> Bool -> IO a) -> (Pos -> IO a) -> IO a;
eval potential p k u = answer potential p k u;

ref :: Bool -> Result -> [Generated_Code.Narrowing_term] -> IO Int;
ref potential r xs = eval potential (apply_fun r xs) (\genuine res -> if res then return 1 else report genuine r xs)
  (\p -> sumMapM (ref potential r) 1 (refineList xs p));

refute :: Bool -> Result -> IO Int;
refute potential r = ref potential r (args r);

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

depthCheck :: Testable a => Bool -> Int -> a -> IO ();
depthCheck potential d p =
  (refute potential $ run (const p) 0 d) >> putStrLn ("NONE") >> hFlush stdout;

smallCheck :: Testable a => Bool -> Int -> a -> IO ();
smallCheck potential d p = mapM_ (\d -> depthCheck potential d p) [0..d] >> putStrLn ("NONE") >> hFlush stdout;

}
