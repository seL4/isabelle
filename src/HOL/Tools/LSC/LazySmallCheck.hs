module LazySmallCheck where {

import Monad;
import Control.Exception;
import System.IO;
import System.Exit;
import Code;

type Pos = [Integer];

-- Term refinement

new :: Pos -> [[Type]] -> [Term];
new p ps = [ Ctr c (zipWith (\i t -> Var (p++[i]) t) [0..] ts)
           | (c, ts) <- zip [0..] ps ];

refine :: Term -> Pos -> [Term];
refine (Var p (SumOfProd ss)) [] = new p ss;
refine (Ctr c xs) p = map (Ctr c) (refineList xs p);

refineList :: [Term] -> Pos -> [[Term]];
refineList xs (i:is) = let (ls, x:rs) = splitAt (fromInteger i) xs in [ls ++ y:rs | y <- refine x is];

-- Find total instantiations of a partial value

total :: Term -> [Term];
total (Ctr c xs) = [Ctr c ys | ys <- mapM total xs];
total (Var p (SumOfProd ss)) = [y | x <- new p ss, y <- total x];

-- Answers

answer :: a -> (a -> IO b) -> (Pos -> IO b) -> IO b;
answer a known unknown =
  try (evaluate a) >>= (\res ->
     case res of
       Right b -> known b
       Left (ErrorCall ('\0':p)) -> unknown (map (toInteger . fromEnum) p)
       Left e -> throw e);

-- Refute

str_of_list [] = "[]";
str_of_list (x:xs) = "(" ++ x ++ " :: " ++ str_of_list xs ++ ")";

report :: Result -> [Term] -> IO Integer;
report r xs = putStrLn ("SOME (" ++ (str_of_list $ zipWith ($) (showArgs r) $ head [ys | ys <- mapM total xs]) ++ ")") >> hFlush stdout >> exitWith ExitSuccess;

eval :: Bool -> (Bool -> IO a) -> (Pos -> IO a) -> IO a;
eval p k u = answer p (\p -> answer p k u) u;

ref :: Result -> [Term] -> IO Integer;
ref r xs = eval (apply_fun r xs) (\res -> if res then return 1 else report r xs) (\p -> sumMapM (ref r) 1 (refineList xs p));
          
refute :: Result -> IO Integer;
refute r = ref r (args r);

sumMapM :: (a -> IO Integer) -> Integer -> [a] -> IO Integer;
sumMapM f n [] = return n;
sumMapM f n (a:as) = seq n (do m <- f a ; sumMapM f (n+m) as);

-- Testable

instance Show Typerep where {
  show (Typerepa c ts) = "Type (\"" ++ c ++ "\", " ++ show ts ++ ")";
};

instance Show Terma where {
  show (Const c t) = "Const (\"" ++ c ++ "\", " ++ show t ++ ")";
  show (App s t) = "(" ++ show s ++ ") $ (" ++ show t ++ ")";
  show (Abs s ty t) = "Abs (\"" ++ s ++ "\", " ++ show ty ++ ", " ++ show t ++ ")";  
};

data Result =
  Result { args     :: [Term]
         , showArgs :: [Term -> String]
         , apply_fun    :: [Term] -> Bool
         };

data P = P (Integer -> Integer -> Result);

run :: Testable a => ([Term] -> a) -> Integer -> Integer -> Result;
run a = let P f = property a in f;

class Testable a where {
  property :: ([Term] -> a) -> P;
};

instance Testable Bool where {
  property app = P $ \n d -> Result [] [] (app . reverse);
};

instance (Term_of a, Serial a, Testable b) => Testable (a -> b) where {
  property f = P $ \n d ->
    let C t c = series d
        c' = conv c
        r = run (\(x:xs) -> f xs (c' x)) (n+1) d
    in  r { args = Var [n] t : args r, showArgs = (show . term_of . c') : showArgs r };
};

-- Top-level interface

depthCheck :: Testable a => Integer -> a -> IO ();
depthCheck d p =
  (refute $ run (const p) 0 d) >>= (\n -> putStrLn $ "OK, required " ++ show n ++ " tests at depth " ++ show d);

smallCheck :: Testable a => Integer -> a -> IO ();
smallCheck d p = mapM_ (`depthCheck` p) [0..d] >> putStrLn ("NONE");

}

