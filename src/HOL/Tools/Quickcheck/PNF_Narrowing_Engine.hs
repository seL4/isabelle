{-
A narrowing-based Evaluator for Formulas in Prefix Normal Form based on the compilation technique of LazySmallCheck
-}
module Narrowing_Engine where

import Control.Monad
import Control.Exception
import System.IO
import System.Exit
import Data.Maybe
import Data.List (partition, findIndex)
import qualified Generated_Code

type Pos = [Int]

--  Refinement Tree

data Quantifier = Existential | Universal

data Truth = Eval Bool | Unevaluated | Unknown deriving Eq

conj :: Truth -> Truth -> Truth
conj (Eval True) b = b
conj (Eval False) _ = Eval False
conj b (Eval True) = b
conj _ (Eval False) = Eval False
conj Unevaluated _ = Unevaluated
conj _ Unevaluated = Unevaluated
conj Unknown Unknown = Unknown

disj :: Truth -> Truth -> Truth
disj (Eval True) _ = Eval True
disj (Eval False) b = b
disj _ (Eval True) = Eval True
disj b (Eval False) = b
disj Unknown _ = Unknown
disj _ Unknown = Unknown
disj Unevaluated Unevaluated = Unevaluated

ball ts = foldl (\s t -> conj s (value_of t)) (Eval True) ts
bexists ts = foldl (\s t -> disj s (value_of t)) (Eval False) ts

data Tree = Leaf Truth
  | Variable Quantifier Truth Pos Generated_Code.Narrowing_type Tree
  | Constructor Quantifier Truth Pos [Tree]

value_of :: Tree -> Truth
value_of (Leaf r) = r
value_of (Variable _ r _ _ _) = r
value_of (Constructor _ r _ _) = r

data Edge = V Pos Generated_Code.Narrowing_type | C Pos Int
type Path = [Edge]

position_of :: Edge -> Pos
position_of (V pos _) = pos
position_of (C pos _) = pos

-- Operation find: finds first relevant unevaluated node and returns its path

find :: Tree -> Path
find (Leaf Unevaluated) = []
find (Variable _ _ pos ty t) = V pos ty : (find t)
find (Constructor _ _ pos ts) = C pos i : find (ts !! i)
  where  
    Just i = findIndex (\t -> value_of t == Unevaluated) ts

-- Operation update: updates the leaf and the cached truth values results along the path

update :: Path -> Truth -> Tree -> Tree
update [] v (Leaf _) = Leaf v
update (V _ _ : es) v (Variable q r p ty t) = Variable q (value_of t') p ty t'
  where
    t' = update es v t    
update (C _ i : es) v (Constructor q r pos ts) = Constructor q r' pos ts' 
  where
    (xs, y : ys) = splitAt i ts
    y' = update es v y
    ts' = xs ++ (y' : ys)
    r' = valueOf ts'
    valueOf = case q of { Universal -> ball; Existential -> bexists}
 
-- Operation: refineTree

replace :: (Tree -> Tree) -> Path -> Tree -> Tree
replace f [] t = (f t)
replace f (V _ _ : es) (Variable q r pos ty t) = Variable q r pos ty (replace f es t)
replace f (C _ i : es) (Constructor q r pos ts) = Constructor q r pos (xs ++ (replace f es y : ys))
   where
     (xs, y : ys) = splitAt i ts

refine_tree :: [Edge] -> Pos -> Tree -> Tree
refine_tree es p t = replace refine (path_of_position p es) t
  where
    path_of_position p es = takeWhile (\e -> position_of e /= p) es  
    refine (Variable q r p (Generated_Code.Narrowing_sum_of_products ps) t) =
      Constructor q r p [ foldr (\(i,ty) t -> Variable q r (p++[i]) ty t) t (zip [0..] ts) | ts <- ps ]

-- refute

refute :: ([Generated_Code.Narrowing_term] -> Bool) -> Bool -> Int -> Tree -> IO Tree
refute exec genuine_only d t = ref t
  where
    ref t =
      let path = find t in
        do
          t' <- answer genuine_only (exec (terms_of [] path)) (\b -> return (update path (Eval b) t))
            (\p -> return (if length p < d then refine_tree path p t else update path Unknown t));
          case value_of t' of
            Unevaluated -> ref t'
            _ -> return t'

depthCheck :: Bool -> Int -> Generated_Code.Property -> IO ()
depthCheck genuine_only d p = refute (checkOf p) genuine_only d (treeOf 0 p) >>= (\t -> 
  case value_of t of
   Eval False -> putStrLn ("SOME (" ++ show (counterexampleOf (reifysOf p) (exampleOf 0 t)) ++ ")")  
   _ -> putStrLn ("NONE"))

-- Term refinement

-- Operation: termOf

term_of :: Pos -> Path -> Generated_Code.Narrowing_term
term_of p (C [] i : es) = Generated_Code.Narrowing_constructor i (terms_of p es)
term_of p [V [] ty] = Generated_Code.Narrowing_variable p ty

terms_of :: Pos -> Path -> [Generated_Code.Narrowing_term]
terms_of p es = terms_of' 0 es
  where
    terms_of' i [] = []
    terms_of' i (e : es) = (t : terms_of' (i + 1) rs) 
      where
        (ts, rs) = Data.List.partition (\e -> head (position_of e) == i) (e : es)
        t = term_of (p ++ [i]) (map (map_pos tail) ts)
        map_pos f (V p ty) = V (f p) ty
        map_pos f (C p ts) = C (f p) ts

-- Answers

data Answer = Known Bool | Refine Pos;

answeri :: a -> (a -> IO b) -> (Pos -> IO b) -> IO b;
answeri a known unknown =
  do res <- try (evaluate a)
     case res of
       Right b -> known b
       Left (ErrorCall ('\0':p)) -> unknown (map fromEnum p)
       Left e -> throw e

answer :: Bool -> Bool -> (Bool -> IO b) -> (Pos -> IO b) -> IO b;
answer genuine_only a known unknown =
  Control.Exception.catch (answeri a known unknown) 
    (\ (PatternMatchFail _) -> known genuine_only)


-- presentation of counterexample


instance Show Generated_Code.Typerep where {
  show (Generated_Code.Typerep c ts) = "Type (\"" ++ c ++ "\", " ++ show ts ++ ")";
};

instance Show Generated_Code.Term where {
  show (Generated_Code.Const c t) = "Const (\"" ++ c ++ "\", " ++ show t ++ ")";
  show (Generated_Code.App s t) = "(" ++ show s ++ ") $ (" ++ show t ++ ")";
  show (Generated_Code.Abs s ty t) = "Abs (\"" ++ s ++ "\", " ++ show ty ++ ", " ++ show t ++ ")";
  show (Generated_Code.Free s ty) = "Free (\"" ++ s ++  "\", " ++ show ty ++ ")";
};
{-
posOf :: Edge -> Pos
posOf (VN pos _) = pos
posOf (CtrB pos _) = pos

tailPosEdge :: Edge -> Edge
tailPosEdge (VN pos ty) = VN (tail pos) ty
tailPosEdge (CtrB pos ts) = CtrB (tail pos) ts

termOf :: Pos -> Tree -> (Narrowing_term, Tree)
termOf pos = if Ctr i (termListOf (pos ++ [i]) )
termOf pos [VN [] ty] = Var pos ty

termListOf :: Pos -> [Narrowing_term]
termListOf pos es = termListOf' 0 es
  where
    termListOf' i [] = []
    termListOf' i (e : es) =
      let
        (ts, rs) = List.partition (\e -> head (posOf e) == i) (e : es)
        t = termOf (pos ++ [i]) (map tailPosEdge ts)
      in
        (t : termListOf' (i + 1) rs) 

termlist_of :: Pos -> QuantTree -> ([Term], QuantTree)

termlist_of p' (Node r)

term_of p' (VarNode _ _ p ty t) = if p == p' then
    (Some (Var ty), t)
  else
    (None, t)
term_of p' (CtrBranch q _ p ts) =
  if p == p' then
    let
      i = findindex (\t -> evalOf t == Eval False)        
    in
      Ctr i (termlist_of (p ++ [i])  (ts ! i) [])
  else
    error ""
-}
termlist_of :: Pos -> ([Generated_Code.Narrowing_term], Tree) -> ([Generated_Code.Narrowing_term], Tree)
termlist_of p' (terms, Leaf b) = (terms, Leaf b) 
termlist_of p' (terms, Variable q r p ty t) = if p' == take (length p') p then
    termlist_of p' (terms ++ [Generated_Code.Narrowing_variable p ty], t)
  else
    (terms, Variable q r p ty t)
termlist_of p' (terms, Constructor q r p ts) = if p' == take (length p') p then
    let
      Just i = findIndex (\t -> value_of t == Eval False) ts
      (subterms, t') = fixp (\j -> termlist_of (p ++ [j])) 0 ([], ts !! i)
    in
      (terms ++ [Generated_Code.Narrowing_constructor i subterms], t')
  else
    (terms, Constructor q r p ts)
  where
    fixp f j s = if length (fst (f j s)) == length (fst s) then s else fixp f (j + 1) (f j s)


alltermlist_of :: Pos -> ([Generated_Code.Narrowing_term], Tree) -> [([Generated_Code.Narrowing_term], Tree)]
alltermlist_of p' (terms, Leaf b) = [(terms, Leaf b)] 
alltermlist_of p' (terms, Variable q r p ty t) = if p' == take (length p') p then
    alltermlist_of p' (terms ++ [Generated_Code.Narrowing_variable p ty], t)
  else
    [(terms, Variable q r p ty t)]
alltermlist_of p' (terms, Constructor q r p ts) =
  if p' == take (length p') p then
    let
      its = filter (\(i, t) -> value_of t == Eval False) (zip [0..] ts)
    in
      concatMap
        (\(i, t) -> map (\(subterms, t') -> (terms ++ [Generated_Code.Narrowing_constructor i subterms], t'))
           (fixp (\j -> alltermlist_of (p ++ [j])) 0 ([], t))) its
  else
    [(terms, Constructor q r p ts)]
  where
    fixp f j s = case (f j s) of
      [s'] -> if length (fst s') == length (fst s) then [s'] else concatMap (fixp f (j + 1)) (f j s)
      _ -> concatMap (fixp f (j + 1)) (f j s)

data Example = UnivExample Generated_Code.Narrowing_term Example | ExExample [(Generated_Code.Narrowing_term, Example)] | EmptyExample

quantifierOf (Variable q _ _ _ _) = q
quantifierOf (Constructor q _ _ _) = q

exampleOf :: Int -> Tree -> Example
exampleOf _ (Leaf _) = EmptyExample
exampleOf p t =
   case quantifierOf t of
     Universal ->
       let
         ([term], rt) = termlist_of [p] ([], t)
       in UnivExample term (exampleOf (p + 1) rt)
     Existential ->
       ExExample (map (\([term], rt) -> (term, exampleOf (p + 1) rt)) (alltermlist_of [p] ([], t)))

data Counterexample = Universal_Counterexample (Generated_Code.Term, Counterexample)
  | Existential_Counterexample [(Generated_Code.Term, Counterexample)] | Empty_Assignment
  
instance Show Counterexample where {
show Empty_Assignment = "Narrowing_Generators.Empty_Assignment";
show (Universal_Counterexample x) = "Narrowing_Generators.Universal_Counterexample" ++ show x;
show (Existential_Counterexample x) = "Narrowing_Generators.Existential_Counterexample" ++ show x;
};

counterexampleOf :: [Generated_Code.Narrowing_term -> Generated_Code.Term] -> Example -> Counterexample
counterexampleOf [] EmptyExample = Empty_Assignment
counterexampleOf (reify : reifys) (UnivExample t ex) = Universal_Counterexample (reify t, counterexampleOf reifys ex)
counterexampleOf (reify : reifys) (ExExample exs) = Existential_Counterexample (map (\(t, ex) -> (reify t, counterexampleOf reifys ex)) exs)

checkOf :: Generated_Code.Property -> [Generated_Code.Narrowing_term] -> Bool
checkOf (Generated_Code.Property b) = (\[] -> b)
checkOf (Generated_Code.Universal _ f _) = (\(t : ts) -> checkOf (f t) ts)
checkOf (Generated_Code.Existential _ f _) = (\(t : ts) -> checkOf (f t) ts)

treeOf :: Int -> Generated_Code.Property -> Tree
treeOf n (Generated_Code.Property _) = Leaf Unevaluated
treeOf n (Generated_Code.Universal ty f _)  = Variable Universal Unevaluated [n] ty (treeOf (n + 1) (f undefined)) 
treeOf n (Generated_Code.Existential ty f _) = Variable Existential Unevaluated [n] ty (treeOf (n + 1) (f undefined))

reifysOf :: Generated_Code.Property -> [Generated_Code.Narrowing_term -> Generated_Code.Term]
reifysOf (Generated_Code.Property _) = []
reifysOf (Generated_Code.Universal _ f r)  = (r : (reifysOf (f undefined)))
reifysOf (Generated_Code.Existential _ f r) = (r : (reifysOf (f undefined)))

