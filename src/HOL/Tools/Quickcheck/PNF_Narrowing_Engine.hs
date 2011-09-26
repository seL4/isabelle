{-
A narrowing-based Evaluator for Formulas in Prefix Normal Form based on the compilation technique of LazySmallCheck
-}
module Narrowing_Engine where

import Monad
import Control.Exception
import System.Exit
import Maybe
import List (partition, findIndex)
import qualified Generated_Code


type Pos = [Int]

-- Term refinement

-- Operation: termOf

posOf :: Edge -> Pos
posOf (VN pos _) = pos
posOf (CtrB pos _) = pos

tailPosEdge :: Edge -> Edge
tailPosEdge (VN pos ty) = VN (tail pos) ty
tailPosEdge (CtrB pos ts) = CtrB (tail pos) ts

termOf :: Pos -> Path -> Generated_Code.Narrowing_term
termOf pos (CtrB [] i : es) = Generated_Code.Ctr i (termListOf pos es)
termOf pos [VN [] ty] = Generated_Code.Var pos ty

termListOf :: Pos -> Path -> [Generated_Code.Narrowing_term]
termListOf pos es = termListOf' 0 es
  where
    termListOf' i [] = []
    termListOf' i (e : es) =
      let 
        (ts, rs) = List.partition (\e -> head (posOf e) == i) (e : es)
        t = termOf (pos ++ [i]) (map tailPosEdge ts)
      in
        (t : termListOf' (i + 1) rs) 
{-
conv :: [[Term] -> a] -> Term -> a
conv cs (Var p _) = error ('\0':map toEnum p)
conv cs (Ctr i xs) = (cs !! i) xs
-}
-- Answers

data Answer = Known Bool | Unknown Pos deriving Show;

answeri :: a -> (a -> IO b) -> (Pos -> IO b) -> IO b;
answeri a known unknown =
  do res <- try (evaluate a)
     case res of
       Right b -> known b
       Left (ErrorCall ('\0':p)) -> unknown (map fromEnum p)
       Left e -> throw e

answer :: Bool -> (Bool -> IO b) -> (Pos -> IO b) -> IO b;
answer a known unknown =
  Control.Exception.catch (answeri a known unknown) 
    (\ (PatternMatchFail _) -> known True)

--  Proofs and Refutation

data Quantifier = ExistentialQ | UniversalQ

data EvaluationResult = Eval Bool | UnknownValue Bool deriving Eq
{-
instance Show EvaluationResult where
  show (Eval True) = "T"
  show (Eval False) = "F"
  show (UnknownValue False) = "U"
  show (UnknownValue True) = "X"
-}
uneval = UnknownValue True
unknown = UnknownValue False

andOp :: EvaluationResult -> EvaluationResult -> EvaluationResult
andOp (Eval b1) (Eval b2) = Eval (b1 && b2)
andOp (Eval True) (UnknownValue b) = UnknownValue b
andOp (Eval False) (UnknownValue _) = Eval False
andOp (UnknownValue b) (Eval True) = UnknownValue b
andOp (UnknownValue _) (Eval False) = Eval False
andOp (UnknownValue b1) (UnknownValue b2) = UnknownValue (b1 || b2)

orOp :: EvaluationResult -> EvaluationResult -> EvaluationResult
orOp (Eval b1) (Eval b2) = Eval (b1 || b2)
orOp (Eval False) (UnknownValue b) = UnknownValue b
orOp (Eval True) (UnknownValue _) = Eval True
orOp (UnknownValue b) (Eval False) = UnknownValue b
orOp (UnknownValue _) (Eval True) = Eval True
orOp (UnknownValue b1) (UnknownValue b2) = UnknownValue (b1 && b2)


data Edge = VN Pos Generated_Code.Narrowing_type | CtrB Pos Int
type Path = [Edge]

data QuantTree = Node EvaluationResult
  | VarNode Quantifier EvaluationResult Pos Generated_Code.Narrowing_type QuantTree
  | CtrBranch Quantifier EvaluationResult Pos [QuantTree]
{-
instance Show QuantTree where
  show (Node r) = "Node " ++ show r
  show (VarNode q r p _ t) = "VarNode " ++ show q ++ " " ++ show r ++ " " ++ show p ++ " " ++ show t
  show (CtrBranch q r p ts) = "CtrBranch " ++ show q ++ show r ++ show p ++ show ts
-}
evalOf :: QuantTree -> EvaluationResult
evalOf (Node r) = r
evalOf (VarNode _ r _ _ _) = r
evalOf (CtrBranch _ r _ _) = r

-- Operation find: finds first relevant unevaluated node and returns its path

find :: QuantTree -> Path
find (Node (UnknownValue True)) = []
find (VarNode _ _ pos ty t) = VN pos ty : (find t)
find (CtrBranch _ _ pos ts) = CtrB pos i : find (ts !! i)
  where  
    Just i = findIndex (\t -> evalOf t == uneval) ts

-- Operation: updateNode ( and simplify)

{- updates the Node and the stored evaluation results along the upper nodes -}
updateNode :: Path -> EvaluationResult -> QuantTree -> QuantTree
updateNode [] v (Node _) = Node v
updateNode (VN _ _ : es) v (VarNode q r p ty t) = VarNode q (evalOf t') p ty t'
  where
    t' = updateNode es v t    
updateNode (CtrB _ i : es) v (CtrBranch q r pos ts) = CtrBranch q r' pos ts' 
  where
    (xs, y : ys) = splitAt i ts
    y' = updateNode es v y
    ts' = xs ++ (y' : ys)
    r' = foldl (\s t -> oper s (evalOf t)) neutral ts'
    (neutral, oper) = case q of { UniversalQ -> (Eval True, andOp); ExistentialQ -> (Eval False, orOp)}
 
-- Operation: refineTree

updateTree :: (QuantTree -> QuantTree) -> Path -> QuantTree -> QuantTree
updateTree f [] t = (f t)
updateTree f (VN _ _ : es) (VarNode q r pos ty t) = VarNode q r pos ty (updateTree f es t)
updateTree f (CtrB _ i : es) (CtrBranch q r pos ts) = CtrBranch q r pos (xs ++ (updateTree f es y : ys))
   where
     (xs, y : ys) = splitAt i ts

refineTree :: [Edge] -> Pos -> QuantTree -> QuantTree
refineTree es p t = updateTree refine (pathPrefix p es) t
  where
    pathPrefix p es = takeWhile (\e -> posOf e /= p) es  
    refine (VarNode q r p (Generated_Code.SumOfProd ps) t) =
      CtrBranch q r p [ foldr (\(i,ty) t -> VarNode q r (p++[i]) ty t) t (zip [0..] ts) | ts <- ps ]

-- refute

refute :: ([Generated_Code.Narrowing_term] -> Bool) -> Int -> QuantTree -> IO QuantTree
refute exec d t = ref t
  where
    ref t =
      let path = find t in
        do
          t' <- answer (exec (termListOf [] path)) (\b -> return (updateNode path (Eval b) t))
            (\p -> return (if length p < d then refineTree path p t else updateNode path unknown t));
          case evalOf t' of
            UnknownValue True -> ref t'
            _ -> return t'

depthCheck :: Int -> Generated_Code.Property -> IO ()
depthCheck d p = refute (checkOf p) d (treeOf 0 p) >>= (\t -> 
  case evalOf t of
   Eval False -> putStrLn ("SOME (" ++ show (counterexampleOf (reifysOf p) (exampleOf 0 t)) ++ ")")  
   _ -> putStrLn ("NONE"))


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
termlist_of :: Pos -> ([Generated_Code.Narrowing_term], QuantTree) -> ([Generated_Code.Narrowing_term], QuantTree)
termlist_of p' (terms, Node b) = (terms, Node b) 
termlist_of p' (terms, VarNode q r p ty t) = if p' == take (length p') p then
    termlist_of p' (terms ++ [Generated_Code.Var p ty], t)
  else
    (terms, VarNode q r p ty t)
termlist_of p' (terms, CtrBranch q r p ts) = if p' == take (length p') p then
    let
      Just i = findIndex (\t -> evalOf t == Eval False) ts
      (subterms, t') = fixp (\j -> termlist_of (p ++ [j])) 0 ([], ts !! i)
    in
      (terms ++ [Generated_Code.Ctr i subterms], t')
  else
    (terms, CtrBranch q r p ts)
  where
    fixp f j s = if length (fst (f j s)) == length (fst s) then s else fixp f (j + 1) (f j s)


alltermlist_of :: Pos -> ([Generated_Code.Narrowing_term], QuantTree) -> [([Generated_Code.Narrowing_term], QuantTree)]
alltermlist_of p' (terms, Node b) = [(terms, Node b)] 
alltermlist_of p' (terms, VarNode q r p ty t) = if p' == take (length p') p then
    alltermlist_of p' (terms ++ [Generated_Code.Var p ty], t)
  else
    [(terms, VarNode q r p ty t)]
alltermlist_of p' (terms, CtrBranch q r p ts) =
  if p' == take (length p') p then
    let
      its = filter (\(i, t) -> evalOf t == Eval False) (zip [0..] ts)
    in
      concatMap
        (\(i, t) -> map (\(subterms, t') -> (terms ++ [Generated_Code.Ctr i subterms], t'))
           (fixp (\j -> alltermlist_of (p ++ [j])) 0 ([], t))) its
  else
    [(terms, CtrBranch q r p ts)]
  where
    fixp f j s = case (f j s) of
      [s'] -> if length (fst s') == length (fst s) then [s'] else concatMap (fixp f (j + 1)) (f j s)
      _ -> concatMap (fixp f (j + 1)) (f j s)

data Example = UnivExample Generated_Code.Narrowing_term Example | ExExample [(Generated_Code.Narrowing_term, Example)] | EmptyExample

quantifierOf (VarNode q _ _ _ _) = q
quantifierOf (CtrBranch q _ _ _) = q

exampleOf :: Int -> QuantTree -> Example
exampleOf _ (Node _) = EmptyExample
exampleOf p t =
   case quantifierOf t of
     UniversalQ ->
       let
         ([term], rt) = termlist_of [p] ([], t)
       in UnivExample term (exampleOf (p + 1) rt)
     ExistentialQ ->
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

dummy = Generated_Code.Var [] (Generated_Code.SumOfProd [[]])

treeOf :: Int -> Generated_Code.Property -> QuantTree
treeOf n (Generated_Code.Property _) = Node uneval
treeOf n (Generated_Code.Universal ty f _)  = VarNode UniversalQ uneval [n] ty (treeOf (n + 1) (f dummy)) 
treeOf n (Generated_Code.Existential ty f _) = VarNode ExistentialQ uneval [n] ty (treeOf (n + 1) (f dummy))

reifysOf :: Generated_Code.Property -> [Generated_Code.Narrowing_term -> Generated_Code.Term]
reifysOf (Generated_Code.Property _) = []
reifysOf (Generated_Code.Universal _ f r)  = (r : (reifysOf (f dummy)))
reifysOf (Generated_Code.Existential _ f r) = (r : (reifysOf (f dummy)))

