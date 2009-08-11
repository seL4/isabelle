{-# OPTIONS_GHC -fglasgow-exts #-}

module Example where {


foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

rev :: forall a. [a] -> [a];
rev xs = foldla (\ xsa x -> x : xsa) [] xs;

list_case :: forall a b. a -> (b -> [b] -> a) -> [b] -> a;
list_case f1 f2 (a : list) = f2 a list;
list_case f1 f2 [] = f1;

data Queue a = AQueue [a] [a];

empty :: forall a. Queue a;
empty = AQueue [] [];

dequeue :: forall a. Queue a -> (Maybe a, Queue a);
dequeue (AQueue [] []) = (Nothing, AQueue [] []);
dequeue (AQueue xs (y : ys)) = (Just y, AQueue xs ys);
dequeue (AQueue (v : va) []) =
  let {
    (y : ys) = rev (v : va);
  } in (Just y, AQueue [] ys);

enqueue :: forall a. a -> Queue a -> Queue a;
enqueue x (AQueue xs ys) = AQueue (x : xs) ys;

}
