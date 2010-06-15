{-# OPTIONS_GHC -fglasgow-exts #-}

module Example where {

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
