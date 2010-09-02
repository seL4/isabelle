{-# OPTIONS_GHC -fglasgow-exts #-}

module Example where {

data Queue a = AQueue [a] [a];

empty :: forall a. Example.Queue a;
empty = Example.AQueue [] [];

dequeue :: forall a. Example.Queue a -> (Maybe a, Example.Queue a);
dequeue (Example.AQueue [] []) = (Nothing, Example.AQueue [] []);
dequeue (Example.AQueue xs (y : ys)) = (Just y, Example.AQueue xs ys);
dequeue (Example.AQueue (v : va) []) =
  let {
    (y : ys) = reverse (v : va);
  } in (Just y, Example.AQueue [] ys);

enqueue :: forall a. a -> Example.Queue a -> Example.Queue a;
enqueue x (Example.AQueue xs ys) = Example.AQueue (x : xs) ys;

}
