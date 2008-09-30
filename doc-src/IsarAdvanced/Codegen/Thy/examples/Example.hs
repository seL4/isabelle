module Example where {


foldla :: forall a b. (a -> b -> a) -> a -> [b] -> a;
foldla f a [] = a;
foldla f a (x : xs) = foldla f (f a x) xs;

rev :: forall a. [a] -> [a];
rev xs = foldla (\ xsa x -> x : xsa) [] xs;

list_case :: forall t a. t -> (a -> [a] -> t) -> [a] -> t;
list_case f1 f2 (a : list) = f2 a list;
list_case f1 f2 [] = f1;

data Queue a = Queue [a] [a];

empty :: forall a. Queue a;
empty = Queue [] [];

dequeue :: forall a. Queue a -> (Maybe a, Queue a);
dequeue (Queue [] []) = (Nothing, Queue [] []);
dequeue (Queue xs (y : ys)) = (Just y, Queue xs ys);
dequeue (Queue (v : va) []) =
  let {
    (y : ys) = rev (v : va);
  } in (Just y, Queue [] ys);

enqueue :: forall a. a -> Queue a -> Queue a;
enqueue x (Queue xs ys) = Queue (x : xs) ys;

}
