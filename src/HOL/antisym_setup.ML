local

val order_antisym_conv = thm "order_antisym_conv"
val linorder_antisym_conv1 = thm "linorder_antisym_conv1"
val linorder_antisym_conv2 = thm "linorder_antisym_conv2"
val linorder_antisym_conv3 = thm "linorder_antisym_conv3"

fun prp t thm = (#prop(rep_thm thm) = t);

fun prove_antisym_le sg ss ((le as Const(_,T)) $ r $ s) =
  let val prems = prems_of_ss ss;
      val less = Const("op <",T);
      val t = HOLogic.mk_Trueprop(le $ s $ r);
  in case Library.find_first (prp t) prems of
       None =>
         let val t = HOLogic.mk_Trueprop(HOLogic.not_const $ (less $ r $ s))
         in case Library.find_first (prp t) prems of
              None => None
            | Some thm => Some(mk_meta_eq(thm RS linorder_antisym_conv1))
         end
     | Some thm => Some(mk_meta_eq(thm RS order_antisym_conv))
  end
  handle THM _ => None;

fun prove_antisym_less sg ss (NotC $ ((less as Const(_,T)) $ r $ s)) =
  let val prems = prems_of_ss ss;
      val le = Const("op <=",T);
      val t = HOLogic.mk_Trueprop(le $ r $ s);
  in case Library.find_first (prp t) prems of
       None =>
         let val t = HOLogic.mk_Trueprop(NotC $ (less $ s $ r))
         in case Library.find_first (prp t) prems of
              None => None
            | Some thm => Some(mk_meta_eq(thm RS linorder_antisym_conv3))
         end
     | Some thm => Some(mk_meta_eq(thm RS linorder_antisym_conv2))
  end
  handle THM _ => None;

val antisym_le = Simplifier.simproc (Theory.sign_of (the_context()))
  "antisym le" ["(x::'a::order) <= y"] prove_antisym_le;
val antisym_less = Simplifier.simproc (Theory.sign_of (the_context()))
  "antisym less" ["~ (x::'a::linorder) < y"] prove_antisym_less;

in

val antisym_setup =
 [Simplifier.change_simpset_of (op addsimprocs) [antisym_le,antisym_less]];

end