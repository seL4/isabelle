(*  Title:      HOL/AxClasses/Tutorial/Product.thy
    ID:         $Id$
    Author:     Markus Wenzel, TU Muenchen

Example 'syntactic' class "product", instantiated on type "bool".  At
first sight this may look like instance in Haskell, but is not quite
the same!
*)

theory Product = Main:;

axclass
  product < "term";
consts
  product :: "'a::product \\<Rightarrow> 'a \\<Rightarrow> 'a"    (infixl "\\<otimes>" 70);

instance bool :: product;
  by intro_classes;
defs
  product_bool_def: "x \\<otimes> y \\<equiv> x \\<and> y";

end;