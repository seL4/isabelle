
theory FunctionOrder = Subspace + Linearform:;


section {* Order on functions *};

types 'a graph = "('a * real) set";

constdefs
  graph :: "['a set, 'a => real] => 'a graph "
  "graph F f == {p. EX x. p = (x, f x) & x:F}"; (* == {(x, f x). x:F} *)

constdefs
  domain :: "'a graph => 'a set" 
  "domain g == {x. EX y. (x, y):g}";

constdefs
  funct :: "'a graph => ('a => real)"
  "funct g == %x. (@ y. (x, y):g)";

lemma graph_I: "x:F ==> (x, f x) : graph F f";
  by (unfold graph_def, intro CollectI exI) force;

lemma graphD1: "(x, y): graph F f ==> x:F";
  by (unfold graph_def, elim CollectD [elimify] exE) force;

lemma graph_domain_funct: "(!!x y z. (x, y):g ==> (x, z):g ==> z = y) ==> graph (domain g) (funct g) = g";
proof ( unfold domain_def, unfold funct_def, unfold graph_def, auto);
  fix a b; assume "(a, b) : g";
  show "(a, SOME y. (a, y) : g) : g"; by (rule selectI2);
  show "EX y. (a, y) : g"; ..;
  assume uniq: "!!x y z. (x, y):g ==> (x, z):g ==> z = y";
  show "b = (SOME y. (a, y) : g)";
  proof (rule select_equality [RS sym]);
    fix y; assume "(a, y):g"; show "y = b"; by (rule uniq);
  qed;
qed;

lemma graph_lemma1: "x:F ==> EX t: (graph F f). t = (x, f x)";
  by (unfold graph_def, force);

lemma graph_lemma2: "(x, y): graph H h ==> y = h x";
  by (unfold graph_def, elim CollectD [elimify] exE) force; 

lemma graph_lemma3: "[| graph H h <= graph H' h'; x:H |] ==> h x = h' x";
  by (unfold graph_def, force);

lemma graph_lemma4: "[| graph H h <= graph H' h' |] ==> H <= H'";
  by (unfold graph_def, force);

lemma graph_lemma5: "[| !! x. x: H ==> h x = h' x; H <= H'|] ==> graph H h <= graph H' h'";
  by (unfold graph_def, force);


constdefs
  norm_prev_extensions :: 
   "['a set, 'a  => real, 'a set, 'a => real] => 'a graph set"
  "norm_prev_extensions E p F f == {g. EX H h. graph H h = g 
                                             & is_linearform H h 
                                             & is_subspace H E
                                             & is_subspace F H
                                             & (graph F f <= graph H h)
                                             & (ALL x:H. h x <= p x)}";
                       
lemma norm_prev_extension_D:  
  "(g: norm_prev_extensions E p F f) ==> (EX H h. graph H h = g 
                                              & is_linearform H h 
                                              & is_subspace H E
                                              & is_subspace F H
                                              & (graph F f <= graph H h)
                                              & (ALL x:H. h x <= p x))";
 by (unfold norm_prev_extensions_def) force;

lemma norm_prev_extension_I2 [intro]:  
   "[| is_linearform H h;    
       is_subspace H E;
       is_subspace F H;
       (graph F f <= graph H h);
       (ALL x:H. h x <= p x) |]
   ==> (graph H h : norm_prev_extensions E p F f)";
 by (unfold norm_prev_extensions_def) force;

lemma norm_prev_extension_I [intro]:  
   "(EX H h. graph H h = g 
             & is_linearform H h    
             & is_subspace H E
             & is_subspace F H
             & (graph F f <= graph H h)
             & (ALL x:H. h x <= p x))
   ==> (g: norm_prev_extensions E p F f) ";
 by (unfold norm_prev_extensions_def) force;


end;

