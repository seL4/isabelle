(*  Title:      HOL/Real/HahnBanach/FunctionOrder.thy
    ID:         $Id$
    Author:     Gertrud Bauer, TU Munich
*)

header {* An order on functions *}

theory FunctionOrder = Subspace + Linearform:

subsection {* The graph of a function *}

text{* We define the \emph{graph} of a (real) function $f$ with
domain $F$ as the set 
\[
\{(x, f\ap x). \ap x \in F\}
\]
So we are modeling partial functions by specifying the domain and 
the mapping function. We use the term ``function'' also for its graph.
*}

types 'a graph = "('a * real) set"

constdefs
  graph :: "['a set, 'a => real] => 'a graph "
  "graph F f == {(x, f x) | x. x \<in> F}" 

lemma graphI [intro?]: "x \<in> F ==> (x, f x) \<in> graph F f"
  by (unfold graph_def, intro CollectI exI) force

lemma graphI2 [intro?]: "x \<in> F ==> \<exists>t\<in> (graph F f). t = (x, f x)"
  by (unfold graph_def, force)

lemma graphD1 [intro?]: "(x, y) \<in> graph F f ==> x \<in> F"
  by (unfold graph_def, elim CollectE exE) force

lemma graphD2 [intro?]: "(x, y) \<in> graph H h ==> y = h x"
  by (unfold graph_def, elim CollectE exE) force 

subsection {* Functions ordered by domain extension *}

text{* A function $h'$ is an extension of $h$, iff the graph of 
$h$ is a subset of the graph of $h'$.*}

lemma graph_extI: 
  "[| !! x. x \<in> H ==> h x = h' x; H <= H'|]
  ==> graph H h <= graph H' h'"
  by (unfold graph_def, force)

lemma graph_extD1 [intro?]: 
  "[| graph H h <= graph H' h'; x \<in> H |] ==> h x = h' x"
  by (unfold graph_def, force)

lemma graph_extD2 [intro?]: 
  "[| graph H h <= graph H' h' |] ==> H <= H'"
  by (unfold graph_def, force)

subsection {* Domain and function of a graph *}

text{* The inverse functions to $\idt{graph}$ are $\idt{domain}$ and 
$\idt{funct}$.*}

constdefs
  domain :: "'a graph => 'a set" 
  "domain g == {x. \<exists>y. (x, y) \<in> g}"

  funct :: "'a graph => ('a => real)"
  "funct g == \<lambda>x. (SOME y. (x, y) \<in> g)"


text {* The following lemma states that $g$ is the graph of a function
if the relation induced by $g$ is unique. *}

lemma graph_domain_funct: 
  "(!!x y z. (x, y) \<in> g ==> (x, z) \<in> g ==> z = y) 
  ==> graph (domain g) (funct g) = g"
proof (unfold domain_def funct_def graph_def, auto)
  fix a b assume "(a, b) \<in> g"
  show "(a, SOME y. (a, y) \<in> g) \<in> g" by (rule selectI2)
  show "\<exists>y. (a, y) \<in> g" ..
  assume uniq: "!!x y z. (x, y) \<in> g ==> (x, z) \<in> g ==> z = y"
  show "b = (SOME y. (a, y) \<in> g)"
  proof (rule select_equality [symmetric])
    fix y assume "(a, y) \<in> g" show "y = b" by (rule uniq)
  qed
qed



subsection {* Norm-preserving extensions of a function *}

text {* Given a linear form $f$ on the space $F$ and a seminorm $p$ on 
$E$. The set of all linear extensions of $f$, to superspaces $H$ of 
$F$, which are bounded by $p$, is defined as follows. *}


constdefs
  norm_pres_extensions :: 
    "['a::{plus, minus, zero} set, 'a  => real, 'a set, 'a => real] 
    => 'a graph set"
    "norm_pres_extensions E p F f 
    == {g. \<exists>H h. graph H h = g 
                \<and> is_linearform H h 
                \<and> is_subspace H E
                \<and> is_subspace F H
                \<and> graph F f <= graph H h
                \<and> (\<forall>x \<in> H. h x <= p x)}"
                       
lemma norm_pres_extension_D:  
  "g \<in> norm_pres_extensions E p F f
  ==> \<exists>H h. graph H h = g 
            \<and> is_linearform H h 
            \<and> is_subspace H E
            \<and> is_subspace F H
            \<and> graph F f <= graph H h
            \<and> (\<forall>x \<in> H. h x <= p x)"
  by (unfold norm_pres_extensions_def) force

lemma norm_pres_extensionI2 [intro]:  
  "[| is_linearform H h; is_subspace H E; is_subspace F H;
  graph F f <= graph H h; \<forall>x \<in> H. h x <= p x |]
  ==> (graph H h \<in> norm_pres_extensions E p F f)"
 by (unfold norm_pres_extensions_def) force

lemma norm_pres_extensionI [intro]:  
  "\<exists>H h. graph H h = g 
         \<and> is_linearform H h    
         \<and> is_subspace H E
         \<and> is_subspace F H
         \<and> graph F f <= graph H h
         \<and> (\<forall>x \<in> H. h x <= p x)
  ==> g \<in> norm_pres_extensions E p F f"
  by (unfold norm_pres_extensions_def) force

end