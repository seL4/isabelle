(*  Title:      HOL/IOA/meta_theory/Solve.thy
    ID:         $Id$
    Author:     Tobias Nipkow & Konrad Slind
    Copyright   1994  TU Muenchen

Weak possibilities mapping (abstraction)
*)

Solve = IOA +

consts

  is_weak_pmap :: "['c => 'a, ('action,'c)ioa,('action,'a)ioa] => bool"

defs

is_weak_pmap_def
  "is_weak_pmap f C A ==                          \
\   (!s:starts_of(C). f(s):starts_of(A)) &        \
\   (!s t a. reachable C s &                      \
\            <s,a,t>:trans_of(C)                  \
\            --> (if a:externals(asig_of(C)) then \
\                   <f(s),a,f(t)>:trans_of(A)     \
\                 else f(s)=f(t)))"

end
