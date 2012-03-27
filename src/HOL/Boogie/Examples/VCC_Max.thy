(*  Title:      HOL/Boogie/Examples/VCC_Max.thy
    Author:     Sascha Boehme, TU Muenchen
*)

header {* Boogie example from VCC: get the greatest element of a list *}

theory VCC_Max
imports Boogie
uses ("VCC_Max.b2i")
begin

text {*
We prove correct the verification condition generated from the following
C code:

\begin{verbatim}
#include "vcc.h"

typedef unsigned char byte;
typedef unsigned long ulong;

static byte maximum(byte arr[], ulong len)
  requires(wrapped(as_array(arr, len)))
  requires (0 < len && len < (1UI64 << 40))
  ensures (forall(ulong i; i<len ==> arr[i] <= result))
  ensures (exists(ulong i; i<len && arr[i] == result))
{
  byte max = arr[0];
  ulong p;
  spec(ulong witness = 0;)

  for (p = 1; p < len; p++)
    invariant(p <= len)
    invariant(forall(ulong i; i < p ==> arr[i] <= max))
    invariant(witness < len && arr[witness] == max)
  {
    if (arr[p] > max) 
    {
      max = arr[p];
      speconly(witness = p;)
    }
  }
  return max;
}
\end{verbatim}
*}

boogie_open (quiet) "VCC_Max.b2i"

declare [[smt_certificates = "VCC_Max.certs"]]
declare [[smt_read_only_certificates = true]]
declare [[smt_oracle = false]]

boogie_status

boogie_vc maximum
  by boogie

boogie_end

end
