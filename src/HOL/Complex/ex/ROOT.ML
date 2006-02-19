(*  Title:      HOL/Complex/ex/ROOT.ML
    ID:         $Id$

Miscellaneous examples involving the Reals, Hyperreals, etc.
*)

use_thy "BinEx";
no_document (with_path "../../NumberTheory" use_thy) "Factorization";
(*These two examples just need the theory Primes.*)
use_thy "Sqrt";
use_thy "Sqrt_Script";
(*This example also needs the theory Factorization.*)
use_thy "NSPrimes";

no_document use_thy "BigO";
use_thy "BigO_Complex";

no_document use_thy "ASeries";
use_thy "ASeries_Complex";
use_thy "HarmonicSeries";

no_document use_thy "NatPair";
use_thy "DenumRat";
