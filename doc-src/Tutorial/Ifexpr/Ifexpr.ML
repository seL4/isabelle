use "bool2if.ML";
use "proof.ML";
qed "bool2if_correct";

use "normif.ML";
use "proof.ML";
qed_spec_mp "normif_correct";
Addsimps [normif_correct];

use "norm.ML";
use "proof.ML";
qed "norm_correct";

use "normal_normif.ML";
use "proof.ML";
qed_spec_mp "normal_normif";
Addsimps [normal_normif];

use "normal_norm.ML";
use "proof.ML";
qed "normal_norm";
