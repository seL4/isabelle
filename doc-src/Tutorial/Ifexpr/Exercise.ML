use "normif.ML";
use "proof.ML";
qed_spec_mp "normif_correct";
Addsimps [normif_correct];

use "norm.ML";
use "proof.ML";
qed "norm_correct";

Goal "!t e. normal t & normal e --> normal(normif b t e)";
use "proof.ML";
qed_spec_mp "normal_normif";
Addsimps [normal_normif];

use "normal_norm.ML";
use "proof.ML";
qed "normal_norm";
