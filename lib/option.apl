namespace Option (

opt : type -> type.

none : opt A.
some : A -> opt A.

pred get_opt (opt A) A.
get_opt (some A) A.

).