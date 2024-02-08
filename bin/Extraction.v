From vvequiv Require VVEquiv.
From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.


Extraction Language OCaml.
Extraction "VVEquiv.ml" VVEquiv.program_name.
