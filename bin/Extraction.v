From vvequiv Require VVEquiv.
From Coq Require Extraction.
From Coq Require Import extraction.ExtrOcamlBasic.
From Coq Require Import extraction.ExtrOcamlString.
From Coq Require Import extraction.ExtrOcamlZInt.

Extraction Language OCaml.

Extract Constant VVEquiv.add1 => "Helpers.add1".
Extraction "VVEquiv.ml" VVEquiv.program_name VVEquiv.a_num.
