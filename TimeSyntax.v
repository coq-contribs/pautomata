Require Import Time.

Infix "+/" := Tplus (left associativity, at level 50).
Infix "-/" := Tminus (left associativity, at level 50).
Infix "*/" := Tmult (left associativity, at level 40).
Infix "</" := Tlt (no associativity, at level 70).
Infix "<=/" := Tle (no associativity, at level 70).
Infix ">/" := Tgt (no associativity, at level 70).
Infix ">=/" := Tge (no associativity, at level 70).