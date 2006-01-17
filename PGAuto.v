(** Generalised automata associated to a p-automata *)

Require Export PAutomataMod.
Require Export GAutomata.
Require Export TimeSyntax.

Module Gauto_of (P: Pauto_struct) <: Gauto_struct.
Definition Loc := P.Loc.
Definition Act := P.Act.

Record gVar : Type := {time_of : Time; val_of : P.Var}.
Definition Var:=gVar.

Definition Evo : G_Evolution Var Loc := 
   fun l v w => time_of v </ time_of w 
   /\ val_of v = val_of w
   /\ forall T : Time, time_of v </ T -> T <=/ time_of w -> P.Inv l T (val_of v).
  
Definition Trans : G_Transitions Var Loc Act := 
   fun a l v l' w => time_of v = time_of w 
   /\ P.Trans a (time_of v) l (val_of v) l' (val_of w).

End Gauto_of.
