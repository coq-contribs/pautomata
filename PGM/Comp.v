(*****************************************************)
(*                       COMP.v                      *)
(*                     Yijia CHEN                    *)
(*                                                   *)
(*****************************************************)

Require Import Bool.

Section COMPARE_DEF.

Fixpoint less (n1 : nat) : nat -> bool :=
  match n1 with
  | O => fun n2 : nat => match n2 with
                         | O => false
                         | S n2' => true
                         end
  | S n1' =>
      fun n2 : nat => match n2 with
                      | O => false
                      | S n2' => less n1' n2'
                      end
  end.

End COMPARE_DEF.