(****************************************************************************)
(* 	           Emmanuel Freund & Christine Paulin-Mohring               *)
(*                               July 1st 2000                              *)
(****************************************************************************)
(*i $Id$ i*)

Set Implicit Arguments.
Unset Strict Implicit.

(*s Modelisation of a labelled transition system *)

Definition LTS_Transitions (S : Type) (A : Set) := S -> A -> S -> Prop.

Record LTS : Type := 
  {LTS_State : Type;
   LTS_Act : Set;
   LTS_Trans : LTS_Transitions LTS_State LTS_Act}.

Section LTS_PROP.

Variable L : LTS.
Let state := LTS_State L.
Let action := LTS_Act L.
Let transition := LTS_Trans (l:=L).

(*s Some properties *)

Inductive access (e1 : state) : state -> Prop :=
  | there : access e1 e1
  | add_acces :
      forall (e2 e3 : state) (t : action),
      access e1 e2 -> transition e2 t e3 -> access e1 e3. 

Definition deadlock (e1 : state) : Prop :=
  forall (t : action) (e2 : state), ~ transition e1 t e2.

CoInductive vivacity : state -> Prop :=
    onemore :
      forall (t : action) (e1 e2 : state),
      vivacity e2 -> transition e1 t e2 -> vivacity e1.

Lemma Invariant :
 forall P : state -> Prop,
 (forall s s' : state, P s -> forall a : action, transition s a s' -> P s') ->
 forall s0 s : state, P s0 -> access s0 s -> P s.
simple induction 3; intros; auto.
apply H with e2 t; auto.
Qed.

End LTS_PROP.

(*s  Synchronisation of two LTS *)

Section LTS_SYNCHRONISATION.

Variable L1 L2 : LTS.

Let state1 := LTS_State L1.
Let state2 := LTS_State L2.
Let act1 := LTS_Act L1.
Let act2 := LTS_Act L2.
Let trans1 := LTS_Trans (l:=L1).
Let trans2 := LTS_Trans (l:=L2).

Definition act_synchro : Set := (act1 * act2)%type.

Definition state_synchro : Type := prodT state1 state2.

Variable ens_synchro : act_synchro -> Prop.

Inductive trans_synchro (s : state_synchro) (a : act_synchro)
(s' : state_synchro) : Prop :=
    trans_both :
      ens_synchro a ->
      trans1 (fstT s) (fst a) (fstT s') ->
      trans2 (sndT s) (snd a) (sndT s') -> trans_synchro s a s'.

Definition LTS_synchro := Build_LTS trans_synchro.

(*s Execute at the same time a synchronisation and a restriction of 
    the set of states 
*)

Variable P : state_synchro -> Prop.

Inductive trans_synchro_restr (s : state_synchro) (a : act_synchro)
(s' : state_synchro) : Prop :=
    trans_both_restr :
      ens_synchro a ->
      P s ->
      P s' ->
      trans1 (fstT s) (fst a) (fstT s') ->
      trans2 (sndT s) (snd a) (sndT s') -> trans_synchro_restr s a s'.

Definition LTS_synchro_restr := Build_LTS trans_synchro_restr.

       
End LTS_SYNCHRONISATION.


(*s Strong bisimulation : 2 definitions, proof of equivalence *)

Section LTS_BISIMULATION.
Variable L : LTS.

Let act := LTS_Act L.
Let state := LTS_State L.
Let transition := LTS_Trans (l:=L).
Let action := LTS_Act L.

(*s [R] is a bisimulation *)
Definition StBisimulation (R : state -> state -> Prop) : Prop :=
  forall p q : state,
  R p q ->
  (forall (a : action) (p' : state),
   transition p a p' -> exists2 q' : state, transition q a q' & R p' q') /\
  (forall (a : action) (q' : state),
   transition q a q' -> exists2 p' : state, transition p a p' & R p' q').

(*s When [R] is symmetric it is enough to check one direction *)

Lemma StBisimulation_sym_intro :
 forall R : state -> state -> Prop,
 (forall x y : state, R x y -> R y x) ->
 (forall p q : state,
  R p q ->
  forall (a : action) (p' : state),
  transition p a p' -> exists2 q' : state, transition q a q' & R p' q') ->
 StBisimulation R.
intros.
split; intros.
apply H0 with (1 := H1); trivial.
elim H0 with q p a q'; auto; intros p' H3 H4.
exists p'; auto.
Qed.


(*s Two states are equivalents when a bisimulation exists*)
Inductive StBEquiv (p q : state) : Prop :=
    exist :
      forall R : state -> state -> Prop,
      R p q -> StBisimulation R -> StBEquiv p q.

(*s Direct coinductive definition *)
CoInductive StateEquiv : state -> state -> Prop :=
    StateEquiv_intro :
      forall p q : state,
      (forall (a : action) (p' : state),
       transition p a p' ->
       exists2 q' : state, transition q a q' & StateEquiv p' q') ->
      (forall (a : action) (q' : state),
       transition q a q' ->
       exists2 p' : state, transition p a p' & StateEquiv p' q') ->
      StateEquiv p q.

(* Properties of [StateEquiv] *)
Lemma StateEquiv_refl : forall p : state, StateEquiv p p.
cofix.
intro; constructor; intros.
exists p'; auto.
exists q'; auto.
Qed.

Lemma StateEquiv_sym : forall p q : state, StateEquiv p q -> StateEquiv q p.
cofix.
simple destruct 1; intros; constructor; intros.
case H1 with a p'; intros; trivial.
exists x; auto.
case H0 with a q'; intros; trivial.
exists x; auto.
Qed.

Lemma StateEquiv_trans :
 forall p q r : state, StateEquiv p q -> StateEquiv q r -> StateEquiv p r.
cofix; intros p q r H1.
case H1; clear H1 p q; intros.
inversion_clear H1; intros.
constructor; intros.
case H with (1 := H1); intros.
case H2 with (1 := H4); intros.
exists x0; eauto.
case H3 with (1 := H1); intros.
case H0 with (1 := H4); intros.
exists x0; eauto.
Qed.

Lemma State_Equiv_bisim : StBisimulation StateEquiv.
constructor.
case H; auto.
case H; auto.
Qed.

(*s Equivalence of the two definitions *)

Lemma StateEquiv_StBEquiv :
 forall p q : state, StateEquiv p q -> StBEquiv p q.
exists StateEquiv; trivial.
exact State_Equiv_bisim.
Qed.

Lemma StBEquiv_StateEquiv :
 forall p q : state, StBEquiv p q -> StateEquiv p q.
simple destruct 1; intros R Rpq Bi; generalize p q Rpq.
cofix; intros.
case Bi with (1 := Rpq0); intros.
constructor; intros.
case H0 with (1 := H2); intros.
exists x; auto.
case H1 with (1 := H2); intros.
exists x; auto.
Qed.

(*s Direct proof of properties of [StBEquiv] *)

Lemma StEquiv_Refl : forall p : state, StBEquiv p p.
intro; exists (fun p q : state => p = q); trivial.
split; intros.
exists p'; trivial.
rewrite <- H; trivial.
exists q'; trivial.
rewrite H; trivial. 
Qed.

Lemma StEquiv_Sym : forall p q : state, StBEquiv p q -> StBEquiv q p.
intros.
case H; intros.
exists (fun p q : state => R q p); trivial.
red in |- *; intros.
case H1 with (1 := H2); auto.
Qed.

Lemma StEquiv_Trans :
 forall p q r : state, StBEquiv p q -> StBEquiv q r -> StBEquiv p r.
intros p q r H1 H2; case H1; case H2; clear H1 H2; intros.
exists (fun p r : state => exists2 q : state, R0 p q & R q r).
exists q; auto.
red in |- *; intros.
case H3; clear H3; intros.
case H2 with (1 := H3); clear H2; intros.
case H0 with (1 := H4); clear H0; intros.
split; intros.
case H2 with (1 := H7); clear H2; intros.
case H0 with (1 := H2); clear H0; intros.
exists x1; trivial; exists x0; trivial.
case H6 with (1 := H7); clear H6; intros.
case H5 with (1 := H6); clear H5; intros.
exists x1; trivial; exists x0; trivial.
Qed.

End LTS_BISIMULATION.


