From Examples Require Import examples_header.

From Stdlib Require Import Fin.

Unset Elimination Schemes.
Print Fin.t.
Print pilotInversion.
Derive Dependent InvProxy for t. (*with pattern
   (pilotInversion 0 [noInversion;
                      pilotInversion 0 [noInversion;
                                        pilotInversion 0 [noInversion;
                                                          pilotInversion 0 [noInversion; noInversion]]]]).*)



Definition Fin_3_rect
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
  create_sdinv_call x.
  
  sdinv x as [|x].

  exact p1.
  sdinv x as [|x].
  exact p2.
  sdinv x as [|x].
  exact p3.
  sdinv x.
  Show Proof.
  Qed.

Inductive list_position {A} : list A -> Type :=
| HeadPosition x l : list_position (x :: l)
| TailPosition x l (p:list_position l) : list_position (x :: l).

Derive InvProxy for list_position with pattern (pilotInversion 1 [noInversion; noInversion]).


Lemma TailPosition_mono {A:Type} {l:list A} {x} {p1 p2 : list_position l} :
  TailPosition x _ p1 = TailPosition x _ p2 -> p1 = p2.
Proof using Type.
  intro h.
  create_sinv_call ( TailPosition x l p1).
  apply (@f_equal _ _ invproxy) in h.
  simpl in h; congruence.
Qed.

Inductive le2 : nat -> nat -> Prop :=
| L0 : forall m, le2 0 m
| LS : forall n m, le2 n m -> le2 (S n) (S m).

Derive InvProxy for le2 with prefix "_".
Derive InvProxy for le2 with pattern (pilotInversion 1 [noInversion; pilotInversion 1 [noInversion; noInversion]]).

Lemma le2_n_1_small n : le2 n 1 -> n = 0 \/ n = 1.
Proof.
  intro l.
  create_sinv_call l.
  sinv l.
  left; reflexivity.
  right; inv H; reflexivity.
  
Qed.



Inductive ge3 : nat -> Prop :=
| G10 : ge3 3
| GS n : ge3 n -> ge3 (S n).



Inductive Pilot : Type :=
|p1  : Pilot
|pn  {A} (l:list A) : Pilot.

Inductive Relation : Pilot -> Prop :=
|Rel (l : list nat) : l = l -> Relation (pn l).

Derive InvProxy for Relation.

Derive InvProxy for Relation with pattern (pilotInversion 0 [noInversion; pilotInversion 1 [noInversion; pilotInversion 1 [noInversion; noInversion]]]) with prefix "_".



Lemma totot n l :  Rel (S n :: l) eq_refl = Rel (S n :: l) eq_refl -> l = l.
Proof.
  intros r_eq.
  create_sinv_call_eq r_eq.
  apply (@f_equal _ _ invproxy) in  r_eq.
  simpl in r_eq.
  congruence.
  Qed.
