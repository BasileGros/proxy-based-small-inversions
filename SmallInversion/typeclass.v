(** * Type Classes for proxy-based inversions *)


Class InvProxy  (T:Type) := {  invproxy_type:     Type;  invproxy:     T -> invproxy_type }.
Class dInvProxy (T:Type) := { dinvproxy_type: T -> Type; dinvproxy: forall t:T, dinvproxy_type t }.


(** ** Algebraic variant *)

#[global] Tactic Notation "sinv" constr(p) :=
  (destruct (invproxy p)).
#[global] Tactic Notation "sinv" constr(p) "as" simple_intropattern(pat) :=
  ( destruct (invproxy p) as pat).
#[global] Tactic Notation "sdinv" constr(p) :=
  (destruct (dinvproxy p)).
#[global] Tactic Notation "sdinv" constr(p) "as" simple_intropattern(pat) :=
  (destruct (dinvproxy p) as pat).
