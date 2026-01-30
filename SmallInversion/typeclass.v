
(** * Type Classes for proxy-based inversions *)

(** ** Algebraic variant *)

Class Proxy  (T:Type) := {  proxy_type:     Type;  invproxy:     T -> proxy_type }.
Class dProxy (T:Type) := { dproxy_type: T -> Type; dinvproxy: forall t:T, dproxy_type t }.

(*
(** ** Applicative variant *)

Class aProxy  (T:Type) := {  aproxy_type:     Type;  aproxy:     T -> aproxy_type }.
Class adProxy (T:Type) := { adproxy_type: T -> Type; adproxy: forall t:T, adproxy_type t }.
*)
(** * Tactics for proxy-based inversions *)

(** ** Algebraic variant *)

#[global] Tactic Notation "sinv" constr(p) :=
  (destruct (invproxy p)).
#[global] Tactic Notation "sinv" constr(p) "as" simple_intropattern(pat) :=
  ( destruct (invproxy p) as pat).
#[global] Tactic Notation "sdinv" constr(p) :=
  (destruct (dinvproxy p)).
#[global] Tactic Notation "sdinv" constr(p) "as" simple_intropattern(pat) :=
  (destruct (dinvproxy p) as pat).
(*
(** ** Applicative variant *)

#[global] Tactic Notation "ainv" constr(p) :=
  let id:= fresh "_proxy" in
  (pose (id:=adproxy p) || pose (id:=aproxy p));apply id;clear id.
*)
