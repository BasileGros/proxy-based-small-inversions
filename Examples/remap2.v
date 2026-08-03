(* Handcrafted proxy-based small inversions for vectors,
   used in map2 and remap2, a simple example of dependent inversion
   The same example using automated PBSI is given in map2_around.v
 *)
From Stdlib Require Import Utf8.
From SmallInversion Require Import small_inversion.

Inductive vect (X : Type) : nat → Type :=
| nil : vect X O
| cons n : X → vect X n → vect X (S n).
Arguments nil {X}.
Arguments cons {X n}.

Notation "[ ]" := nil (format "[ ]").
Notation "x :: v" := (cons x v).
Notation "[ x ]" := (cons x nil).
Notation "[ x ; y ; .. ; z ]" :=  (cons x (cons y .. (cons z nil) ..)).

Unset Elimination Schemes (* For comfort *).
Derive InvProxy for vect.
Derive Dependent InvProxy for vect.
Set Elimination Schemes (* For comfort *).

(* Using the explicit instance is sometimes useful *)
Definition sdinv_vect {A n} (v : vect A n) := (vect_dproxy _ _).(dinvproxy) v.

(* Destructuring let for dependent proxies of vectors *)
Notation "'let_nil' '()' := E 'in' F" :=  (let 'nil_O_dep _ := E in F)  (at level 200).
Notation "'let_cons' ( A ,  B ) := E 'in' F" :=
  (let 'cons_S_dep _ _ A B := E in F)  (at level 200, A binder, B binder).

(* ====================================================================== *)
(* Basic map2 function *)

Fixpoint map2 {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []     => λ v, []
  | x :: u => λ v, let '(cons_S _ _ y v) := invproxy v in f x y :: map2 f u v
  end.

(*For non-dependent inversion, the notation "let (y,v) := ... v in" is also possible*)

Fixpoint map2' {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  vect B n → vect C n :=
  match u with
  | []     => λ v, []
  | x :: u => λ v, let (y,v) := invproxy v : vect_S _ _ in f x y :: map2' f u v
  end.

(* A map2 function on vectors that remembers its inputs in its type *)
Inductive Remap2 {C A B : Type} : ∀ {n}, vect A n → vect B n → Type :=
| Rmnil : Remap2 [] []
| Rmcons {a b n} {aa : vect A n} {bb : vect B n} :
  C → Remap2 aa bb → Remap2 (a :: aa) (b :: bb).
Arguments Remap2 C {A B n} _ _.

Fixpoint remap2 {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []     => λ v, let 'nil_O_dep _        := sdinv_vect v in Rmnil
  | x :: u => λ v, let 'cons_S_dep _ _ y v := sdinv_vect v in Rmcons (f x y) (remap2 f u v)
  end.

(* With nicer notations *)
Fixpoint remap2' {A B C : Type} (f : A → B → C) {n} (u : vect A n) :
  ∀ v : vect B n, Remap2 C u v :=
  match u with
  | []     => λ v, let_nil  ()     := sdinv_vect v in Rmnil
  | x :: u => λ v, let_cons (y, v) := sdinv_vect v in Rmcons (f x y) (remap2' f u v)
  end.
