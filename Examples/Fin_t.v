
From Stdlib Require Import Fin.
From Examples Require Import examples_header.

Inductive Fin_O : Fin.t 0 -> Set :=.
Inductive Fin_S (n : nat) : Fin.t (S n) -> Set :=
| is_F1 : Fin_S n F1
| is_FS  (r:Fin.t n) : Fin_S n (FS r).

Definition Fin_proxy_type (n:nat) : Fin.t n -> Set :=
  match n with
  | 0 => Fin_O
  | S m => Fin_S m
  end.

Definition Fin_proxy(n:nat) (r : Fin.t n) : Fin_proxy_type n r :=
  match r as r' in Fin.t n' return Fin_proxy_type n' r' with
  | @F1 n => is_F1 n
  | @FS n t' => is_FS n t'
  end.



Definition Fin_3_rect_smallinv
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x :=
  match Fin_proxy 3 x with
  |is_F1 _ => p1
  |is_FS _ x' =>
     match Fin_proxy 2 x' with
     |is_F1 _ => p2
     |is_FS _ x'' =>
        match Fin_proxy 1 x'' with
        |is_F1 _ => p3
        |is_FS _ x''' =>
           match Fin_proxy 0 x''' with end
        end
     end
  end.


Derive Dependent InvProxy for Fin.t.

Definition Fin_3_rect_autosmall
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
 sdinv x.
 exact p1.
 sdinv t.
 exact p2.
 sdinv t.
 exact p3.
 sdinv t.
Defined.
Print Fin_3_rect_autosmall.




Definition Fin_3_rect_inv
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
  inversion x as [n' eq| n' i' eq].
  Fail exact p1.
Abort.


Definition Fin_3_rect_dinv
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
  Fail dependent inversion x.
Abort.


From Equations Require Import Equations.
Definition Fin_3_rect_depelim
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
  dependent elimination x
    as [F1|FS F1|FS (FS F1)].
  - exact p1.
  - exact p2.
  - exact p3.
Defined.
Print Fin_3_rect_depelim.

Equations Fin_3_rect_equations
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x :=
  Fin_3_rect_equations P p1 p2 p3 F1 := p1;
  Fin_3_rect_equations P p1 p2 p3 (FS F1) := p2;
  Fin_3_rect_equations P p1 p2 p3 (FS (FS F1)) := p3.
Print Fin_3_rect_equations.


(*The third method is dependent destruction, which is a refinment
  of the BasicElim tactic.*)
Require Import Stdlib.Program.Equality.
Definition Fin_3_rect_destr
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
  dependent destruction x.
  - exact p1.
  - dependent destruction x.
    -- exact p2.
    -- dependent destruction x.
       --- exact p3.
       --- dependent destruction x.
Defined.
Print Fin_3_rect_destr.


Compute (Fin_3_rect_destr (fun _ => Fin.t 3) (FS (FS F1)) F1 (FS F1) F1).
Compute (Fin_3_rect_depelim (fun _ => Fin.t 3) (FS (FS F1)) F1 (FS F1) F1).
Compute (Fin_3_rect_smallinv (fun _ => Fin.t 3) (FS (FS F1)) F1 (FS F1) F1).
Compute (Fin_3_rect_autosmall (fun _ => Fin.t 3) (FS (FS F1)) F1 (FS F1) F1).

