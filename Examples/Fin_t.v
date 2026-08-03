
From Stdlib Require Import Fin.

(* Handcrafted proxy-based dependent small inversion *)
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

(* *)

(* Use case *)
Definition Fin_3_rect_smallinv
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x :=
  match Fin_proxy 3 x with
  | is_F1 _ => p1
  | is_FS _ x' =>
     match Fin_proxy 2 x' with
     | is_F1 _ => p2
     | is_FS _ x'' =>
        match Fin_proxy 1 x'' with
        | is_F1 _ => p3
        | is_FS _ x''' =>
           match Fin_proxy 0 x''' with end
        end
     end
  end.

(* Automated small inversion *)
From SmallInversion Require Import small_inversion.

(* For λ notation *)
From Stdlib Require Import Utf8.

Derive Dependent InvProxy for Fin.t.

(* Interactive definition *)
Definition Fin_3_rect_autoscript
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x.
Proof.
 sdinv x as [ | x2]. { exact p1. }
 sdinv x2 as [ | x1]. { exact p2. }
 sdinv x1 as [ | x0]. {  exact p3. }
 sdinv x0.
Defined.
Print Fin_3_rect_autoscript.

Fail Definition Fin_3_rect_autosmall
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x :=
  let d := dinvproxy x in
  match d in (t_S_dep _ t) return (P t) with
  | F1_S_dep _ => p1
  | FS_S_dep _ t0 =>
      (λ x2 : t 2,
         let d0 := dinvproxy x2 in
         match d0 in (t_S_dep _ t) return (P (FS t)) with
         | F1_S_dep _ => p2
         | FS_S_dep _ t1 =>
             (λ x1 : t 1,
                let d1 := dinvproxy x1 in
                match d1 in (t_S_dep _ t) return (P (FS (FS t))) with
                | F1_S_dep _ => p3
                | FS_S_dep _ t2 =>
                    (λ x0 : t 0, let d2 := dinvproxy x0 in match d2 return (P (FS (FS (FS x0)))) with
                                                           end) t2
                end)
               t1
         end)
        t0
  end.

(* After obvious simplication, renaming and repair of a slight oversight *)
Definition Fin_3_rect_autosmall
  (P : Fin.t 3 -> Type)
  (p1 : P F1)
  (p2 :  P (FS F1))
  (p3 : P (FS (FS F1))) 
  (x : Fin.t 3) : P x :=
  match dinvproxy x in t_S_dep _ t return (P t) with
  | F1_S_dep _ => p1
  | FS_S_dep _ x2 =>
      match dinvproxy x2 in t_S_dep _ t return (P (FS t)) with
      | F1_S_dep _ => p2
      | FS_S_dep _ x1 => 
          match dinvproxy x1 in t_S_dep _ t return (P (FS (FS t))) with
          | F1_S_dep _ => p3
          | FS_S_dep _ x0 => match dinvproxy x0 in t_O_dep _ with end
          end
      end
  end.

(* ====================================================================== *)
(* Other approaches *)

(* The tactic inversion fails *)
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

(* Equations works... *)
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

(* But the result is not suppoed to be readable *)
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
(* Same result *)
Print Fin_3_rect_equations.


(* The third method is dependent destruction, which is a refinement
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

