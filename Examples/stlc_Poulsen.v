(** This file is an adaptation in Rocq of some of the material presented in
    "Intrinsically-Typed Definitional Interpreters for Imperative Languages"
    by Poulsen et al., POPL 2018 *)


From Stdlib Require Import Utf8.
From SmallInversion Require Import small_inversion.
(* From Stdlib Require Import ZArith.*)  (* optional *) 
From Stdlib Require Import Fin.



Module ExpLang.
  (* A small intrinsically-typed interpreter for an expression
  language with arithmetic, conditionals, and variables, presented in
  Section 1 *)

  Inductive Ty : Set :=
  | Bool : Ty
  | Int : Ty.

  Definition Ctx := list Ty.


  Inductive in_list {A} (x:A) : list A -> Type :=
  | here {l} : in_list x (cons x l)
  | there {y l} : in_list x l -> in_list x (cons y l).

  Notation "t '∈' Γ" := (in_list t Γ) (at level 0).

  Unset Elimination Schemes.
  Derive InvProxy for in_list.
  Arguments in_list_proxy {_ _ _} _.
  Set Elimination Schemes.

  Inductive Expr (Γ : Ctx) : Ty -> Type :=
  | boolexpr : bool -> Expr Γ Bool
  | num : Z -> Expr Γ Int
  | var {t} : t ∈ Γ -> Expr Γ t
  | ifexpr {t} : Expr Γ Bool -> Expr Γ t -> Expr Γ t -> Expr Γ t
  | plus : Expr Γ Int -> Expr Γ Int -> Expr Γ Int.

  Inductive Val : Ty -> Set :=
  | boolval : bool -> Val Bool
  | numval : Z -> Val Int.

  Inductive All{A} (P : A -> Set) : list A -> Type :=
  | allnil : All P []
  | allcons : forall x xs,  P x -> All P xs -> All P (x :: xs).

  Definition Env (Γ : Ctx) := All Val Γ.

  Fixpoint lookup {A P xs} {x:A} (HA : All P xs) : x ∈ xs → P x :=
    match HA with
    | allnil _            => λ Hin', match in_list_proxy Hin' with end
    | allcons _ hd tl p a => λ Hin',
        match in_list_proxy Hin' with
        | here_cons _ _ _      => λ p' _, p'
        | there_cons _ _ _ y i => λ _  a', lookup a' i
        end p a
    end.

  Unset Elimination Schemes.
  Derive InvProxy for Val.
  Arguments Val_proxy {_} _.
  Set Elimination Schemes.

  Fixpoint eval {Γ t} (exp : Expr Γ t) (E : Env Γ) : Val t :=
    match exp with
    | boolexpr _ b => boolval b
    | num _ x => numval x
    | var _ x => lookup E x
    | ifexpr _ c t' e =>
        let b := eval c E in
        match Val_proxy b with
        | boolval_Bool b' => if b' then eval t' E else eval t' E
        end
    | plus _ e1 e2 =>
        let z1 :=  eval e1 E in
        let z2 :=  eval e2 E in
        match Val_proxy z1, Val_proxy z2 with
        | numval_Int z1', numval_Int z2' => numval (z1' + z2')
        end
    end.

  Eval compute in (eval (plus _ (var _ (here Int)) (num _ 2))
                        (allcons Val Int [] (numval 3) (allnil _) ) ).

End ExpLang.

Module STLC.
  (*This is a Rocq translation of section 2, A definitional interpreter for STLC. *)

  Inductive Ty :=
  | unit : Ty
  | implies : Ty -> Ty -> Ty
  | int : Ty.

  Notation "t '==>' u" := (implies t u)(at level 0).

  Definition Ctx := list Ty.


  Inductive in_list{A}(x:A) : list A -> Type :=
  | here {l} : in_list x (cons x l)
  | there {y l} : in_list x l -> in_list x (cons y l).


  Notation "t '∈' Γ" := (in_list t Γ) (at level 0).

  Unset Elimination Schemes.
  Derive InvProxy for in_list.
  Arguments in_list_proxy {_ _ _} _.
  Set Elimination Schemes.

  Inductive Expr (Γ : Ctx) : Ty -> Type :=
  | unitexpr : Expr Γ unit
  | var {t} : t ∈ Γ -> Expr Γ t
  | lam {t u} : Expr (cons t Γ) u -> Expr Γ (t ==> u)
  | app {t u} : Expr Γ (t ==> u) -> Expr Γ t -> Expr Γ u
  | num : Z -> Expr Γ int
  | iop : (Z -> Z -> Z) -> Expr Γ int -> Expr Γ int -> Expr Γ int.

  Inductive All{A} (P : A -> Type) : list A -> Type :=
  | allnil : All P nil
  | allcons : forall x xs,  P x -> All P xs -> All P (cons x xs).


  Inductive Val : Ty -> Type :=
  | unitval : Val unit
  | numval : Z -> Val int
  | closure {Γ t u} :
    Expr (t :: Γ) u -> All Val Γ -> Val (t ==> u).

  Notation "'Env' Γ" := (All Val Γ)(at level 0).

  Unset Elimination Schemes.
  Derive InvProxy for Val.
  Arguments Val_proxy {_} _.
  Set Elimination Schemes.
  
  Fixpoint lookup {A P xs} {x:A} (HA : All P xs) : x ∈ xs → P x :=
    match HA with
    | allnil _            => λ Hin', match in_list_proxy Hin' with end
    | allcons _ hd tl p a => λ Hin',
        match in_list_proxy Hin' with
        | here_cons _ _ _      => λ p' _, p'
        | there_cons _ _ _ y i => λ _  a', lookup a' i
        end p a
    end.
  
  Definition M (Γ : Ctx) (A:Type) : Type :=
    (Env Γ -> option A).

  Definition bind {Γ A B} (f: M Γ A)(c : A -> M Γ B) : M Γ B :=
    λ E, match f E with
         | Some x => c x E
         | None => None
         end.

  Notation "mA '>>=' f" := (bind mA f)(at level 0, right associativity).

  Definition ret {Γ A} (x : A) : M Γ A := λ _, Some x.

  Definition getEnv {Γ} :  M Γ (Env Γ) := λ E, ret E E.

  Definition usingEnv {Γ Γ' A} (E : Env Γ) (f : M Γ A) : M Γ' A :=
    fun _ => f E.

  Definition timeout {Γ A} : M Γ A := λ _, None.

  Fixpoint eval (n:nat){Γ t} (exp : Expr Γ t) : M Γ (Val t) :=
    match n, exp with
    | O, _ => timeout
    | S k, unitexpr _ => ret unitval
    | S k, var _ x => getEnv >>= fun E => ret (lookup E x)
    | S k, lam _ e => getEnv >>= fun E => ret (closure e E)
    | S k, app _ l r =>
       getEnv >>= λ E', (eval k l) >>=
                          λ v', match Val_proxy v' with
                                | closure_implies _ _ _ e E =>
                                    λ _ r0 _, getEnv >>=
                                             λ _ , (eval k r0) >>=
                                                     λ v'', usingEnv (allcons Val _ _ v'' E) (eval k e)
                                   
                                end l r v'
    | S k , num _ x => ret (numval x)
    | S k, iop _ f l r =>
       getEnv >>= λ E', (eval k l) >>=
                          λ v, match Val_proxy v with
                               | numval_int vl => getEnv >>=
                                                    λ E', (eval k r) >>=
                                                            λ v', match Val_proxy v' with
                                                                  | numval_int vr => ret (numval (f vl vr))
                                                                  end
                               end
    end.

  Definition idexpr : Expr nil (unit ==> unit) := (lam _ ( var _ (here unit))).


  Lemma test_idexpr : eval 2 (app nil (idexpr) (unitexpr nil)) (allnil Val)  = Some unitval.
    reflexivity.
  Qed.


  Definition curry_plus : Expr nil (int ==> (int ==> int)) :=
    lam _ (lam _ (iop _ Z.add (var _ (here _)) (var _ (there _ (here _))))).

  Lemma text_curry_plus : eval 3 (app _ (app _ curry_plus (num _ 1)) (num _ 1))
                                 (allnil Val) = Some (numval 2).
    reflexivity.
  Qed.

End STLC.
