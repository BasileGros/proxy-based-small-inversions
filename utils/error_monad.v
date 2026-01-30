From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MRMonadNotation.
From utils Require Import TM_notations.

(*A monad that allows to transmit and add to an error trace*)
Inductive ErrorMonad (A : Type) : Type :=
| Success : A -> ErrorMonad A
| Error : string -> ErrorMonad A.

Arguments Success {A}.
Arguments Error {A}.


(** Links to the MetaRocq TemplateMonad.*)
(*The bind functions, with or without adding a new message to the trace*)
Definition ErrorBind
  {A B : Type} (Err : ErrorMonad A) (f : A -> ErrorMonad B)
  : ErrorMonad B :=
  match Err with
  |Error message => Error message
  |Success a => f a
  end.

Definition ErrorMessageBind
  {A B : Type} (Err : ErrorMonad A) (add : string) (f : A -> ErrorMonad B)
  : ErrorMonad B :=
  match Err with
  |Error message => Error (add ^ message)
  |Success a => f a
  end.

(*Converts to MetaCoq's TemplateMonad*)
Definition tmErrorReturn {A : Type} (Err : ErrorMonad A) : TemplateMonad A :=
  nErr <-- tmEval all Err;;
  match nErr with
  |Error message => tmFail message
  |Success a => eval <-- tmEval all a;; tmReturn a
  end.

(*Converts to printing in MetaCoq's TemplateMonad*)
Definition tmErrorPrint {A : Type} (Err : ErrorMonad A) : TemplateMonad unit :=
  match Err with
  |Error message => tmFail message
  |Success a => b <- tmEval all a;;
               tmPrint b
  end.

Definition error_to_option{A : Type}
  (Err : ErrorMonad A) : option A :=
  match Err with
  |Error _ => None
  |Success a => Some a
  end.

(*Notations for infix bind operators.*)

Declare Scope error_scope.

Notation "x <-? c1 ;; c2" :=
  (@ErrorBind _ _ c1 (fun x => c2))
    (at level 100, c1 at next level,
      right associativity) : error_scope.

Notation "x <-? c1 'except' message ;; c2" :=
  (@ErrorMessageBind _ _ c1 message (fun x => c2))
    (at level 100, c1 at next level,
      right associativity) : error_scope.

Notation "' pat <-? c1 ;; c2" :=
  (@ErrorBind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level,
      right associativity) : error_scope.


Notation "' pat <-? c1 'except' message ;; c2" :=
  (@ErrorMessageBind _ _ c1 message (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level,
      right associativity) : error_scope.


Open Scope error_scope.

