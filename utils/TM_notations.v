From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.

(*Notations to use the monad*)
Declare Scope template_scope.

Notation "x <-- c1 ;; c2" :=
  (@tmBind _ _ c1 (fun x => c2))
    (at level 100, c1 at next level,
      right associativity) : template_scope.

Notation "' pat <-- c1 ;; c2" :=
  (@tmBind _ _ c1 (fun x => match x with pat => c2 end))
    (at level 100, pat pattern, c1 at next level,
      right associativity) : template_scope.

Notation "[< x1 , x2 >]" :=
  (@existT_typed_term x1 x2) : template_scope.

Open Scope template_scope.
