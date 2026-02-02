(*Functions that use TemplateMonad to define or quote Rocq objects*)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.

From utils Require Import TM_notations.
From utils Require Import error_monad.
From utils Require Import term_functions.


(*Functions that wrap the TemplateMonad definitions with a preceding tmEval.
Created to be used with the previous list functions*)

Definition define_const (name:string) (t:term) : TemplateMonad unit :=
  eval <-- tmEval all t;;
  tmMkDefinition name eval.


Definition define_mib (mib : mutual_inductive_body) : TemplateMonad unit :=
  eval <-- tmEval all mib;;
  tmMkInductive true (mind_body_to_entry eval).

Definition eval_print{X}(A:X) : TemplateMonad unit :=
  eval <-- tmEval all A;;
  tmPrint eval.

Fixpoint tmMap{A B} (f :  A -> TemplateMonad B) (l : list A) : TemplateMonad (list B) :=
  match l with
  |[] => tmReturn []
  |hd::tl =>
     nhd <-- f hd;;
     ntl <-- tmMap f tl;;
     tmReturn (nhd::ntl)
  end.
