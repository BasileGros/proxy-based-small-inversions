From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.
From SmallInversion Require Import strategy_engine.


Definition print_glob_def
  (Σ : global_env)
  (g : Glob_def)
  : TemplateMonad unit :=
  match g with
  | DefInductive msg info mib => tmMsg ( msg ^ "
" ^ pTransfo_info Σ [] info ^ "
" ^ pMib Σ [] mib)
  | DefConst nam ast => tmMsg (nam ^ " : " ^ pTerm Σ [] ast)
  end.

Definition ugly_print_glob_def
  (Σ : global_env)
  (g : Glob_def)
  : TemplateMonad unit :=
  match g with
  | DefInductive msg info mib =>
      _ <-- eval_print msg;;
      _ <-- eval_print info;;
      eval_print mib
  | DefConst nam ast =>
      _ <-- eval_print nam;;
      eval_print ast
  end.

Fixpoint print_list_glob_def
  (Σ : global_env)(l : list Glob_def)
  : TemplateMonad unit :=
  match l with
  | [] => tmReturn tt
  | hd :: tl =>
      _ <-- print_glob_def Σ hd;;
      _ <-- tmMsg("

");;
      print_list_glob_def Σ tl
  end.

Fixpoint ugly_print_list_glob_def
  (Σ : global_env)(l : list Glob_def)
  : TemplateMonad unit :=
  match l with
  | [] => tmReturn tt
  | hd :: tl =>
      _ <-- ugly_print_glob_def Σ hd;;
      ugly_print_list_glob_def Σ tl
  end.


