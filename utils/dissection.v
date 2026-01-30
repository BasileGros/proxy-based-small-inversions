From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import error_monad.
From utils Require Import TM_notations.
From utils Require Import term_functions.
From utils Require Import term_printer.

(*Prints the MetaCoq term of a Coq constant.*)
Definition dissect_constante {X}(constant:X) : TemplateMonad unit :=
  '(env,term_const) <-- tmQuoteRec constant;;
  match term_const with
  | tConst a _ =>
      let term := lookup_constant env a in
      match term with
      |None => tmFail "Constant not in the environment"
      |Some t =>
         match t.(cst_body) with
         |None => tmFail "the constant does not have a body"
         |Some cst =>
         eval <-- tmEval all cst;;
         tmPrint eval
         end
      end
  |_ => tmFail "The Coq object given is not a constant."
  end.

Definition pretty_dissect_constante {X}(constant:X) : TemplateMonad unit :=
  '(env,term_const) <-- tmQuoteRec constant;;
  match term_const with
  | tConst a _ =>
      let term := lookup_constant env a in
      match term with
      |None => tmFail "Constant not in the environment"
      |Some t =>
         match t.(cst_body) with
         |None => tmFail "the constant does not have a body"
         |Some cst =>
         eval <-- tmEval all (pTerm env [] cst);;
         tmMsg eval
         end
      end
  |_ => tmFail "The Coq object given is not a constant."
  end.



(*Prints the mutual_inductive_body of a given inductive Coq object.*)
Definition dissect_mib {X} (inductive_object:X) : TemplateMonad unit :=
  '(env,term_ind) <-- tmQuoteRec inductive_object;;
  match term_ind with
  |tInd ind _ =>
     match lookup_mind_decl (inductive_mind ind) env.(declarations) with
     |None => tmFail "Inductive not in env"
     |Some mib => tmPrint mib
     end
  |_ => tmFail "Not an inductive"
end.

(*Prints the mutual_inductive_body of a given inductive Coq object.*)
Definition pretty_dissect_mib {X} (inductive_object:X) : TemplateMonad unit :=
  '(env,term_ind) <-- tmQuoteRec inductive_object;;
  match term_ind with
  |tInd ind _ =>
     match lookup_mind_decl (inductive_mind ind) env.(declarations) with
     |None => tmFail "Inductive not in env"
     |Some mib =>
        eval <-- tmEval all (pMib env [] mib);;
         tmMsg eval
     end
  |_ => tmFail "Not an inductive"
end.


(*Prints the one_inductive_body of a given inductive Coq object.*)
Definition dissect_oib {X} (inductive_object:X) : TemplateMonad unit :=
  '(env,term_ind) <-- tmQuoteRec inductive_object;;
  match term_ind with
  |tInd ind _ =>
     match lookup_mind_decl (inductive_mind ind) env.(declarations) with
     |None => tmFail "Inductive not in env"
     |Some mib =>
        
        match one_inductive_body_from_mib mib (inductive_ind ind) with
        |Error message => tmFail message
        |Success oib => tmPrint oib
        end
     end
  |_ => tmFail "Not an inductive"
  end.
