From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
Import MRMonadNotation.

From utils Require Import utils.

Notation ind_eq := {| inductive_mind := (MPfile ["Logic"; "Init"; "Corelib"], "eq"); inductive_ind := 0 |}.

Definition quotetype(X : Type) :=
  x <-- tmQuote X;;
  eval <-- tmEval all x;;
  tmReturn eval.

  
Definition extract_type_and_args (type : term) : TemplateMonad (inductive × list term) :=
  match type with
  | tApp (tInd ind_type _) largs => tmReturn (ind_type, largs)
  | tInd ind_type _ => tmReturn (ind_type, [])
  | _ => tmFail "Not an inductive type"
  end.

Definition extract_type_and_args_eq (type : term) : TemplateMonad (inductive × list term) :=
  match type with
  | tApp (tInd ind_eq _) (type_eq::_) => extract_type_and_args type_eq
  | _ => tmFail "Not an equality"
  end.


Fixpoint extract_first_interesting_index (nb_params_R : nat) (args : list term) (pos_index : nat)
  : ErrorMonad (((inductive × nat) × nat) × list term) :=
  match args, nb_params_R with
  |[],_ => Error "No interesting index found"
  |t::q, S n => extract_first_interesting_index n q (1 + pos_index)
  |t::q, 0 => match t with
            |tConstruct ind pos_cons _ => Success (ind, pos_index, pos_cons, [])
            |tApp (tConstruct ind pos_cons _) largs => Success (ind, pos_index, pos_cons, largs)
            | _ => extract_first_interesting_index 0 q (1 + pos_index)
            end
  end.

Record info_construct : Type :=
  Builn_info_construct
    {
      nb_params : nat;
      lctors : list constructor_body;
    }.

Definition extract_info_construct (ind : inductive) :=
  mib <-- tmQuoteInductive ind.(inductive_mind);;
  match one_inductive_body_from_mib mib (inductive_ind ind) with
  |Error message => tmFail message
  |Success oib =>
     tmReturn {|
         nb_params := mib.(ind_npars);
         lctors := oib.(ind_ctors)
       |}       
  end.

Unset Guard Checking.

Definition create_new_list_args(pos_initial_cons : nat)(pos_index : nat)(largs_cons : list term)(largs_R : list term)(nb_params_cons : nat)(pos_constr : nat)(cons_body : constructor_body) :=
  let new_list :=
    if pos_initial_cons =? pos_constr
    then without_firstn largs_cons nb_params_cons
    else list_const (tVar "") cons_body.(cstr_arity)
  in
  remove_index_replace_by_list largs_R pos_index new_list.
      

Unset Guard Checking.
Fixpoint create_index_tree (nb_params_R : nat)(largs : list term){struct nb_params_R}  :=
  match extract_first_interesting_index nb_params_R largs 0 with
  |Error m => tmReturn leaf
  |Success a =>
                        
     let '(ind_cons, pos_index, pos_cons, largs_cons) := a in
     infos_cons <-- extract_info_construct ind_cons;;
     let largs_for_cons :=
       mapi
         (create_new_list_args pos_cons pos_index largs_cons largs infos_cons.(nb_params))
         infos_cons.(lctors)
     in 
     sub_trees <-- tmMap (create_index_tree nb_params_R) largs_for_cons;;

     tmReturn (node pos_index sub_trees)
  end.
Set Guard Checking.  

Fixpoint list_string_cat (l : list string)(is_beginning : bool) :=
  match l, is_beginning with
  |[],_ => ""
  |t::q, true => t ^ (list_string_cat q false)
  |t::q, false => "; " ^ t ^ (list_string_cat q false)
  end.

Fixpoint indextree_to_string (t : tree nat) :=
  match t with
  |leaf => "noInversion"
  |node a l =>
     let list_tl := list_string_cat (map indextree_to_string l) true in
     "pilotInversion " ^ (string_of_nat a) ^ " [" ^ list_tl ^ "]"
  end.

Definition get_pattern{X}(R:X)(is_eq : bool)  :=
  type <-- quotetype X;;

  '(ind_type, largs) <--
    (if is_eq
     then
       extract_type_and_args_eq type
     else
       extract_type_and_args type);;
  mib <-- tmQuoteInductive ind_type.(inductive_mind);;
  let '(_,ind_name) := ind_type.(inductive_mind) in
  pattern_index_tree <-- create_index_tree mib.(ind_npars) largs;;
  let string_tree := indextree_to_string pattern_index_tree in
  let call := "Derive InvProxy for " ^ ind_name ^ " with pattern (" ^ string_tree ^ ")." in
  tmMsg call.

#[global] Tactic Notation "create_sinv_call" constr(x) := ltac:((let p := fun _ => idtac in
                             run_template_program (get_pattern x false) p)).

#[global] Tactic Notation "create_sinv_call_eq" constr(x) := ltac:((let p := fun _ => idtac in
                             run_template_program (get_pattern x true) p)).


Definition get_dependent_pattern{X}(R:X):=
  type <-- quotetype X;;
  '(ind_type, largs) <-- extract_type_and_args type;;
  mib <-- tmQuoteInductive ind_type.(inductive_mind);;
  let '(_,ind_name) := ind_type.(inductive_mind) in
  pattern_index_tree <-- create_index_tree mib.(ind_npars) largs;;
  let string_tree := indextree_to_string pattern_index_tree in
  let call := "Derive Dependent InvProxy for " ^ ind_name ^ " with pattern (" ^ string_tree ^ ")." in
  tmMsg call.

#[global] Tactic Notation "create_sdinv_call" constr(x) := ltac:((let p := fun _ => idtac in
                             run_template_program (get_dependent_pattern x) p)).
