(** * Removes recursive calls to an inductive and its mytual inductive types.
 Also removes any let in construct present in any type telescope.*)

From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.

(** Partial derecursivation : does not change the final call to the inductive in each constructor. *)

Definition derecursivation_constructor
  (transfo_info : transformation_info) (telescope_oib : term -> term)
  (nb_oib : nat)
  (cons : constructor_body)
  : constructor_body :=
  
  (*lifts by the number of mutual inductives the last inductive call so that it is not replaced by the explicit call to Relation, so that it is not affected by the replacement.*)
  let lift_type :=
    lift_inductive cons.(cstr_type) ((index_oib transfo_info) + 1)
  in

  (*Adds let in declarations of the mutual inductives to explicit.*)
  let added_type := telescope_oib lift_type in
  (*Zeta-reduction*)
  let new_type :=
    remove_let_in added_type []
  in

  (*Inference of the new list arguments and indices from the changed type telescope.*)
  let new_args := telescope_to_args new_type (pmib transfo_info).(pseudo_npars) cons.(cstr_arity) in
  let new_indices := telescope_to_indices new_type (pmib transfo_info).(pseudo_npars) in

  {|
    cstr_name := cons.(cstr_name);
    cstr_args := new_args;
    cstr_indices := new_indices;
    cstr_arity := cons.(cstr_arity);
    cstr_type := new_type
  |}.

Definition derecursivation_oib
  (transfo_info : transformation_info) (telescope_oib : term -> term)
  : pseudo_oib :=
  let poib := poib transfo_info in

  (*Zeta-reduction *)
  let new_type :=
    remove_let_in (telescope_oib poib.(pseudo_type)) []
  in
  (*Inference of the new indices and their types.*)
  let new_indices :=
    telescope_to_args new_type (pmib transfo_info).(pseudo_npars) (length poib.(pseudo_indices))
  in
  {|
    pseudo_name := poib.(pseudo_name);
    pseudo_indices := new_indices;
    pseudo_sort := poib.(pseudo_sort);
    pseudo_type :=  new_type;
    pseudo_kelim := poib.(pseudo_kelim);
    pseudo_projs := poib.(pseudo_projs);
    pseudo_relevance := poib.(pseudo_relevance)
  |}.


Definition derecursivation_mib
  (transfo_info : transformation_info) (telescope_oib : term -> term)
  (nb_oib : nat)
  : transformation_info :=
  let pmib := pmib transfo_info in
  let new_poib := derecursivation_oib transfo_info telescope_oib in
  let new_cons :=
    map_list_options
      (derecursivation_constructor transfo_info telescope_oib nb_oib)
      (lctors transfo_info)
  in
  recreate_transfo_info transfo_info pmib new_poib new_cons.


(** Full  derecursivation, also changes the final call to the inductive.
A list of instranciated values of the parameters can also be given to be propagated.*)


Definition full_derecursivation_constructor
  (transfo_info : transformation_info)
  (instanciated_parameter_list : list term)
  (telescope_oib : term -> term)
  (cons : constructor_body): constructor_body :=


  (*Adds let in declarations of the mutual inductives to explicit.*)
  let letin_type :=  telescope_oib cons.(cstr_type)  in
  (*Zeta-reduction*)
  let instanciated_type :=
    remove_let_in letin_type []
  in
  (*Transformation des parametres de forall en let in pour les valeurs instanciées.*)
  let added_type := (prod_to_letin instanciated_type instanciated_parameter_list)in
  (*Zeta-reduction*)
  let new_type :=
    remove_let_in added_type []
  in

  (*Removes the parameters and generate the new argument list.*)
  let new_args :=
    telescope_to_args
      new_type
      ((pmib transfo_info).(pseudo_npars)- length instanciated_parameter_list)
      (cons.(cstr_arity))
  in
  let new_indices := telescope_to_indices new_type ((pmib transfo_info).(pseudo_npars)- length instanciated_parameter_list) in

  {|
    cstr_name := cons.(cstr_name);
    cstr_args := new_args;
    cstr_indices := new_indices;
    cstr_arity := cons.(cstr_arity);
    cstr_type := new_type
  |}.

Definition full_derecursivation_oib
  (transfo_info : transformation_info)(instanciated_parameter_list : list term)
  (telescope_oib : term -> term)
  : pseudo_oib :=
  
  let poib := poib transfo_info in
  (*Instanciate via let in the  parameters in the type telescope*)
  let let_in_type := prod_to_letin poib.(pseudo_type) instanciated_parameter_list in
  (*Adds let ins for mutual inductives*)
  let added_type := telescope_oib let_in_type in
  (* Zeta-reduction*)
  let new_type :=
    remove_let_in added_type []
  in
  
  let new_indices := telescope_to_args new_type ((pmib transfo_info).(pseudo_npars) - length instanciated_parameter_list) (length poib.(pseudo_indices)) in
  
  {|
    pseudo_name := poib.(pseudo_name);
    pseudo_indices := new_indices;
    pseudo_sort := poib.(pseudo_sort);
    pseudo_type :=  new_type;
    pseudo_kelim := poib.(pseudo_kelim);
    pseudo_projs := poib.(pseudo_projs);
    pseudo_relevance := poib.(pseudo_relevance)
  |}.

Definition full_derecursivation_mib
  (transfo_info : transformation_info)
  (instanciated_parameter_list : list term)
  (telescope_oib : term -> term)
  : transformation_info :=
  let pmib := pmib transfo_info in
  
  let new_cons :=
    map_list_options
      (full_derecursivation_constructor transfo_info instanciated_parameter_list telescope_oib)
      (lctors transfo_info)
  in
  let new_poib :=
    full_derecursivation_oib transfo_info instanciated_parameter_list telescope_oib

  in

  let (_,new_pars) :=
    firstn_lastn pmib.(pseudo_params) (pmib.(pseudo_npars) - (length instanciated_parameter_list))
  in
  let new_pmib :=
    {|
      pseudo_finite := pmib.(pseudo_finite);
      pseudo_npars := pmib.(pseudo_npars) - (length instanciated_parameter_list);
      pseudo_params :=  new_pars;
      pseudo_universes := pmib.(pseudo_universes);
      pseudo_variance := pmib.(pseudo_variance);
    |}
  in
  recreate_transfo_info transfo_info new_pmib new_poib new_cons.




(*Removes the need for external info, used in specialisation*)

Definition full_derecursivation_constructor'
  (instanciated_parameter_list : list term)
  (cons : constructor_body): constructor_body :=
  (*Transformation des parametres de forall en let in pour les valeurs instanciées.*)
  let tLetIn_params := list_term_to_letin instanciated_parameter_list in
  let added_type := tLetIn_params cons.(cstr_type) in
  (*Zeta-reduction*)
  let new_type :=
    remove_let_in added_type []
  in

  (*Removes the parameters and generate the new argument list.*)
  let new_args :=
    telescope_to_args
      new_type
      0
      (cons.(cstr_arity))
  in
  let new_indices := telescope_to_indices new_type 0 in

  {|
    cstr_name := cons.(cstr_name);
    cstr_args := new_args;
    cstr_indices := new_indices;
    cstr_arity := cons.(cstr_arity);
    cstr_type := new_type
  |}.
