(** * Transformation needed for dependent inversion*)
(* We suppose that deparametrisation HAS ALREADY TAKEN PLACE*)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.

Definition dependent_constructor
  (og_inductive : inductive)(nb_params : nat)
  (pos_cons : nat) (cons : constructor_body)
  : constructor_body :=

  let range_db_args := rev_range_deBruijn (cons.(cstr_arity) + nb_params) 0 in
  let call_const :=
    tApp (tConstruct og_inductive pos_cons []) range_db_args
  in
  let new_type := add_to_concl_telescope cons.(cstr_type) [call_const] in
  
  let new_indices := telescope_to_indices new_type nb_params in
  let new_name := cons.(cstr_name) in
  {|
    cstr_name := new_name;
    cstr_args := cons.(cstr_args);
    cstr_indices := new_indices;
    cstr_arity := cons.(cstr_arity);
    cstr_type := new_type
  |}.


Definition dependent_oib  (poib : pseudo_oib)(term_og_inductive : term)
  (nb_params : nat) : pseudo_oib :=

  let range_db_indices := rev_range_deBruijn (length poib.(pseudo_indices) + nb_params) 0 in
  let type_old_inductive :=
    tApp term_og_inductive range_db_indices
  in
  let tprod_old_inductive :=
    fun x => tProd nameAnon type_old_inductive x
  in
  let new_type :=
    insert_tProd_in_type
      poib.(pseudo_type) (length poib.(pseudo_indices) + nb_params) tprod_old_inductive
  in
  let new_indices :=
    telescope_to_args new_type nb_params (length poib.(pseudo_indices) + 1)
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
