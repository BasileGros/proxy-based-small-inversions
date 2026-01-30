(** * Change into parameters all indices of a given inductive.
It is done incrementally, indices are checked one by one, left to right,
 when one is found to be parameterisable is is parameterised,
then the process restarts.
 *)
From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
Import MRMonadNotation.

From utils Require Import utils.
From SmallInversion Require Import strategy_engine.
From SmallInversion Require Import proxy_identity.

(** * Finding Indices that can be parameterised
 i.e. finding indices that are variables in the conclusions of all the constructors
 and that are not dependant on other indices.*)

(** The find_variables functions check if there is a variable in a telescope that points to an other element of this same telescope. *)
Definition find_variables_range_predicate (p : predicate term) (threshold:nat) (depth : nat) (f : nat -> nat -> term -> option nat) :=
  let list_res_params := map (f threshold depth) (pparams p) in
  let res_params := fold_left merge_option list_res_params None in
  let depth' := depth + length (pparams p) in
  let threshold' := threshold + length (pparams p) in
  let res_return := f threshold' depth' (preturn p) in
  merge_option res_params res_return.


Definition find_variables_range_branch (threshold:nat)(depth : nat) (f : nat -> nat -> term -> option nat) (br : branch term)  :=
  let depth' := length (bcontext br) + depth in
  let threshold' := length (bcontext br) + threshold in
  f threshold' depth' (bbody br).


Fixpoint find_variables_range  (threshold : nat) (depth : nat) (t : term) : option nat :=
match t with
| tEvar ev args => fold_left merge_option (map (find_variables_range threshold depth) args ) None
| tCast c kind t0 => merge_option (find_variables_range threshold depth c) (find_variables_range threshold depth t0)
| tProd _ A B =>
    merge_option
      (find_variables_range threshold depth A)
      (find_variables_range (threshold + 1) (depth + 1) B)
| tLambda _ T M =>
    merge_option
      (find_variables_range threshold depth T)
      (find_variables_range (threshold + 1) (depth + 1) M)
| tLetIn _ b t0 c =>
    let a := merge_option (find_variables_range threshold depth b) (find_variables_range threshold depth t0) in
    merge_option a (find_variables_range (threshold + 1) (depth + 1) c)
| tApp u v =>
    let a := fold_left merge_option (map (find_variables_range threshold depth) v ) None in
    merge_option (find_variables_range threshold depth u) a
| tProj _ c => find_variables_range threshold depth c
| tFix mfix _ =>
    let depth' := length (fix_decls mfix) + depth in
    let threshold' := length (fix_decls mfix) + threshold in
    let list_res := map (map2_def merge_option (find_variables_range threshold depth) (find_variables_range threshold depth')) mfix in
    fold_left merge_option list_res None
| tCoFix mfix _ =>
    let depth' := length (fix_decls mfix) + depth in
    let threshold' := length (fix_decls mfix) + threshold in
    let list_res := (map (map2_def merge_option (find_variables_range threshold depth) (find_variables_range threshold' depth')) mfix) in
    fold_left merge_option list_res None
| tCase ci p c brs =>
    let res_pred := find_variables_range_predicate p threshold depth find_variables_range in
    let list_res_branch := map (find_variables_range_branch threshold depth find_variables_range) brs in
    let res_branch := fold_left merge_option list_res_branch None in
    merge_option res_pred res_branch
                 
| tRel n => if (n <? threshold) && (depth <=? n) then Some (n - depth) else None
                                             
|_ => None
end.

(** Checking that a given index is a variable in all constructor conclusions *)

(*Checks if an index in the conclusion of a constructor is a variable that points to one of the arguments of this constructor. *)
Definition is_variable_in_conclusion (position_index : nat) (cons : constructor_body) : bool :=
  
  match nth_error cons.(cstr_indices) position_index with
  |None => false
  |Some (tRel a) => a <? length cons.(cstr_args)
  |Some _ => false
  end.

(*Maps the precedent variable check to all constructors of an inductive.*)
Definition is_variable_in_constructors (position_index : nat) (lcons : list (option constructor_body)) : bool :=
  let list_res := map_list_options (is_variable_in_conclusion position_index) lcons in
  fold_left andb (concat_options list_res) true.


(*Finds the first index of an inductive that is not dependent on an other index and has all its values in the conclusions of the constructors in the form of variables pointing at constructor arguments*)
Fixpoint first_parameterisable_list_index (index_telescope:term)(constructors : list (option constructor_body))(pos:nat) :=
  match index_telescope with
  |tProd _ type b =>
     match find_variables_range pos 0 type with
     |None =>
        if is_variable_in_constructors pos constructors
        then
          Some pos
        else
          first_parameterisable_list_index b constructors (pos + 1)
     |Some _ => first_parameterisable_list_index b constructors (pos + 1)
     end
  |tLambda _ type b =>
     match find_variables_range pos 0 type with
     |None =>
        if is_variable_in_constructors pos constructors
        then
          Some pos
        else
          first_parameterisable_list_index b constructors (pos + 1)
     |Some _ => first_parameterisable_list_index b constructors (pos + 1)
     end
  | _ => None
  end.

(*Wrapper of the previous check to work on a one_inductive_body*)
Definition first_parameterisable_index_oib
  (poib : pseudo_oib)(nb_params : nat)
  (lctors : list (option constructor_body))
  : option nat :=
  let telescope_without_params := peel_telescope poib.(pseudo_type) nb_params in
  first_parameterisable_list_index telescope_without_params lctors 0.

(** * Parameterising an inductive for a given index. *)
(** Changing the positions of the index being parameterised
 to be with the other parameters at the beginning of the telescope*)

(*In the type telescope of an inductive, change the position of the index that is being paramtrized.*)
Definition parameterise_index (pos_index:nat)(nb_params:nat)(telescope:term) :=
  let (insert_params,telescope_without_params) := cut_telescope telescope nb_params in
  (*Lift references to other parameters*)
  let lift_telescope := lift0 1 telescope_without_params in

  (*Get the parameter to insert after zeta-reduction*)
  let (part_to_letin,_) := cut_telescope telescope_without_params (pos_index + 1) in
  let list_dummy := list_const (tVar "dummy") pos_index in
  let let_in_param := prod_to_letin (part_to_letin (tVar "dummy")) list_dummy in
  let reduced_param := remove_let_in let_in_param [] in
  let (insert_new_param,_) := cut_telescope reduced_param 1 in

  (*Transforms the index into a let in pointing to the parameter *)
  let telescope_let_in := nth_prod_to_letin lift_telescope (tRel pos_index) pos_index in
  let full_telescope := insert_params (insert_new_param telescope_let_in) in
  let parameterised_telescope := remove_let_in full_telescope [] in
  parameterised_telescope.

(*In the telescope of a constructor,
change the position of the index that is being parameterised in the conclusion of the constructor,
and remove the argument it points to from the constructor's arguments.*)
Definition parameterise_index_constructor (position_index:nat)(nb_params:nat)(const : constructor_body) :=
  match nth_error const.(cstr_indices) position_index with
  |Some (tRel a) =>
     let pos_arg := (const.(cstr_arity)) - (a + 1) in
     (*Witch the position of the constructor argument to reflect its new parameter status.*)
     let modified_telescope_type := parameterise_index pos_arg nb_params const.(cstr_type) in

     (*Get the indices in the conclusion of the constructor*)
     let concl_type := telescope_to_indices modified_telescope_type 0 in
     (*Remove the parameterised index*)
     let (concl_without_index, opt_var_index) := remove_and_return_index_from_list concl_type (position_index + nb_params) in
     match opt_var_index with
     |Some var_index =>
        (*Add back the removed index a the end of the parameters*)
        let new_concl := insert_list_in_list [var_index] concl_without_index nb_params in
        (*Put back the indices at the conclusion of the constructor telescope*)
        let new_type := insert_new_concl_telescope modified_telescope_type new_concl in

        (*Compute the new values of the other fields of the constructor.*)
        let new_arity := const.(cstr_arity) - 1 in
        let new_args := telescope_to_args new_type (nb_params + 1) new_arity in
        let new_indices := telescope_to_indices new_type (nb_params + 1) in
        let new_name := const.(cstr_name) in
        Success ({|
            cstr_name := new_name;
            cstr_args := new_args;
            cstr_indices := new_indices;
            cstr_type := new_type;
            cstr_arity := new_arity;

          |},pos_arg)
     |None =>
        Error (
            "Error when parameterising constructor " ^
              const.(cstr_name) ^ " for index " ^
                (string_of_nat position_index) ^
                  ": conclusion too short")
     end
  |None => Error (
              "Error when parameterising constructor "
              ^ const.(cstr_name) ^ " for index " ^
                (string_of_nat position_index) ^
                  ": not an index")
  |Some _ => Error (
                "Error when parameterising constructor " ^
                  const.(cstr_name) ^
                    " for index " ^
                      (string_of_nat position_index) ^
                        ": not a variable")
  end.

(** The iteration function and its wrappers*)
(*Parameterise the indices (in a left to right pattern) of a one_inductive_body.*)
Fixpoint parameterise_all_possible_indices
  (poib : pseudo_oib)
  (lctors : list (option constructor_body))
  (nb_params : nat)
  (fuel : nat)
  (list_pos : list nat)
  (list_args : list (list nat))
  : ErrorMonad ((((pseudo_oib × list (option constructor_body)) × nat) × list nat) × list (list nat)) :=
  match fuel with
  |0 => Success (poib, lctors, nb_params, list_pos, list_args)
  |S new_fuel =>
     match first_parameterisable_index_oib poib nb_params lctors with
     |None => Success (poib, lctors, nb_params, list_pos, list_args)
     |Some pos =>
        
        let new_type := parameterise_index pos nb_params poib.(pseudo_type) in
        couple <-?
          map_err_list_options
          (parameterise_index_constructor pos nb_params)
          lctors;;
        let (new_constructors, olist_cons_args) :=
          split (map split_option couple)
        in
        let list_cons_args := concat_options olist_cons_args in
        let new_indices :=
          telescope_to_args new_type (nb_params + 1) (length poib.(pseudo_indices) - 1)
        in
        
        parameterise_all_possible_indices (
           {|
                  pseudo_name := poib.(pseudo_name);
                  pseudo_indices := new_indices;
                  pseudo_sort := poib.(pseudo_sort);
                  pseudo_type :=  new_type;
                  pseudo_kelim := poib.(pseudo_kelim);
                  pseudo_projs := poib.(pseudo_projs);
                  pseudo_relevance := poib.(pseudo_relevance)
                |}
              
          )
          new_constructors
          (nb_params + 1)
          new_fuel
          ((pos + length list_pos)::list_pos)
          (list_cons_args::list_args)
     end
  end.

(*Wrapper for mib definition and naming of the parameterisation of an inductive.*)
Definition parameterise_inductive_error (transfo_info : transformation_info)
  :  ErrorMonad
       ((((pseudo_mib × pseudo_oib) × list (option constructor_body)) × list nat) × list (list nat))
  :=
  let poib := poib transfo_info in
  let lctors := lctors transfo_info in
  '(param_oib, param_lctors, new_npars, list_pos, list_args) <-?
    parameterise_all_possible_indices
    poib
    lctors
    ((pmib transfo_info).(pseudo_npars))
    (length poib.(pseudo_indices)) [] []
  ;;
  let new_name := poib.(pseudo_name)in
  let new_poib :=
    {|
      pseudo_name := new_name;
      pseudo_indices := param_oib.(pseudo_indices);
      pseudo_sort := param_oib.(pseudo_sort);
      pseudo_type := param_oib.(pseudo_type);
      pseudo_kelim := poib.(pseudo_kelim);
      pseudo_projs := poib.(pseudo_projs);
      pseudo_relevance := poib.(pseudo_relevance)
    |} in
  
  let new_params := telescope_to_args param_oib.(pseudo_type) 0 new_npars in
  Success
    ({|
        pseudo_finite := (pmib transfo_info).(pseudo_finite);
        pseudo_npars := new_npars;
        pseudo_params := new_params;
        pseudo_universes := (pmib transfo_info).(pseudo_universes);
        pseudo_variance := (pmib transfo_info).(pseudo_variance)
      |},
      new_poib, param_lctors, list_pos, list_args).



(** * Creating the proxy type adapter and the proxy adapters.*)

(*Change the type of the constructor to move the new parameter *)
Definition change_type_call_constr
  (type: term)
  (type_repar : term)
  (list_args_repar : list nat)
  (nb_old_params : nat)
  (name_disp : string)
  : term :=
  let peeled_type :=
    peel_telescope type nb_old_params
  in
  let (insert_params, _) :=
    cut_telescope type_repar (length list_args_repar + nb_old_params)
  in
  let let_in_type :=
    insertion_list_letin_position peeled_type list_args_repar
  in
  
 (*The type of the constructor in parameter*)
  let disp_type := var_inductive let_in_type (tVar name_disp) in
  let insert_type := (insert_params disp_type) in
  let new_type := remove_let_in insert_type [] in
  (*let disp_type := var_inductive type_repar (tVar name_disp) in
  let new_type := remove_let_in disp_type [] in*)
  (*let l:= map (fun n => tVar (string_of_nat n)) list_args_repar in
tApp (tVar name_disp) l*)
  new_type
.
  
Fixpoint pos_arg (rel_pos_arg : nat) (acc : nat) (list_acc : list bool) :=
  match list_acc, rel_pos_arg with
  |[], _ => Error "list of args not of correct length"
  |false::tl, 0 => Success (true::tl, acc)
  |false::tl, S n =>
     '(nlist_acc, nacc) <-? pos_arg n (S acc) tl;;
     Success (false::nlist_acc, nacc)
  |true::tl, _ =>
     '(nlist_acc, nacc) <-? pos_arg rel_pos_arg (S acc) tl;;
     Success (true::nlist_acc, nacc)
  end.

Fixpoint list_pos_arg (list_rel_pos_args : list nat)(list_acc : list bool):=
  match list_rel_pos_args with
  |[] => Success []
  |hd::tl =>
     '(nlist,npos) <-? pos_arg hd 0 list_acc;;
     ntl <-? list_pos_arg tl nlist;;
     Success (npos::ntl)
  end.

Definition list_pos_args (list_rel_pos_args : list nat)(nb_args : nat) :=
  list_pos_arg list_rel_pos_args (list_const false nb_args).

(*Creation of the proxy adapter for a constructor of the inductive to parameterise*)
Definition proxy_constructor_reparam
  (old_params : context) (decl_disp : context_decl)
  (name_disp : string)
  (calls_old_params : list term)(poib_repar : pseudo_oib)
  (glob:global_env) (offset:nat)
  (constructor_init : constructor_body)
  (constructor_repar : constructor_body)
  (list_args_repar : list nat)
  :=

  list_position_args <-? list_pos_args list_args_repar constructor_init.(cstr_arity);;
  
  let named_args := name_context constructor_init.(cstr_args) (offset+ 1) in
  
  (*Create the variable calls to refer to the parameters and indices of the inductive.*)
  let calls_old_args := context_to_call named_args in
  
  let (calls_new_args, calls_opt_new_params) :=
    separate_list (calls_old_args,[]) list_position_args (length list_args_repar)
  in

  let type_call_constr := 
    (*(constructor_repar.(cstr_type)) in*)
  
    change_type_call_constr
      (constructor_init.(cstr_type))
      (constructor_repar.(cstr_type))
      (list_position_args) (*list_args_repar*)
      (length old_params)
      name_disp
  in
  
  let context_constructor :=
    [vass  (string_to_aname ("_"^constructor_repar.(cstr_name)^"_reparam")) type_call_constr]
  in
  
  (*Name the contexts of the inductive for the future variable uses. *)
  let ctx_old_params_args := named_args ++ old_params in

  match unfold_option (rev calls_opt_new_params) with
  |None => Error "One of the arguments to parameterise was not found"
  |Some calls_new_params =>
     (*Creates the telescope by successively adding the different elements and transforming the variabel references into De Bruijn indexes.*)
     let call_constructor :=
       tApp (tVar ("_" ^ constructor_repar.(cstr_name)^"_reparam")) ( (calls_old_params) ++ (calls_new_params) ++ calls_new_args)
     in
     let proxy_without_cons := append_context_vars_lambda glob ctx_old_params_args call_constructor in
     let proxy := append_context_vars_lambda glob (context_constructor ++ [decl_disp]) proxy_without_cons in
     Success (Some proxy)
  end.

(*Creation of the proxy adapter for the type of the inductive to parameterise*)
Definition proxy_type_reparam
  (transfo_info : transformation_info) (derec_poib : pseudo_oib)
  (derec_lctors : list (option constructor_body))
  (lctors_repar: list (option constructor_body))
  (poib_repar : pseudo_oib)
  (list_isparam : list nat) (lists_args_reparam : list (list nat))
  : ErrorMonad (term × list (option term)) :=
 


  let l := mapi (fun i l => tApp (tVar (string_of_nat i)) (map (fun n => tVar (string_of_nat n)) l)) lists_args_reparam in
  
  let name_type := "_"^(poib_repar).(pseudo_name)^"_reparam" in
  let decl_type :=
    vass
      (string_to_aname name_type)
      (poib_repar).(pseudo_type)
  in
  let concat_lctors := (concat_options lctors_repar) in

  (*Name the contexts of the inductive for the future variable uses. *)

  let ctx_old_indices := name_context derec_poib.(pseudo_indices) (length concat_lctors) in
  let named_params := name_context (pmib transfo_info).(pseudo_params) (length concat_lctors + length ctx_old_indices) in
  let ctx_old_params_indices := ctx_old_indices ++ named_params in

  (*Create the variable calls to refer to the parameters and indices of the inductive.*)
  let calls_old_params_indices := context_to_call ctx_old_params_indices in
  let calls_old_params := context_to_call named_params in
  let calls_old_indices := context_to_call ctx_old_indices in

  (*Computes the references to new indices and parameters.*)
  let (calls_new_indices, calls_opt_new_params) :=
    separate_list (calls_old_indices,[]) list_isparam ((length list_isparam))
  in

  match unfold_option ( calls_opt_new_params) with
  |None => Error "One of the index to parameterise was not found"
  |Some calls_new_params =>
     
     (*Creates the telescope by successively adding the different elements and transforming the variable references into De Bruijn indexes.*)
     let tail_proxy_type :=
       tApp (tVar name_type) (*l*) (calls_old_params ++ calls_new_params++ calls_new_indices)
     in
     let proxy_type_without_dispatch :=
       append_context_vars_lambda (env_quote transfo_info) ctx_old_params_indices tail_proxy_type
     in
     let proxy_type :=
       append_context_vars_lambda (env_quote transfo_info) [decl_type] proxy_type_without_dispatch
     in
     let ordered_lists_args_reparam :=
       get_vertical_slices lists_args_reparam (length concat_lctors)
     in
     
     let name_disp := "_"^(poib transfo_info).(pseudo_name)^"_reparam" in
     let decl_disp :=
       vass
         (string_to_aname name_disp)
         (derec_poib).(pseudo_type)
     in

     
     match list_isparam with
     |[] =>
        let proxy_constructors :=
          map_list_options (fun l => proxy_adapter_identity decl_disp ((poib transfo_info).(pseudo_name)^"_reparam") transfo_info l) lctors_repar
        in
        Success (proxy_type, proxy_constructors)
     |_ =>  
        proxy_constructors <-?
          map3_err_option
          (proxy_constructor_reparam
             named_params
             decl_disp name_disp
             calls_old_params
             poib_repar
             (env_quote transfo_info)
             (length derec_poib.(pseudo_indices) + length lctors_repar)
          )
          
          derec_lctors
          lctors_repar
          ordered_lists_args_reparam
        ;;
        Success (proxy_type, proxy_constructors)
        
     end
 end.


(*Wrapper to call the different functions to reparameterise.*)
Definition proxy_reparam_error
 (transfo_info : transformation_info) :=
  '(mib_repar, oib_repar, lctors_repar, list_pos, list_args) <-?
    parameterise_inductive_error transfo_info
  ;;
  '(proxy_type, list_proxy_cons) <-?
    proxy_type_reparam transfo_info
    (poib transfo_info) (lctors transfo_info)
    lctors_repar oib_repar
     list_pos list_args
  ;;
  Success (proxy_type, list_proxy_cons, mib_repar, oib_repar, lctors_repar).


(*Adapter to fit the definition of a transformation.
 Supposes that the mib is already deparameterised.*)
Definition transfo_parameterisation : transfo :=
  fun (transfo_info : transformation_info) =>
    '(proxy_type_adapter, list_proxy_cons_adapter, mib_reparam, oib_repar, lctors_repar) <-?
      proxy_reparam_error transfo_info;;
    let transfo_info_reparam :=
      recreate_transfo_info transfo_info mib_reparam oib_repar lctors_repar
    in
    Success ((proxy_type_adapter,list_proxy_cons_adapter),[transfo_info_reparam],fun l => l).
