From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
Import MRMonadNotation.
From utils Require Import utils.
From SmallInversion Require Import data_extraction.
From SmallInversion Require Import strategy_engine.
From SmallInversion Require Import derecursivation.

(*A data type that stores the form of the call for the pilot inductive
 in a given constructor*)
Inductive ref_pilot :=
(*A constructor applied to some arguments in the form of de Bruijn indexes*)
|application : nat (*The id of the constructor*) ->
               list term (*its parameters, included in the next list but separated for ease of use*) ->
               list term (*the objects it's applied to*) ->
               ref_pilot
(*A de Bruijn refering to a constructor argument*)
|variable : nat (*The value of the de Bruijn*) ->
            nat (*The position of the variable in the telescope*) ->
            list term (*The parameters in its type*) ->
            ref_pilot
.


(*Stores the relation that a constructor of the pilot is present
in a conclusion of a constructor of the relation.
 We call this relation the reference relation*)
Record reference_info : Type :=
  mkRefInfo {
      index_cons_relation : nat;
      cons_relation : constructor_body;
      reference_pilot : ref_pilot;
      name_ind_part: string;
      index_cons_pilot : nat;
      cons_pilot : constructor_body;
    }.


Fixpoint get_ref_info_from_R (index_cons_R : nat) (l : list reference_info) :=
  match l with
  |[] => Error "No inversion for constructor"
  |ref_info :: tl =>
     if ( index_cons_relation ref_info) =? index_cons_R
     then Success ref_info
     else get_ref_info_from_R index_cons_R tl
  end.

Definition print_ref_info (r: reference_info) : string :=
  "(R : " ^
    string_of_nat r.(index_cons_relation) ^
      ", P : " ^
        string_of_nat r.(index_cons_pilot) ^
          ", " ^
            r.(name_ind_part) ^
              ")".

Fixpoint print_list_inv (l : list reference_info) : string :=
  match l with
  |[] => ""
  |t::q => (print_ref_info t)^(print_list_inv q)
  end.



Record specialisation_info : Type :=
  mkSpecInfo {
      transfo_info_R : transformation_info;
      
      position_pilot : nat;
      (*The internal structures of the relation*)
      pmib_R : pseudo_mib;
      poib_R : pseudo_oib;
      lctors_R : list (option constructor_body);
      nb_indices_R : nat;
      (*The name of the relation*)
      ident_R : string;
      
      
      inductive_P : inductive;
      nb_params_P : nat;
      nb_indices_P : nat;
      parametres_P : list term;
      indices_P : context;
      list_constructors_P : list constructor_body;
      name_oib_P : string;

      (*The reference relation with the index of the pilot constructor as key*)
      list_ref_P : (list (nat * (list reference_info)));
      (*The reference relation with the index of the relation constructor as key*)
      list_ref_R : (list (nat * (list reference_info)));
      (*The path to the file from where the metacoq call for the small inversion was made.*)
      modpath_call_spec : modpath;
      name_dispatch : string;
      transfo_info_spec : transformation_info;
      telescope_oib_P : term -> term;
      og_transfo_info_P : transformation_info;
    }.

(*Extracts the Metacoq term of the type of the pilot argument*)
Definition extraction_parameters_cons_pilot (cons : constructor_body) (position_variable:nat):
  ErrorMonad (list term)
  :=
  
  match nth_error (rev cons.(cstr_args)) position_variable with
    
  |Some element_context => match element_context.(decl_type) with
                          |tApp _ l => Success l
                          |_ => Success []
                          end
  |None                 =>
     Error ("Variable not found " ^ cons.(cstr_name) ^ " " ^ (string_of_nat position_variable))
  end.


(*In the case the pilot is in the form of a variable in a constructor of the relation,
 create the record of the reference relation for all constructors of the pilot*)
Fixpoint aux_form_ref_variable
  (nb_constructor_P : nat)
  (list_constructors_P : list constructor_body)
  (de_Bruijn_index : nat) (position_constructor_R : nat)
  (constructor_R : constructor_body)
  (ident_R : string)
  (acc_R : list reference_info) (acc_P : list (nat * (list  reference_info)))
  : ErrorMonad ((list reference_info) * (list (nat * (list  reference_info)))) :=
  match nb_constructor_P with
  |0 => Success (acc_R,acc_P)
  |S n =>
     let position_constructor_P := nb_constructor_P - 1 in
     match nth_error list_constructors_P position_constructor_P with
     |None =>
        Error (
            "data_extraction.form_pilot_ref_variable : " ^
              "Constructor number " ^
                (string_of_nat position_constructor_P) ^
                  " of the pilot not found while inverting constructor number " ^
                    (string_of_nat position_constructor_R) ^ " of the relation")
     |Some constructor_P =>
        let position_variable := constructor_R.(cstr_arity) - (de_Bruijn_index + 1) in
        list_params_type <-? extraction_parameters_cons_pilot constructor_R position_variable ;;
        let new_name := ident_R^"_"^constructor_P.(cstr_name) in
        let info_head :=
          mkRefInfo
            position_constructor_R constructor_R
            (variable de_Bruijn_index position_variable list_params_type)
            new_name
            position_constructor_P constructor_P
        in
        aux_form_ref_variable
          n list_constructors_P de_Bruijn_index position_constructor_R
          constructor_R ident_R (info_head::acc_R)
          ((position_constructor_P, [info_head])::acc_P)
     end
  end.

Definition form_ref_variable
  (nb_constructor_P : nat)
  (list_constructors_P : list constructor_body)
  (de_Bruijn_index : nat) (position_constructor_R : nat)
  (constructor_R : constructor_body)
  (ident_R : string)
  : ErrorMonad ((list reference_info) * (list (nat * (list  reference_info)))) :=
  '(list_R, list_P) <-? aux_form_ref_variable
    nb_constructor_P
    list_constructors_P
    de_Bruijn_index
    position_constructor_R
    constructor_R
    ident_R
    []
    []
  ;;
  Success (rev list_R, rev list_P).



(*Creates the two reference relations relation that store
  - for each constructor of the relation which constructor of the pilot can be in its conclusion,
    and under which form
  - for each constructor of the pilot which constructor of the relation it can be in the conclusion of,
    and under which form.*)
Fixpoint aux_form_ref_info
  (position_pilot:nat)
  (list_constructors_P : list constructor_body)
  (nb_params_P:nat)
  (list_constructor_R: list (option constructor_body))
  (nb_constructor_P: nat)
  (position_constructor_R : nat)
  (ident_R : string)
  (acc_R : list (nat * (list reference_info)))
  (acc_P : list (nat * (list reference_info)))
  : ErrorMonad ((list (nat * (list reference_info))) * (list (nat * (list reference_info)))) :=
  match list_constructor_R with
  |[] => Success (acc_R,acc_P)
  |None :: t_constructor_R =>
     aux_form_ref_info
       position_pilot
       list_constructors_P nb_params_P
       t_constructor_R nb_constructor_P
       (position_constructor_R+1)
       ident_R acc_R acc_P
  |Some constructor_R :: t_constructor_R =>
     
     match nth_error (constructor_R.(cstr_indices)) position_pilot with
       
     |Some index =>
        match index with
        |tConstruct _ position_constructor_P _                  =>
           match nth_error list_constructors_P position_constructor_P with
           |None =>
              Error (
                  "data_extraction.form_pilot_ref_info : " ^
                    "Constructor number " ^
                      (string_of_nat position_constructor_P) ^
                        " of the pilot not found while inverting constructor number " ^
                          (string_of_nat position_constructor_R) ^ " of the relation")
           |Some constructor_P =>
              let new_name := ident_R ^ "_" ^ constructor_P.(cstr_name)in
              let infos_ref_pilot :=
                mkRefInfo
                  position_constructor_R constructor_R
                  (application position_constructor_P [] [])
                  new_name
                  position_constructor_P constructor_P
              in
              let new_acc_R := ((position_constructor_R,[infos_ref_pilot])::acc_R) in
              let new_acc_P := merge_in_map position_constructor_P [infos_ref_pilot] acc_P in
              aux_form_ref_info
                position_pilot
                list_constructors_P nb_params_P
                t_constructor_R nb_constructor_P
                (position_constructor_R+1)
                ident_R new_acc_R new_acc_P
           end
             
        |tApp (tConstruct _ position_constructor_P _) list_args =>
           match nth_error list_constructors_P position_constructor_P with
           |None =>
              Error (
                  "data_extraction.form_pilot_ref_info : " ^
                    "Constructor number " ^ (string_of_nat position_constructor_P) ^
                      " of the pilot not found while inverting constructor number " ^
                        (string_of_nat position_constructor_R) ^ " of the relation")

           |Some constructor_P =>
              let new_name := ident_R ^ "_" ^ constructor_P.(cstr_name) in
              let list_params := firstn nb_params_P list_args in
              let infos_ref_pilot :=
                mkRefInfo
                  position_constructor_R constructor_R
                  (application position_constructor_P list_params list_args)
                  new_name
                  position_constructor_P constructor_P
              in
              let new_acc_R := ((position_constructor_R,[infos_ref_pilot])::acc_R) in
              let new_acc_P := merge_in_map position_constructor_P [infos_ref_pilot] acc_P in
              aux_form_ref_info position_pilot
                list_constructors_P nb_params_P
                t_constructor_R nb_constructor_P
                (position_constructor_R+1) ident_R new_acc_R new_acc_P
           end
        |tRel de_Bruijn_index  =>
           lists <-? form_ref_variable
             nb_constructor_P list_constructors_P
             de_Bruijn_index position_constructor_R
             constructor_R ident_R
           ;;
           let (list_info_pilot_R, list_info_pilot_P) := lists in
           let new_acc_R := ((position_constructor_R,list_info_pilot_R)::acc_R) in
           let new_acc_P :=
             fold_right
               (fun (tail:nat*(list reference_info)) list_P =>
                  let (indice, infos) := tail in
                  merge_in_map indice infos list_P)
               acc_P list_info_pilot_P
           in
           aux_form_ref_info
             position_pilot list_constructors_P
             nb_params_P t_constructor_R
             nb_constructor_P (position_constructor_R+1)
             ident_R
             new_acc_R new_acc_P

        |_   =>
           Error (
               "data_extraction.form_pilot_ref_info : " ^
                 "Call to the pilot not an inductive or a variable in constructor number " ^
                   (string_of_nat position_constructor_R) ^ " of the relation")
        end

     |None      =>  Error (
                       "data_extraction.form_pilot_ref_info : " ^
                         "Anomaly : pilot not found in constructor number " ^
                           (string_of_nat position_constructor_R) ^ " of the relation")
     end
  end.

Definition form_ref_info
  (position_pilot:nat)
  (list_constructors_P : list constructor_body)
  (nb_params_P:nat)  (list_constructor_R: list (option constructor_body))
  (nb_constructor_P: nat) (position_constructor_R : nat)
  (ident_R : string)
  : ErrorMonad ((list (nat * (list reference_info))) * (list (nat * (list reference_info))))
  :=
  aux_form_ref_info
    position_pilot list_constructors_P
    nb_params_P list_constructor_R
    nb_constructor_P position_constructor_R
    ident_R [] [].

(*Extracts the Metacoq term of the type of the pilot argument*)
Definition extraction_inductive_pilot (poib : pseudo_oib) (position_pilot:nat):
  ErrorMonad term
  :=
  
  match nth_error (rev poib.(pseudo_indices)) position_pilot with
    
  |Some element_context =>
     Success (element_context.(decl_type))
  |None                 =>
     Error
       ("The one_inductive_body " ^
          poib.(pseudo_name) ^
            " does not have an index at position " ^ (string_of_nat position_pilot))
  end.

(*Checks if at least one value of the index has the form of a constructor*)
Fixpoint check_ref_info  (l : list (nat * list reference_info) ):=
  match l with
  |[] => false
  |(_,ref)::tl =>
     match nth_error ref 0 with
     |None => false
     |Some r =>
        match reference_pilot r with
        |application _ _ _ => true
        |variable _ _ _ => check_ref_info tl
        end
     end
  end.


(*Check if pbsi is possible*)
Definition check_spec_info (spec_info : specialisation_info)
  : ErrorMonad (specialisation_info):=
  match indices_P spec_info with
  |_::_ => Error "Pilot index is dependent"
  |[] =>
     if check_ref_info (list_ref_R spec_info)
     then
       if isdep (transfo_info_spec spec_info)
       then
         if  (nb_indices_R spec_info) - (position_pilot spec_info + 1) =? 0
         then
           Error "Pilot index is the dependent index"
         else
           Success spec_info
       else
         Success spec_info
     else Error "Pilot index is only instanciated by variables"
  end.


(*Same check, but without the variable check, for forced patterns.*)
Definition check_spec_info_novar (spec_info : specialisation_info)
  : ErrorMonad (specialisation_info):=
  match indices_P spec_info with
  |_::_ => Error "Pilot index is dependent"
  |[] =>
     if isdep (transfo_info_spec spec_info)
     then
       if  (nb_indices_R spec_info) - (position_pilot spec_info + 1) =? 0
       then
         Error "Pilot index is the dependent index"
       else
         Success spec_info
     else
       Success spec_info
  end.

Definition data_extraction_spec
  (transfo_info : transformation_info) (position_pilot:nat) (is_forced : bool)
  : ErrorMonad (specialisation_info):=
  let prefix := prefix transfo_info in

  let pmib_R := pmib transfo_info in
  let poib_R := poib transfo_info in
  let nb_indices_R := (length poib_R.(pseudo_indices)) in
  let (_,ident_R) := inductive_mind (inductive_transfo transfo_info) in
  let list_constructors_R := lctors transfo_info in
  
  term_P <-? extraction_inductive_pilot poib_R position_pilot ;;
  '(inductive_P,parametres_P,tInd_P) <-? app_inductive_from_term term_P ;;
  '(mib_P, index_P) <-? mib_index_from_env tInd_P (env_quote transfo_info) ;;
  let telescope_oib_P :=
    create_telescope_letin_mutual_inductive inductive_P (length mib_P.(ind_bodies))
  in
  let nb_params_P := mib_P.(ind_npars) in
  let nb_oib_P  := length mib_P.(ind_bodies) in
  
  temp_oib_P <-? one_inductive_body_from_mib mib_P index_P ;;
  let transfo_info_P :=
    {|
      inductive_transfo := inductive_P;
      term_transfo := term_P;
      index_oib := index_P;
      prefix := prefix;
      pmib := pseudo_mib_of_mib mib_P;
      poib := pseudo_oib_of_oib temp_oib_P;
      lctors := map (fun c => Some c) temp_oib_P.(ind_ctors);
      og_poib := og_poib transfo_info;
      og_lctors := og_lctors transfo_info;
      env_quote := env_quote transfo_info;
      modpath_call := (modpath_call transfo_info);
      name_og_inductive := temp_oib_P.(ind_name);
      term_og_inductive := term_P;
      og_inductive := inductive_P;
      isdep := isdep transfo_info;
    |}
  in
  let derec_transfo_P := full_derecursivation_mib transfo_info_P parametres_P telescope_oib_P in
  
  lists <-? form_ref_info
    position_pilot (concat_options (lctors derec_transfo_P))
    (mib_P.(ind_npars)) list_constructors_R
    (length (concat_options (lctors derec_transfo_P))) 0
    poib_R.(pseudo_name) ;;
  let (list_ref_R,list_ref_P) := lists in
  let name_disp := (name_og_inductive transfo_info) ^ "_dispatch" in
  let spec_info :=
    {|
      transfo_info_R := transfo_info;
      
      position_pilot := position_pilot;
      (*The internal structures of the relation*)
      pmib_R := pmib_R;
      poib_R := poib_R;
      lctors_R := list_constructors_R;
      nb_indices_R := nb_indices_R;
      (*The name of the relation*)
      ident_R := poib_R.(pseudo_name);
      
      
      inductive_P := inductive_P;
      nb_params_P := nb_params_P;
      nb_indices_P := length (poib derec_transfo_P).(pseudo_indices);
      parametres_P := parametres_P;
      indices_P := (poib derec_transfo_P).(pseudo_indices);
      list_constructors_P := concat_options (lctors derec_transfo_P) ;
      name_oib_P := temp_oib_P.(ind_name);
      
      (*The reference relation with the index of the pilot constructor as key*)
      list_ref_P := list_ref_P;
      (*The reference relation with the index of the relation constructor as key*)
      list_ref_R := list_ref_R;

      (*The path to the file from where the metacoq call for the small inversion was made.*)
      modpath_call_spec := (modpath_call transfo_info);
      name_dispatch := name_disp;
      transfo_info_spec := transfo_info;
      telescope_oib_P := telescope_oib_P;
      og_transfo_info_P := transfo_info_P;
    |}
  in
  if is_forced then
    check_spec_info_novar spec_info
  else
    check_spec_info spec_info.

Definition data_extraction_specialisation
  (transfo_info : transformation_info) (position_pilot:nat)(is_forced : bool)
  : TemplateMonad (specialisation_info) :=
  tmErrorReturn (data_extraction_spec transfo_info position_pilot is_forced).

Definition print_data_extraction_specialisation{X}(R:X) (position_pilot:nat)(prefix : string)(is_forced : bool) :=
  transfo_info <-- data_extraction R prefix false;;
  spec_info <-- data_extraction_specialisation transfo_info position_pilot is_forced;;
  eval_print spec_info.


(*
Modifies the type telescope of a constructor to change the conclusion.
Removes the pilot argument and adds the new parametres that were the arguments of the constructor of the pilot if any.
 *)
Fixpoint specialize_pilot_index 
  (type_to_modify : term)
  (spec_info : specialisation_info)
  (nb_cons_arg : nat)
  :
  term
  :=

  match type_to_modify with

  | tApp app list_argument =>
      (*Extract the call to the arguments of Kj if any in alpha_kappa*)
      let  appels_args_constr_P :=
        extract_args list_argument ((position_pilot spec_info))
      in
      (*removes alpha_kappa from the conclusion*)
      let args_suppr :=
        remove_index_from_list list_argument ((position_pilot spec_info))
      in
      (*removes the calls to the parameters of P from the extracted arguments*)
      let args_without_params :=
        without_firstn appels_args_constr_P (nb_params_P spec_info)
      in
      (*adds the extracted arguments to the conclusion, at the place of the pilot*)
      let new_args :=
        insert_list_in_list
          args_without_params
          args_suppr
          ((position_pilot spec_info))
      in
      tApp app new_args

  | tProd name type body =>
      tProd name type (specialize_pilot_index body spec_info nb_cons_arg)
  |tLetIn name value type body =>
     tLetIn name value type (specialize_pilot_index body spec_info nb_cons_arg)
  | other_term => other_term
  end.

(*Creates the constructor Ki_Cj for a partial inductive Relation_Cj.*)
Definition partial_inductive_constructor
  (ref_info : reference_info)(list_sigma : list (option term))
  (constructor_P : constructor_body)(new_arity : nat)
  (spec_info : specialisation_info)(is_variable : bool)
  (params_variable : list term)
  (position_variable : nat)
  : constructor_body :=
  let position_constructor_R := index_cons_relation ref_info in
  let constructor_R := cons_relation ref_info in
  let new_name :=
    constructor_R.(cstr_name)^ "_" ^ constructor_P.(cstr_name)
  in
  let let_in_type :=
    if is_variable
    then
      (*Lifts the deBruijn indexes in the type telescope by the number of new indices.
        This only lift after the position of the variable
        that will be swapped for the arguments of its constructors.
       *)
      let lift_type :=
        lift_past_params
          (constructor_P.(cstr_arity))
          (constructor_R.(cstr_type))
          (position_variable) 0
      in
      (*Inserts the sigma substitution of the constructor arguments
    in the type telescope via let_ins*)
      let sigma_type :=
        telescope_to_letin lift_type list_sigma
      in
      let tProd_new_args := rev_context_to_tProd constructor_P.(cstr_args) in
    let letin_params := list_term_to_letin params_variable in
      (*Adds the new parametres to the type*)
      let added_type :=
        insert_tProd_in_type sigma_type (position_variable) tProd_new_args
      in
      added_type
    else
      constructor_R.(cstr_type)
  in
  (*Propagates the change by eliminating let ins*)
  let mod_type :=
    remove_let_in let_in_type []
  in

  (*Adds the instanciated parameters of the partial inductive to the conclusion of the constructor*)
  let new_type :=
    specialize_pilot_index mod_type spec_info constructor_R.(cstr_arity)
  in
  
  let new_args := telescope_to_args new_type 0 new_arity in
  
  let new_indices := telescope_to_indices new_type 0 in

  {|
    cstr_name := new_name;
    cstr_args := new_args;
    cstr_indices :=  new_indices;
    cstr_type :=  new_type;
    cstr_arity :=  new_arity;

  |}
.



Definition info_partial_inductive_constructor
  (ref_info : reference_info)(constructor_P : constructor_body) 
  (spec_info : specialisation_info)
  : constructor_body :=
  let constructor_R := cons_relation ref_info in
  let constr :=
    partial_inductive_constructor
      ref_info [] constructor_P
      constructor_R.(cstr_arity) spec_info false [] 0
  in
  constr.

Definition info_partial_inductive_variable
  (ref_info : reference_info)(de_Bruijn : nat)(params_var:list term)
  (constructor_P : constructor_body) (spec_info : specialisation_info)
  : constructor_body :=

  let position_constructor_P := index_cons_pilot ref_info in
  let constructor_R := cons_relation ref_info in
  let position_variable :=
    constructor_R.(cstr_arity) - (de_Bruijn + 1)
  in
  
  let list_args_P := 
    rev_range_deBruijn constructor_P.(cstr_arity) 0
  in
  
  let term_constructor_P :=
    tApp
      (tConstruct (inductive_P spec_info) position_constructor_P [])
      ((map (lift0 (constructor_P.(cstr_arity))) params_var) ++  list_args_P)
  in
  let list_sigma_params := 
    (fill_None position_variable)++[Some term_constructor_P]
  in
  let new_arity := 
    constructor_R.(cstr_arity) + constructor_P.(cstr_arity) - 1
  in
  let constr :=
    partial_inductive_constructor
      ref_info list_sigma_params constructor_P new_arity spec_info true params_var position_variable
  in
  constr.


Definition create_information_constructor_partial_inductive
  (constructor_P : constructor_body)(og_constructor_P : constructor_body) (spec_info : specialisation_info)
  (ref_info : reference_info)
  : nat * constructor_body :=
  let constructor_R := cons_relation ref_info in
  let index_cons_R := index_cons_relation ref_info in
  
  match reference_pilot ref_info with
  |application position_constructor _ _ =>
     let tProd_new_args := rev_context_to_tProd constructor_P.(cstr_args) in
     let constr :=
       info_partial_inductive_constructor ref_info constructor_P spec_info
     in
     (index_cons_R,constr)
  |variable de_Bruijn _ params =>
     (*Adapts the arguments of the constructor to its parameters*)
     let new_constructor_P := full_derecursivation_constructor (og_transfo_info_P spec_info) params (telescope_oib_P spec_info) og_constructor_P in
     let constr :=
       info_partial_inductive_variable ref_info de_Bruijn params new_constructor_P spec_info
     in
     (index_cons_R,constr)
  end.

Fixpoint interleave_cons_partial
  (lctors : list (option constructor_body))
  (lpartial_cons : list (nat * constructor_body))
  (index_cons : nat)
  : list (option constructor_body) :=
  match lctors with
  |[] => []
  |None::tl =>
     None::(interleave_cons_partial tl lpartial_cons (index_cons + 1))
  |Some _::tl =>
     match lpartial_cons with
     |[] => None::interleave_cons_partial tl lpartial_cons (index_cons + 1)
     |(pos, cstr)::tl_partial =>
        if pos =? index_cons
        then Some cstr :: interleave_cons_partial tl tl_partial (index_cons + 1)
        else None :: interleave_cons_partial tl lpartial_cons (index_cons + 1)
     end
  end.


(*Creation of the mutual_inductive_body of the partial inductive Relation_Dj,
 as well as the branch of the match in the dispatch corresponding to said partial inductive*)
Definition create_partial_inductive
  (spec_info : specialisation_info)(position_constructor_P : nat)
  (constructor_P : constructor_body)(og_constructor_P : constructor_body)
  : transformation_info × branch term × context_decl :=
  
  (*Creation of the insertion function of the new indices that are the arguments of Dj*)
  let term_params := rev_context_to_tProd constructor_P.(cstr_args) in

  (*The deBruijn list corresponding to the indices of Relation_Dj
    that replace the arguments of constructor Dj*)
  let list_args_P := 
    rev_range_deBruijn constructor_P.(cstr_arity) 0
  in
  (*The parameters of inductive Dj that are lifted
    to account for the new parameters that replace the arguments of constructor Dj*)
  let list_params_P := (map (lift0 constructor_P.(cstr_arity)) (parametres_P spec_info)) in

  (*The contructor Dj applied to its altered parameters and arguments*)
  let term_constructor_P :=
    tApp (tConstruct (inductive_P spec_info) position_constructor_P [])
      (list_params_P ++ list_args_P)
  in

  
  (*Lift the indices of the inductive to account for new parameters.*)
  let lift_type :=
    lift_past_params
      (constructor_P.(cstr_arity)) ((poib_R spec_info).(pseudo_type))
      (position_pilot spec_info) 0
  in
  (*Removes the pilot argument from the type telecope by transforming it into a let in*)
  let let_in_type :=
    nth_prod_to_letin
      lift_type
      term_constructor_P
      (position_pilot spec_info)
  in
  (*Propagates the let in*)
  let prop_type :=
    remove_let_in let_in_type []
  in
  (*Adds the new indices*)
  let new_type :=
    insert_tProd_in_type prop_type (position_pilot spec_info) term_params
  in
  
  let new_name := (ident_R spec_info)^"_"^constructor_P.(cstr_name) in
  
  (*Creation of the constructors*)
  let list_constructors :=
    match get_value_from_int_map position_constructor_P (list_ref_P spec_info) with
    |None => []
    |Some list_info_ref =>
       rev_map
         (create_information_constructor_partial_inductive constructor_P og_constructor_P spec_info)
         list_info_ref
    end
  in

  let new_constructors := interleave_cons_partial (lctors_R spec_info) list_constructors 0 in

  (*The contructor Dj applied to its altered parameters and arguments for the dispatch branch,
so taking into account the parameters of Relation*)
  let term_P_dispatch :=
    tApp
      (tConstruct (inductive_P spec_info) position_constructor_P [])
      ((parametres_P spec_info)++
         (rev_range_deBruijn
            (constructor_P.(cstr_arity))
            ( position_pilot spec_info)
         )
      )
      
  in
  (*The letin telescope at the beginning of the dispatch branch.*)
  let lambda_dispatch :=
    prod_to_letin_lambda
      ((poib_R spec_info).(pseudo_type))
      ((list_const
          (tRel
             (constructor_P.(cstr_arity) +
                (position_pilot spec_info) ))
          (position_pilot spec_info))
         ++[term_P_dispatch])
  in

  (*pointers to p*)
  let list_db_params_R := rev_range_deBruijn 0 (nb_indices_R spec_info) in
  (*pointers to a*)
  let list_db_indices_R := rev_range_deBruijn (nb_indices_R spec_info) 0 in
  (*pointers to yj*)
  let list_db_args_cons_P :=
    rev_range_deBruijn
      (constructor_P.(cstr_arity)) (nb_indices_R spec_info)
  in
  (*Removing the pilot index from the pointers to a*)
  let list_db_wo_pilot := remove_index_from_list list_db_indices_R (position_pilot spec_info) in
  (*Replacing it with the yj*)
  let list_db_new_indices :=
    insert_list_in_list list_db_args_cons_P list_db_wo_pilot (position_pilot spec_info)
  in
  let deBruijn_app_dispatch := list_db_params_R ++ list_db_new_indices in
  
  let new_indices :=
    telescope_to_args new_type 0 (nb_indices_R spec_info + (length constructor_P.(cstr_args)) -1)
  in
  let new_pmib := pmib_R spec_info in
  let new_poib :=
    {|
      pseudo_name := new_name;
      pseudo_indices := new_indices;
      pseudo_sort := (poib_R spec_info).(pseudo_sort);
      pseudo_type :=  new_type;
      pseudo_kelim := (poib_R spec_info).(pseudo_kelim);
      pseudo_projs := (poib_R spec_info).(pseudo_projs);
      pseudo_relevance := (poib_R spec_info).(pseudo_relevance)
    |}
  in
  let new_transfo_info :=
    recreate_transfo_info (transfo_info_spec spec_info) new_pmib new_poib new_constructors
  in
  (*mib of the partial inductive*)
  (new_transfo_info,
    ((
        (*branch term of the dispatch*)
        {|
          bcontext := map (fun decl => decl.(decl_name)) constructor_P.(cstr_args);
          bbody := remove_let_in (
                       lambda_dispatch(
                           tApp
                             (tVar ("_"^new_name))
                             (deBruijn_app_dispatch))) []
        |}
      ),
      vass (string_to_aname ("_"^new_name)) new_type)
  ).


(*Create the lambda term of the dispatch.*)
Definition create_dispatch_term
  (spec_info : specialisation_info)(cases : list (branch term))(sub_inductives : context)
  : term :=

  (*Lifts the type telescope to compensate for putting the end of the telescope
    after the pilot index in the return clause of the dispatch *)
  let lift_type := lift0 (2+(position_pilot spec_info)) (poib_R spec_info).(pseudo_type) in

  (*Sépare l'avant et l'après pilote*)
  let let_in_type :=
    prod_to_letin lift_type
      ((list_const (tRel ((position_pilot spec_info) + 1)) (position_pilot spec_info))
         ++[tRel (position_pilot spec_info)]) in
  let return_type :=
    remove_let_in let_in_type [] in
  
  (*The lambda terms of the indexes of the Relation up to the pilot index*)
  let lambda_indices :=
    first_n_tProds_into_lambda  (poib_R spec_info).(pseudo_type) ((position_pilot spec_info) + 1)
  in
  let body_dispatch :=
    lambda_indices (
        tCase
          {|
            ci_ind := inductive_P spec_info;
            ci_npar := length (parametres_P spec_info);
            ci_relevance := Relevant
          |}
          {|
            puinst := [];
            pparams := map (lift0 1) (parametres_P spec_info);
            pcontext := [nameAnon];
            preturn :=  return_type;
          |}
          (*The reference to the pilot index variable, which is the one the case analysis is on.*)
          (tRel 0)
          cases
      ) in

  let dispatch_term :=
    append_context_vars_lambda (env_quote (transfo_info_R spec_info)) sub_inductives body_dispatch
  in
  dispatch_term.



Fixpoint get_correct_constructor
  (index_cons_R : nat) (list_inv_pilot : list reference_info)
  (list_cons : list term) : ErrorMonad term :=
  match list_inv_pilot, list_cons with
  |[],[] => Error "No correct constructor found"
  |hinv::tinv, hcons::tcons => if hinv.(index_cons_relation) =? index_cons_R
                            then Success hcons
                            else get_correct_constructor index_cons_R tinv tcons
  |_,_ => Error "Lists of inversion infos not of same size"
  end.


Definition change_type_call_constr
  (spec_info : specialisation_info)
  (type : term)
  (position_variable : nat)
  (cons_pilot : constructor_body)
  (og_cons_pilot : constructor_body)
  (index_cons_pilot : nat)
  (call_disp  : term)
  (reference_pilot : ref_pilot):=
  let args_cons := rev_range_deBruijn (length cons_pilot.(cstr_args)) 0 in
  let '(params_cons, args_pilot) :=
    match reference_pilot with
    |application _ _ _ => (cons_pilot.(cstr_indices), rev_context_to_tProd cons_pilot.(cstr_args))
    |variable deBruijn_variable _ params =>
       (*let cons_param_P := full_derecursivation_constructor' (params) cons_pilot in*)
       let cons_param_P := full_derecursivation_constructor (og_transfo_info_P spec_info) params (telescope_oib_P spec_info) og_cons_pilot in
       ((map (lift0 (length args_cons)) params), rev_context_to_tProd cons_param_P.(cstr_args))
    end
  in
  let subst_pilot :=
    tApp
      (tConstruct (inductive_P spec_info) index_cons_pilot [])
      (params_cons
      ++ args_cons)
  in
  let end_type :=
    nth_prod_to_letin type subst_pilot position_variable
  in
  let var_type := var_inductive end_type call_disp in
  (*Lift by the number of new indices, the +1 and 1 are to avoid the let in we just put in*)
  let lift_type := lift_past_params (length cons_pilot.(cstr_args)) var_type (S position_variable) 1 in
  let let_in_type := insert_tProd_in_type lift_type position_variable args_pilot in
  let new_type := remove_let_in let_in_type [] in
  new_type.

Fixpoint create_cases_submatch
  (list_inv_info : list reference_info)
  (spec_info : specialisation_info)
  (position_variable : nat)
  (deBruijn_variable : nat)
  (list_params : list term)
  (call_disp  : term)
  : ErrorMonad (list (branch term) * context) :=
  match list_inv_info with
  |[] => Success ([],[])
  |inv_info :: t_inv_info =>
     
     list_inv_info_pilot <-?
       get_value_from_int_map_err (index_cons_pilot inv_info) (list_ref_P spec_info)
     ;;
     
     let constr_name := ("_"^ (cons_relation inv_info).(cstr_name)^"_"^ (cons_pilot inv_info).(cstr_name)) in
     let constr := tVar constr_name in
     og_cons_pilot <-? (nth_err (concat_options (lctors (og_transfo_info_P spec_info))) (index_cons_pilot inv_info));;
     let decl_constr :=
       let temp_type :=
         change_type_call_constr
           spec_info
           ((cons_relation inv_info).(cstr_type))
           position_variable
           (cons_pilot inv_info)
           og_cons_pilot
           (index_cons_pilot inv_info)
           call_disp
           (reference_pilot inv_info)
       in
       vass (string_to_aname constr_name) temp_type
     in
     '(list_branch, list_ctx_cons) <-?
       create_cases_submatch
       t_inv_info
       spec_info
       position_variable
       deBruijn_variable
       list_params
       call_disp
     ;;
     
     let arity_cons_pilot := (cons_pilot inv_info).(cstr_arity) in
     let nb_args_R_after_variable :=
       (cons_relation inv_info).(cstr_arity) - (position_variable + 1)
     in
     
     let dB_args_R_after_variable := rev_range_deBruijn nb_args_R_after_variable 0 in
     let dB_args_R_before_variable :=
       rev_range_deBruijn
         position_variable
         ((cons_relation inv_info).(cstr_arity) - position_variable)
     in
     let dB_args_cons :=
       rev_range_deBruijn arity_cons_pilot (cons_relation inv_info).(cstr_arity)
     in
     let dB_args :=
       dB_args_R_before_variable ++ dB_args_cons ++ dB_args_R_after_variable
     in

     let args_R_after_variable :=
       firstn nb_args_R_after_variable (cons_relation inv_info).(cstr_args)
     in
     let lambda_args_R_after_variable :=
       rev_params_into_lambdas args_R_after_variable
     in
     let dB_letin_args_R_before_variable :=
       list_const
         (tRel ((cons_relation inv_info).(cstr_arity) + arity_cons_pilot - 1))
         position_variable
     in
     let letin_args_R_before_variable :=
       context_to_letin
         (rev (cons_relation inv_info).(cstr_args))
         dB_letin_args_R_before_variable
     in

     let db_args_variable := rev_range_deBruijn arity_cons_pilot position_variable in
     let call_cons_variable :=
       tApp
         (tConstruct (inductive_P spec_info) (index_cons_pilot inv_info) [])
         ((*(map (lift0 (1 + deBruijn_variable)) list_params )*) list_params ++ db_args_variable)
     in
     decl_variable <-? nth_err (rev (cons_relation inv_info).(cstr_args)) position_variable;;
     let letin_variable :=
       fun x =>
         tLetIn decl_variable.(decl_name) call_cons_variable decl_variable.(decl_type) x
     in
     
     let case_term :=
       letin_args_R_before_variable
         (letin_variable (lambda_args_R_after_variable (tApp constr dB_args)))
     in
     let case_body := remove_let_in case_term [] in
     Success ({|
           bcontext := create_anon_context (cons_pilot inv_info).(cstr_arity);
           bbody := case_body
         |}::list_branch,
      decl_constr ::list_ctx_cons)
  end.

Definition create_inversion_submatch
  (spec_info : specialisation_info)
  (deBruijn_variable : nat) (position_variable : nat)
  (list_params : list term)
  (constructor_R : constructor_body)(index_cons_R : nat)
  (list_inv_info : list reference_info)
  : ErrorMonad term :=


  let name_disp := (poib_R spec_info).(pseudo_name) in
  let decl_disp := vass (string_to_aname ( name_disp)) (poib_R spec_info).(pseudo_type) in
  
  
  let rev_args := rev constructor_R.(cstr_args) in
  
  (**The return clause of the match*)

  let call_dispatch := (tVar ("_" ^ name_disp)) in
  
  (*DeBruijns for x(i,k>θ)*)
  let deBruijn_args_after_variable := rev_range_deBruijn deBruijn_variable 0 in
  (*∀ x(i,k>θ)*)
  let prod_args_after_variable := 
    context_to_tProd (without_firstn rev_args (position_variable + 1))
  in
  (*DeBruijns for x(i,k<θ)*)
  let deBruijn_args_before_variable :=
    list_const (tRel (constructor_R.(cstr_arity))) position_variable
  in
  (*DeBruijn for xθ*)
  let deBruijn_variable_match := tRel position_variable in
  let deBruijns_for_let_in := deBruijn_args_before_variable ++ [deBruijn_variable_match] in
  (*let x(i,k<θ)' := x(i,k<θ) in let x(i,θ)' := xθ in ...*)
  let let_in_args_before_variable :=
    context_into_letin (firstn (position_variable + 1) rev_args) deBruijns_for_let_in
  in
  let list_lifted_params := map (lift0 (deBruijn_variable + 1)) list_params in
  let concl_return :=
    tApp call_dispatch (constructor_R.(cstr_indices))
  in
  let full_return := let_in_args_before_variable ( prod_args_after_variable ( concl_return ) ) in
  let match_return := remove_let_in full_return [] in

  (**The lambdas before the match and dB after variable*)

  let lambdas_args := params_into_lambdas rev_args in
  let nb_args_R_after_variable := deBruijn_variable in
  let dB_after_variable := rev_range_deBruijn  nb_args_R_after_variable 0 in
  
  '(cases_submatch, ctx_cons) <-?
    create_cases_submatch list_inv_info spec_info position_variable deBruijn_variable list_params call_dispatch
  ;;
  let ctx_beginning :=
    (rev ctx_cons)++(name_context [decl_disp] 0)
  in
  (*TODO : will break*)
  let params_match_in :=
     map (lift0 (1 + deBruijn_variable)) list_params
  in
  
  let case_body := tCase
                     {|
                       ci_ind := inductive_P spec_info;
                       ci_npar := nb_params_P spec_info;
                       ci_relevance := Relevant
                     |}
                     {|
                       puinst := [];
                       pparams := params_match_in;
                       pcontext := [nameAnon];
                       preturn := match_return
                     |}
                     (tRel deBruijn_variable)
                     cases_submatch
  in
  let case_term := lambdas_args (tApp case_body dB_after_variable)  in
  let inv_term :=
    append_context_vars_lambda (env_quote (transfo_info_R spec_info)) ctx_beginning case_term
  in
  Success inv_term.


Fixpoint create_inversion_objects
  (spec_info : specialisation_info) (index_constr_R : nat) (list_constr_R : list (option constructor_body))
  : ErrorMonad (list (option term)) :=
  
  match list_constr_R with
  |[] => Success []
  |None :: t_constr_R =>
     tl <-? create_inversion_objects spec_info (index_constr_R + 1) t_constr_R;;
     Success (None :: tl)
  |Some constr_R :: t_constr_R =>
     let opt_infos_constr_R :=
       get_value_from_int_map index_constr_R (list_ref_R spec_info)
     in
     
     match opt_infos_constr_R with
     |None =>
        Error (
            "small_inv.create_inversion_cases : Anomaly : constructor "
            ^(string_of_nat index_constr_R)
            ^" of R was not inverted")
     |Some list_ref_relation =>
        
        match list_ref_relation with
        |[] => Success []
        |ref_pilot :: _ =>
           list_tail_objects <-?
             create_inversion_objects spec_info (index_constr_R + 1) t_constr_R 
           ;;
           
           match (reference_pilot ref_pilot) with
             
           |application nb_cons list_params list_args =>

              list_inv_info_pilot <-? get_value_from_int_map_err nb_cons (list_ref_P spec_info);;
              let name_disp := (poib_R spec_info).(pseudo_name) in
              let decl_disp :=
                vass
                  (string_to_aname name_disp)
                  (poib_R spec_info).(pseudo_type)
              in
              let cons_type :=
              var_inductive constr_R.(cstr_type) (tVar ("_" ^ name_disp)) 
              in
              let cons_name :=
                ("_"^ (cons_relation ref_pilot).(cstr_name)^"_"^ (cons_pilot ref_pilot).(cstr_name))
              in
              let decl_cons :=
                vass (string_to_aname cons_name) cons_type
              in
              let constr :=
                tVar cons_name
              in
              let context_constr := decl_cons::(name_context [decl_disp] 0) in
              
              let lambda_args := rev_params_into_lambdas constr_R.(cstr_args) in
              let debruijn_indexes := rev_range_deBruijn (length constr_R.(cstr_args)) 0 in
              let cons_body := (lambda_args (tApp constr debruijn_indexes)) in
              let proxy_adapter_cons :=
                append_context_vars_lambda
                  (env_quote (transfo_info_R spec_info))
                  context_constr cons_body
              in
              Success ((Some proxy_adapter_cons) ::list_tail_objects)

           |variable de_Bruijn position_variable list_params =>

              inversion_submatch <-? create_inversion_submatch
                spec_info de_Bruijn position_variable list_params
                constr_R index_constr_R (rev list_ref_relation)
              ;;
              Success ( (Some inversion_submatch) ::list_tail_objects)
           end
        end
     end
  end.

Definition transfo_specialisation

  (*If the pilot has the form of a variable in all constructor,
    does the specialisation still happen (true)
    or does it returns an error (false)?*)
  (is_forced : bool)
  (position_pilot : nat) : transfo :=
  fun transfo_info =>
    spec_info <-? data_extraction_spec transfo_info position_pilot is_forced;;
    let (list_transfo,list_dispatch_cases_context) :=
      split (
          map2i
            (fun position_constructor_P constructor_P og_constructor_P =>
               create_partial_inductive spec_info position_constructor_P  constructor_P og_constructor_P
            )
            (list_constructors_P spec_info) (concat_options (lctors (og_transfo_info_P spec_info)))
        )
    in
    let (list_dispatch_cases, dispatch_context) := split list_dispatch_cases_context in
    let proxy_type_adapter :=
      create_dispatch_term spec_info list_dispatch_cases (rev dispatch_context)
    in
    
    new_end_constructors <-? create_inversion_objects spec_info 0  (lctors transfo_info) ;;

    Success ((proxy_type_adapter,new_end_constructors ), list_transfo, fun l => l).
