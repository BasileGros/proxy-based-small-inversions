From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import error_monad.
From utils Require Import list_functions.
From utils Require Import db_manipulation.

Notation nameAnon := {| binder_name := nAnon; binder_relevance := Relevant |}.

(*Extracts the list of indices
from the conclusion of a constructor's type telescope*)
Fixpoint telescope_to_indices (t:term) (nb_args : nat) : list term :=
  match t with
  | tProd _ _ cont => telescope_to_indices cont nb_args
  | tLambda _ _ cont => telescope_to_indices cont nb_args
  | tLetIn _ _ _ cont  => telescope_to_indices cont nb_args
  | tApp _ l => without_firstn l nb_args
  | _ => []
  end.

Fixpoint insert_new_concl_telescope (t:term) (new_concl : list term) : term :=
  match t with
  | tProd na t cont => tProd na t (insert_new_concl_telescope cont new_concl)
  | tLambda na t cont => tLambda na t (insert_new_concl_telescope cont new_concl)
  | tLetIn na t v cont  => tLetIn na t v (insert_new_concl_telescope cont new_concl)
  | tApp t _ => tApp t new_concl
  | _ => t
  end.

Fixpoint add_to_concl_telescope (t:term) (new_concl : list term) : term :=
  match t with
  | tProd na t cont => tProd na t (add_to_concl_telescope cont new_concl)
  | tLambda na t cont => tLambda na t (add_to_concl_telescope cont new_concl)
  | tLetIn na t v cont  => tLetIn na t v (add_to_concl_telescope cont new_concl)
  | tApp t l => tApp t (l++new_concl)
  | _ => t
  end.



(*Removes the first n elements in a type telescope*)
Fixpoint peel_telescope (t:term) (n:nat) : term :=
  match t,n with
  | _, 0 => t
  | tProd _ _ cont, S m => peel_telescope cont m
  | tLambda _ _ cont, S m => peel_telescope cont m
  | tLetIn _ _ _ cont, S m => peel_telescope cont m
  | x, _ => x
  end.

Fixpoint cut_telescope (t:term) (n:nat) : (term -> term) * term :=
  match t,n with
  | _, 0 => (fun x => x, t)
  | tProd na t cont, S m =>
      let (fun_cont, cut_part) := cut_telescope cont m in
     ( fun x => tProd na t (fun_cont x), cut_part)
  | tLambda na t cont, S m =>
      let (fun_cont, cut_part) := cut_telescope cont m in
     ( fun x => tLambda na t (fun_cont x), cut_part)
  | tLetIn na t v cont, S m =>
      let (fun_cont, cut_part) := cut_telescope cont m in
     ( fun x => tLetIn na t v (fun_cont x), cut_part)
  | _, _ => (fun x => x, t)
  end.

Fixpoint aux_telescope_to_args
  (telescope : term) (nb_args : nat) (acc : context)
  : context :=

  match telescope,nb_args with
  |_, 0 => acc
  |tProd name type cont, S m => let decl := {| decl_name := name;
                                             decl_body := None;
                                             decl_type := type
                                           |} in
                               aux_telescope_to_args cont m (decl::acc)
  |_ , _ => acc
  end.

Definition telescope_to_args
  (telescope : term) (nb_params : nat) (nb_args : nat)
  : context :=
  let peeled_telescope := peel_telescope telescope nb_params in
  aux_telescope_to_args peeled_telescope nb_args [].



(*Like prod_to_letin but options allow for holes.*)
Fixpoint telescope_to_letin
  (telescope:term) (substitution : list (option term))
  : term :=
  match telescope, substitution with
  |t, [] => t
  |tProd name type body, None::q =>
     tProd name type (telescope_to_letin body q)
  |tProd name type body, (Some def)::q =>
     tLetIn name def type (telescope_to_letin body q)
  |t, _ => t
  end.


(*Does a destInd, but wrapped with the ErrorMonad monad instead of the option monad.*)
Definition inductive_from_term (inductive_term:term): ErrorMonad inductive :=
  
  match destInd inductive_term with
  | Some (extraction_inductive, _) => Success extraction_inductive
  |None => Error "The term given was not a tInd."
  end.

(*Returns the one_inductive_body of a mutual_inductive_body
corresponding to the index.
 *)
Definition one_inductive_body_from_mib (mib : mutual_inductive_body) (index:nat)
  : ErrorMonad one_inductive_body :=
  
  match (nth_error (mib.(ind_bodies)) index) with
  |Some oib => Success oib
  | None =>
      Error ("The oib indexed at " ^ (string_of_nat index) ^ " does not exist.")
  end.


Definition create_telescope_letin_mutual_inductive
  (ind:inductive)(nb_oib:nat)
  : term -> term :=
  let dummy_type := tSort (sType (Universe.make' Level.lzero)) in
  let f :=
    (fix f (decr : nat) (incr : nat) :=
       match decr with
       |0 => fun x => x
       |S n =>
          fun x =>
            tLetIn
              nameAnon
              (tInd {|inductive_mind := ind.(inductive_mind); inductive_ind := incr|} [])
              dummy_type (f n (1 + incr) x)
       end)
  in f nb_oib 0.

Fixpoint create_ctx_mutual_oibs
  (loibs : list one_inductive_body)(acc : context)
  : context :=
  match loibs with
  |[] => acc
  |oib::tl =>
     let decl :=
       {| decl_name := string_to_aname oib.(ind_name); decl_body := None; decl_type := oib.(ind_type) |}
     in
     create_ctx_mutual_oibs tl (decl::acc)
  end.

Definition create_context_mutual_oibs 
  (loibs : list one_inductive_body)
  : context :=
  create_ctx_mutual_oibs loibs [].


(*Call the above created insertion function at the nth position of a tProd chain *)
Fixpoint insert_tProd_in_type
  (term_insert_in:term) (offset:nat) (insertion:term -> term) : term :=
  
  match term_insert_in,offset with
  |_ , 0               => insertion term_insert_in
  |tProd n t body, S m => tProd n t (insert_tProd_in_type body m insertion)
  |tLetIn n val t body, S m => tLetIn n val t (insert_tProd_in_type body m insertion)                           
  |other_term, _      => insertion other_term
  end.

(*Takes a call to arguments and gives the arguments it was called on*)
Definition extract_args (list_arguments : list term) (position_pilote : nat) : list term :=
  match nth_error list_arguments position_pilote with
  |None => []
  |Some term_pilot => match term_pilot with
                     |tApp _ list_app => list_app
                     |_ => []
                     end
  end.




(*Gives back a list of None option terms*)
Fixpoint fill_None (nb_params : nat) : list (option term) :=
  match nb_params with
  |0 => []
  |S n => None :: (fill_None n)
  end.



(*Transforms a context into a function that inserts the corresponding tProd chain before the term given in its argument.*)
Fixpoint context_to_tProd (c:context) : term -> term :=
  match c with
  |[]      => (fun term_body => term_body)
  | decl::t => (fun term_body => tProd decl.(decl_name)  decl.(decl_type) (context_to_tProd t term_body ))
  end.


(*Does the same but in reverse order of the context.*)
Definition rev_context_to_tProd (c:context) : term -> term :=
  fun x => fold_left (fun term_cont decl => tProd decl.(decl_name)  decl.(decl_type) term_cont) c x.

(*
Transforms the nth tProd of a tProd chain into a tLetIn witht the given value
 *)
Fixpoint nth_prod_to_letin 
  (term_a_modifier:term)
  (valeur : term)
  (n:nat)
  :
  term
  :=

  match term_a_modifier,n with
  |tProd nom type continuation, 0 =>
     tLetIn nom valeur type continuation

  |tProd nom type continuation, S m =>
     tProd nom type (nth_prod_to_letin continuation valeur m)

  |terme_autre,_=> terme_autre
  end
.


(*Transforms a telescope of TProds into either tLetIns or tLambdas
 depending if there are values for it.*)
Fixpoint prod_to_letin_lambda
  (type:term) (list_letin : list term)
  : term -> term :=
  match type,list_letin with
  |tProd name type body,[] =>
     fun x =>
       tLambda name type (prod_to_letin_lambda body [] x)
  |tProd name type body, value::t =>
     fun x =>
       tLetIn name value  type (prod_to_letin_lambda body t x)
  |_,_ => fun x => x
  end.



(*Extracts inductives or application of inductives.*)
Definition app_inductive_from_term
  (inductive_term:term)
  : ErrorMonad (inductive*list term*term) :=
  
  match inductive_term with
  | tInd extraction_inductive l =>
      Success (extraction_inductive, [],tInd extraction_inductive l)
  | tApp (tInd extraction_inductive l) list_args =>
      Success (extraction_inductive, list_args, (tInd extraction_inductive l))
  |_=> Error "The term given was not a tInd or a tApp of a tInd."
  end.


(*Does the same as the precedent, but with a coq environment passed along*)
Definition mib_index_from_env
  (inductive_term:term) (env : global_env)
  : ErrorMonad (mutual_inductive_body × nat) :=
  match inductive_from_term inductive_term with
  |Error message => Error message
  | Success extraction_inductive =>
      let index := inductive_ind extraction_inductive in
      
      let kername := inductive_mind extraction_inductive in
      match lookup_mind_decl kername env.(declarations) with
      |None =>
         Error ("Pilot inductive " ^ (string_of_kername kername) ^
                  " not found in environment")
      | Some mib => Success (mib, index)
      end
  end.

(*
Transforms a chain of tProds into tLetIns with the values given
 *)
Fixpoint prod_to_letin 
  (term_a_modifier:term)
  (valeurs : list term)
  :
  term
  :=

  match term_a_modifier, valeurs with
  |_,[] => term_a_modifier

  |tProd nom type body, t::q => tLetIn nom t type (prod_to_letin body q)

  |terme_autre,_=> terme_autre
  end.

(*Tranforms a list of parameters into a telescope of lambda term
but in reverse order of the list *)
Definition rev_params_into_lambdas (list_params : context) := 
  fun x =>
    fold_left
      (fun term_cont decl =>  tLambda decl.(decl_name) decl.(decl_type) term_cont)
      list_params x.

Fixpoint context_to_letin (c : context) (l : list term) :=
  match c, l with
  |[],_ => fun x => x
  |_, [] => fun x => x
  |decl::tc, val::tl =>
     fun x =>
       tLetIn decl.(decl_name) val decl.(decl_type) (context_to_letin tc tl x)
  end.

(*Transforms the first nth elements of a tProd telescope into lambda terms.*)
Fixpoint first_n_tProds_into_lambda (t:term) (nb_keep:nat) : term -> term :=
  match t,nb_keep with
  |_,0 => fun x => x
  |tProd name type body,S n =>
     fun x =>
       tLambda name type (first_n_tProds_into_lambda body n x)
  |_,_ => fun x => x
  end.

(*Does the same thing but for a list of parameters*)
Fixpoint context_into_letin
  (list_params : context) (list_values : list term)
  : term -> term :=
  match list_params, list_values with
  |[], _ => fun x => x
  |_, [] => fun x => x
  |decl::t,val::t_val =>
     fun x =>
       tLetIn decl.(decl_name) val decl.(decl_type) (context_into_letin t t_val x)
  end
.


Fixpoint create_anon_context (n:nat) : list aname :=
  match n with
  |0 => []
  |S m => nameAnon::(create_anon_context m)
  end.

Definition merge_option{A}(o1 o2 : option A) : option A :=
  match o1, o2 with
  |Some a, _ => Some a
  |_, Some a => Some a
  |None, None => None
  end.

Definition map2_def{A B C: Type}
  (f : B -> B -> C) (g1 : A -> B) (g2 : A -> B) (d : def A) : C :=
  f (g1(dtype d)) (g2 (dbody d)).

  
(*Lifts the final call to the inductive in a constructor's type
telescope by quantity.*)
Fixpoint lift_inductive (telescope:term) (quantity:nat) : term :=
  match telescope with
  |tProd name type body =>
     tProd name type (lift_inductive body quantity)
  |tLetIn name value type body =>
     tLetIn name value type (lift_inductive body quantity)
  |tApp app list_app =>
     tApp (lift0 quantity app) list_app
  |tRel n => (lift0 quantity (tRel n))
  |t => t
  end.


Definition rename_cstr (prefix : string)(suffix: string)(cstr : constructor_body) :=
  {|
    cstr_name :=  prefix ^ cstr.(cstr_name) ^ suffix;
    cstr_args := cstr.(cstr_args); 
    cstr_indices := cstr.(cstr_indices);
    cstr_type := cstr.(cstr_type);
    cstr_arity := cstr.(cstr_arity)
  |}.


Definition rename_kername (prefix : string)(suffix : string)(ker : kername)
  : kername :=
  let (modp, id) := ker in
  (modp, prefix ^ id ^suffix).

Definition rename_inductive (prefix : string)(suffix : string)(ind : inductive)
  : inductive :=
  {|
    inductive_mind := rename_kername prefix suffix ind.(inductive_mind);
    inductive_ind := ind.(inductive_ind)
  |}.

(*Change a prod into a letin at the position given.*)
Fixpoint insert_letin_position
  (telescope : term)
  (position : nat)
  (dB : nat)(depth : nat)
  : term := 
  match telescope with
  |tProd na t b =>
        if depth =? position
        then tLetIn na (tRel dB) t
               (insert_letin_position
                  b position (dB) (S depth)
               )
        else tProd na t
               (insert_letin_position
                  b position (S dB) (S depth)
               )

  |tLetIn na v t b => tLetIn na v t (insert_letin_position
                  b position (S dB) (S depth)
               )
  |_ => telescope
  end.

Fixpoint insert_list_letin_position
  (telescope : term)
  (list_position : list nat)
  (len_list : nat) (pos_param:nat)
  :=
  match list_position with
  | [] => telescope
  | hd::tl =>
      let new_tel :=
        insert_letin_position telescope hd (len_list - pos_param - 1) 0
      in
      insert_list_letin_position new_tel tl len_list (S pos_param)
  end.

Definition insertion_list_letin_position
  (telescope : term)
  (list_position : list nat) :=
  insert_list_letin_position telescope list_position (length list_position) 0.

Fixpoint list_term_to_letin (l : list term) :=
  match l with
  | [] => fun x => x
  | val::tl =>
     fun x =>
       tLetIn nameAnon val (tVar "dummy_type") (list_term_to_letin tl x)
  end.
