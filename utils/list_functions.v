(** Functions manipulation Rocq lists*)
From MetaRocq.Utils Require Import utils.
From utils Require Import error_monad.

(*Removes the first n elenments of a list.
So up to and not including element of index n*)
Fixpoint without_firstn{A} (l : list A) (n:nat) : list A  :=
  match l,n with
  |t,0 => t
  |[],_ => []
  |t::q, S m => without_firstn q m
  end.


(*Separates the list into 2 at element n.
The element of index n will be in the second list.*)
Fixpoint firstn_lastn{A} (l : list A) (n:nat) : list A * list A  :=
  match l,n with
  |_,0 => ([],l)
  |[],_ => ([],[])
  |t::q, S m => let (lfirst,llast) :=  firstn_lastn q m in
              (t::lfirst,llast)
  end.

(*Creates a list filled witht the value given*)
Fixpoint list_const{A} (const:A) (n:nat) : list A :=
  match n with
  |O => []
  |S m => const::(list_const const m)
  end.

(*Separates in two a list of couples nested in the ErrorMonad*)
Fixpoint unzip_err {A B}
  (l:list (ErrorMonad(A × B))) (accA : list A) (accB : list B)
  : ErrorMonad (list A × list B) :=
  match l with
  |[] => Success (rev accA,rev accB)
  | (Error message)::tl => Error message
  |(Success (a,b))::tl =>
     unzip_err tl (a::accA) (b::accB)
  end.

(*Same but for the option monad*)
Fixpoint unfold_option {A} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  |a :: q =>
     match a with
     |None => None
     |Some a' =>
        match unfold_option q with
        |None => None
        |Some t => Some (a'::t)
        end
     end
  end.


(*List map3 but with the ErrorMonad*)
Fixpoint map3_err_option {A B C D}
  (fABC : A -> B -> C -> ErrorMonad (option D)) (lA: list (option A)) (lB: list (option B)) (lC : list C)
  : ErrorMonad (list (option D)) :=
  match lA,lB,lC with
  | [],[],[] => Success []
  | (Some a) :: qa,(Some b)::qb,c::qc =>
      d <-? fABC a b c;;
      lD <-? map3_err_option fABC qa qb qc;;
      Success (d::lD)
  | None :: qa,None::qb,_ =>
      lD <-? map3_err_option fABC qa qb lC;;
      Success (None::lD)
  | None :: _ , (Some _)::_ , _ => Error "Error on list synchro in map3_err_option : None Some"
  | (Some _) :: _ , None::_ , _ => Error "Error on list synchro in map3_err_option : Some None"
  | _,[],[] => Error "Size mismatch on first list of map3 : too long"
  | [],_,[] => Error "Size mismatch on second list of map3 : too long"
  | [],[],_ => Error "Size mismatch on third list of map3 : too long"
  | [],_,_ => Error "Size mismatch on first list of map3 : too short"
  | _,[],_ => Error "Size mismatch on second list of map3 : too short"
  | _,_,[] => Error "Size mismatch on third list of map3 : too short"
                   
  end.

(*nth_error but with the ErrorMonad*)
Definition nth_err{A}  (l:list A)(n:nat) : ErrorMonad A :=
  match nth_error l n with
  |None => Error "list too short"
  |Some a => Success a
  end.


(*Removes the nth element of a list and returns it*)
Fixpoint remove_and_return_index_from_list{X} (l:list X) (n:nat) :=
  match l,n with
  | [], _ => ([], None)
  | t::q,O => (q, Some t)
  | t::q, S m =>
      let (q2, result) := remove_and_return_index_from_list q m in
      (t::q2, result)
  end.

Fixpoint unlift_list_nat (l : list nat) (v:nat) (threshold : nat) :=
  match l with
  |[] => []
  |t::q =>
     if Nat.leb threshold t
     then
       (t - v)::(unlift_list_nat q v threshold)
     else
       t::(unlift_list_nat q v threshold)
  end.

Fixpoint separate_list{X : Type}
  (lists : (list X) * (list (option X)))(list_ind : list nat) (fuel : nat) :=
  match list_ind, fuel with
  |_, 0 => lists
  |[],_ => lists
  |tind :: qind, S new_fuel =>
     let (list_to_remove, list_acc) := lists in
     let (list_left, opt_removed) :=
       remove_and_return_index_from_list list_to_remove tind
     in
     let new_qind := unlift_list_nat qind 1 tind in
     separate_list (list_left, opt_removed::list_acc) new_qind new_fuel
  end.
  
(*Removes the nth element of a list*)
Definition remove_index_from_list{X} (l:list X) (n:nat) : list X :=
  let (l_result,_) := remove_and_return_index_from_list l n in l_result.

(*Insert a list at the nth index of an other list*)
Fixpoint insert_list_in_list{A}
  (list_to_insert:list A) (list_where_insert:list A) (offset:nat)
  : list A :=
  match list_where_insert, offset with
  |[], _ => list_to_insert
  |t::q, 0 => list_to_insert ++ (t::q)
  |t::q, S m => t::(insert_list_in_list list_to_insert q m)
  end.


(** Functions for a map structure with integer key*)

(*In a map of elements of a index by integers, add elements to the key given.*)
Fixpoint aux_merge_in_map{A}
  (key:nat) (values : list A)
  (map_to_merge : list (nat * list A))
  (acc:list (nat * list A))
  : list (nat * list A) :=
  match map_to_merge with
  |[] => (key, values)::acc
  | (key_h,values_h)::map_t =>
      if key =? key_h
      then
        ((key_h,values++values_h)::map_t)++acc
      else
        aux_merge_in_map key values map_t ((key_h,values_h)::acc)
  end.

Definition merge_in_map{A}
  (key:nat) (values : list A)
  (map_to_merge : list (nat * list A))
  : list (nat * list A) :=
  aux_merge_in_map key values map_to_merge [].

(*In a map of elements of a index by integers, gets elements for the given key.*)
Fixpoint get_value_from_int_map{A} (key:nat) (l : list (nat * A)) : option A :=
  match l with
  |[] => None
  |(key_h,value_h)::tl =>
     if key =? key_h
     then Some value_h
     else get_value_from_int_map key tl
  end.

(*In a map of elements of a index by integers, gets elements for the given key.*)
Fixpoint get_value_from_int_map_err{A} (key:nat) (l : list (nat * A)) : ErrorMonad A :=
  match l with
  |[] => Error "key not present"
  |(key_h,value_h)::tl =>
     if key =? key_h
     then Success value_h
     else get_value_from_int_map_err key tl
  end.

(*In a map of elements of a index by integers, gets elements for the given key.*)
Fixpoint get_all_from_int_map{A} (key:nat) (l : list (nat * A)) : list A :=
  match l with
  |[] => []
  |(key_h,value_h)::tl =>
     let cont := get_all_from_int_map key tl in
     if key =? key_h then value_h::cont else cont
  end.


Fixpoint sorting_insert (n:nat) (l:list nat) :=
  match l with
  |[] => [n]
  |h::t => if n<? h then h::(sorting_insert n t) else n::h::t
  end.

Fixpoint get_vertical_slice
  (l : list (list nat)) (acc:list nat) (lacc : list (list nat))
   : list nat × list (list nat) :=
  match l with
  |[] => (acc, lacc)
  |[]::t => (acc, lacc)
  |(h1::t1)::t2 =>
     let new_acc := (*sorting_insert h1 acc*) h1::acc in
     get_vertical_slice t2 new_acc (t1::lacc)
  end.

Fixpoint get_vertical_slices
  (l : list (list nat)) (nb_sublists : nat)
  : list (list nat) :=
  match nb_sublists with
  |0 => []
  |S n => let (slice,leftover_l) := get_vertical_slice l [] [] in
         slice::(get_vertical_slices leftover_l n)
  end.

(*Removes options from a list of objects but deletion of the None*)
Fixpoint concat_options{A} (l : list (option A)) : list A :=
  match l with
  |[] => []
  |None::tl => concat_options tl
  |(Some a)::tl => a::(concat_options tl)
  end.


(*A list of the integers from n to n+m*)
Fixpoint range_nat (length:nat)(initial_value:nat): list nat :=
  match length with
  |0 => []
  |S m => (initial_value)::(range_nat m (initial_value + 1))
  end.

Fixpoint map_list_options{A B} (f : A -> B) (l : list (option A))
  : list (option B):=
  match l with
  |[] =>[]
  |None :: tl => None::map_list_options f tl
  |Some a :: tl => (Some (f a)) :: map_list_options f tl
  end.

Fixpoint mapi_list_options_rec'' {A B : Type}
  (f : nat -> A -> B) (l : list (option A)) (n : nat) {struct l}
  : list (option B) :=
  match l with
  | [] => []
  | None :: tl => None::mapi_list_options_rec'' f tl (S n)
  | Some a :: tl => Some (f n a) :: mapi_list_options_rec'' f tl (S n)
  end.

Definition mapi_list_options''{A B} (f : nat -> A -> B) (l : list (option A))
  : list (option B) := 
  mapi_list_options_rec'' f l 0.

Fixpoint mapi_list_options_rec' {A B : Type}
  (f : nat -> A -> B) (l : list (option A)) (n : nat) {struct l}
  : list (option B) :=
  match l with
  | [] => []
  | None :: tl => None::mapi_list_options_rec' f tl n
  | Some a :: tl => Some (f n a) :: mapi_list_options_rec' f tl (S n)
  end.

Definition mapi_list_options'{A B} (f : nat -> A -> B) (l : list (option A))
  : list (option B) := 
  mapi_list_options_rec' f l 0.

Fixpoint mapi_list_options_rec {A B : Type}
  (f : nat -> A -> B) (l : list (option A)) (n : nat) {struct l}
  : list B :=
  match l with
  | [] => []
  | None :: tl => mapi_list_options_rec f tl (S n)
  | Some a :: tl =>  (f n a) :: mapi_list_options_rec f tl (S n)
  end.

Definition mapi_list_options{A B} (f : nat -> A -> B) (l : list (option A))
  : list B := 
  mapi_list_options_rec f l 0.


Fixpoint map_err_list_options{A B} (f : A -> ErrorMonad B) (l : list (option A))
  : ErrorMonad (list (option B)):=
  match l with
  |[] => Success []
  |None :: tl =>
     lb <-? map_err_list_options f tl;;
        Success (None::lb)
  |Some a :: tl =>
     b <-? f a;;
     lb <-? map_err_list_options f tl;;
     Success ((Some b)::lb)
  end.

Definition split_option{A B} (o : option (A * B)) : (option A) * (option B) :=
  match o with
  |None => (None, None)
  |Some (a,b) => (Some a, Some b)
  end.

Fixpoint remove_index_replace_by_list{A} (l  : list A ) (index : nat)(replace_list : list A) :=
  match l, index with
  |[], _ => l
  |t::q, 0 => replace_list ++ q
  |t::q, S n => t::(remove_index_replace_by_list q n replace_list)
  end.
