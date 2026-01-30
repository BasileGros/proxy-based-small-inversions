From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.

From utils Require Import map_constr_with_binders.

(*Creates an decreasing list of deBruijn indexes*)
Definition rev_range_deBruijn : forall len val_min : nat, list term :=
  let loop := (fix f (acc:list term) (len :nat) (val:nat) :=
    match len with
    |0 => acc
    |S m => f ((tRel val)::acc) m (val + 1)
    end
  ) in loop [].

(*Zeta-reduction*)
Fixpoint remove_let_in
  (t:term) 
  (l:context)
  : term :=
  match t with

  |tProd nom type cont => 
     let type_new := (remove_let_in type l) in
     let decl := mkdecl nom None type_new  in  
     let result_term := remove_let_in cont (decl::l) in 
     tProd nom type_new result_term

  |tLambda nom type cont => 
     let type_new := (remove_let_in type l) in
     let decl := mkdecl nom None type_new  in  
     let result_term := remove_let_in cont (decl::l) in 
     tLambda nom type_new result_term

  |tLetIn nom valeur type cont => 
     let type_new := (remove_let_in type l) in
     let decl := mkdecl nom (Some valeur) type_new  in 
     let result_term := remove_let_in cont (decl::l) in
     (*lift_moins_un 0*) result_term

  |x => (expand_lets l x)

  end.


(*Lifts a telescope past the firts nth elements by the given amount*)
Fixpoint lift_past_params
  (value : nat)
  (telescope:term)
  (nb_params : nat)
  (threshold:nat)
  : term :=
  match telescope,nb_params with
  |tProd name type body, S n =>
     tProd name type (lift_past_params value body n threshold)
  |tLetIn name val type body, S n =>
     tLetIn name val type (lift_past_params value body n threshold)
  |t, _ => lift value threshold t
  end.

(*Lifts spcifically the final inductive call in a constructor's type telescope*)
Fixpoint lift_past_telescope
  (value : nat)
  (telescope:term)
  (threshold:nat)
  : term :=
  match telescope with
  |tProd name type body => tProd name type (lift_past_telescope value body threshold)
  |tApp val list_args => tApp (lift value threshold val) list_args
  |t => lift value threshold t
  end.




(*Takes a list of de Bruijn indexes tRel i and return a list of natural indexes i*)
Fixpoint extract_tRel_list (list_tRel : list term) : list nat
  :=
  match list_tRel with
  |[]             => []
  |(tRel n)::tail => n::(extract_tRel_list tail)
  |_::tail        => (extract_tRel_list tail)                  
  end.


(** Functions to use tVars in the place of db indices and swap afterwards.*)

Fixpoint pos_string (str : string) (n : nat)(l : list aname) : option nat :=
  match l with
  |[] => None
  |s::tl =>
     match s.(binder_name) with
     |nAnon => pos_string str (S n) tl
     |nNamed id =>
       if String.eqb id str
       then
         Some n
       else
         pos_string str (S n) tl
     end
  end.

Definition position_string  (str : string) (l : list aname) : option nat :=
  pos_string str 0 l.

Fixpoint convert_var_to_rel
  (glob : global_env)
  (lvars : list aname)
  (lctx : context)
  (t:term)
  {struct t}
  : term :=
  match t with
  |tVar id =>
     match position_string id lvars with
      |None => tVar id
     |Some val =>  tRel ((length lctx) + val)
     end
  |_ => map_constr_with_binders glob (convert_var_to_rel glob lvars) lctx t
  end.

Fixpoint context_vars_to_rel
  (glob : global_env)(ctx : context)
  : list context_decl × list aname :=
  match ctx with
  |[] => ([],[])
  |decl::tl =>
     let (new_tl,lvars) := context_vars_to_rel glob tl in
     let new_decl := map_decl (convert_var_to_rel glob lvars []) decl in
     (new_decl::new_tl, decl.(decl_name)::lvars)
  end.

Definition append_context_vars_prod
  (glob : global_env)(lctx : context) (t:term)
  : term :=
  let (new_context,lvars) := context_vars_to_rel glob lctx in
  let hd_term := it_mkProd_or_LetIn new_context in
  let new_term := convert_var_to_rel glob lvars [] t in
  hd_term new_term.

Fixpoint ctx_to_call (p:context) (lvars : list term) : list term :=
  match p with
  |[] => lvars
  |d::tl =>
     match d.(decl_name).(binder_name) with
     |nAnon => ctx_to_call tl lvars
     |nNamed nam => ctx_to_call tl ((tVar nam) :: lvars)
     end
  end.



Definition context_to_call (p:context) : list term :=
  ctx_to_call p [].

Definition name_inductive (i:inductive) : string :=
  let (_, s) := (inductive_mind i) in
  s.


Fixpoint name_term (t:term) : string :=
  match t with
  | tCast c kind t0 =>  name_term c
  | tProd na A B =>
      match na.(binder_name) with
      |nAnon => name_term A
      |nNamed nam => nam
      end
  | tLambda na T M =>
      match na.(binder_name) with
      |nAnon => name_term T
      |nNamed nam => nam
      end
  | tLetIn na b t0 c =>
      match na.(binder_name) with
      |nAnon => name_term t0
      |nNamed nam => nam
      end
  | tApp u v => name_term u
  | tCase ci p c brs => name_inductive (ci_ind ci)
  | tProj p c => name_term c
  | tInd i _ => name_inductive i
  | tConstruct i _ _ => name_inductive i
  | tConst na _ => let (_,s) := na in s
  | tVar s => s
  | _ => "ctx_unamed"
  end.

Fixpoint name_context (p:context) (n:nat) : context := 
  match p with
  |[] => []
  |d::tl =>
     match d.(decl_name).(binder_name) with
     |nAnon =>
        let string_d := name_term d.(decl_type) in
        let new_d :=
          
          {|
            decl_name :=
              {| binder_name := nNamed ("_"^string_d^(string_of_nat n));
                binder_relevance := d.(decl_name).(binder_relevance) |};
            decl_body := d.(decl_body);
            decl_type := d.(decl_type) |}
        in
        new_d::(name_context tl (S n))
            
     |nNamed nam =>
        let new_d :=
          {|
            decl_name :=
              {| binder_name := nNamed ("_"^nam);
                binder_relevance := d.(decl_name).(binder_relevance) |};
            decl_body := d.(decl_body);
            decl_type := d.(decl_type)
          |} in
            
                  new_d::(name_context tl n)
     end
  end.


Definition append_context_vars_lambda
  (glob : global_env)(lctx : context) (t:term)
  : term :=
  let (new_context,lvars) := context_vars_to_rel glob lctx in
  let hd_term := it_mkLambda_or_LetIn new_context in
  let new_term := convert_var_to_rel glob lvars [] t in
  hd_term new_term.


Fixpoint var_inductive (telescope:term) (var : term) : term :=
  match telescope with
  |tProd name type body => tProd name type (var_inductive body var)
  |tLetIn name value type body => tLetIn name value type (var_inductive body var)
  |tLambda name type body => tLambda name type (var_inductive body var)
  |tApp app list_app => tApp var list_app
  |tRel _ => var
  |t => t
  end.

Definition string_to_aname (nam : string) : aname :=
  {| binder_name := nNamed nam;
    binder_relevance := Relevant|}.

Definition create_context_constructor
  (name_disp : string)(cons : constructor_body)
  : context_decl :=
  
  let new_type := var_inductive cons.(cstr_type) (tVar ("_"^name_disp)) in
  let new_decl := vass (string_to_aname ("_"^ cons.(cstr_name))) new_type in
  new_decl.

Fixpoint create_context_constructors
  (name_disp : string)(lcons : list constructor_body) (ctx_acc : context)
  : context :=
  match lcons with
  |[] => ctx_acc
  |cns::tl =>
     let new_decl := create_context_constructor name_disp cns in
     create_context_constructors name_disp tl ( new_decl :: ctx_acc)
  end.


Definition list_nat_to_list_db (l : list nat) :=
  map (fun n => tRel n) l.
  
