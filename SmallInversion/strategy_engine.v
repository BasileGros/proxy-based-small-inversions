From MetaRocq.Utils Require Import utils.
From MetaRocq.Template Require Import All.
From MetaRocq.Template Require Import Checker.
From utils Require Import utils.
From SmallInversion Require Import proxy0.

Definition proxy_adapter : Type := term * list (option term) %type.
Definition dependent_proxy : Type := term * list (option term) %type. (*TODO : find a better name*)

Inductive Glob_def: Type :=
| DefInductive (msg:string) : transformation_info -> mutual_inductive_body -> Glob_def
| DefConst :     string -> term -> Glob_def.

Definition define_glob_def  (g : Glob_def) : TemplateMonad unit :=
  match g with
  | DefInductive msg info mib => tmMkInductive' mib
  | DefConst nam ast => tmMkDefinition nam ast
  end.

Fixpoint define_list_glob_def (l : list Glob_def): TemplateMonad unit :=
  match l with
  | [] => tmReturn tt
  | hd :: tl =>
      _ <-- define_glob_def hd;;
      define_list_glob_def tl
  end.

Definition glob_diff := list Glob_def -> list Glob_def.

Definition transfo := transformation_info -> ErrorMonad (proxy_adapter * list transformation_info * glob_diff)%type.

Definition Result := proxy_adapter * glob_diff%type.
(* type family + generator functions *)


Inductive debug_flag : Set :=
|no_debug : debug_flag
|here_debug : debug_flag
|later_debug : debug_flag.

CoInductive strategy :Type :=
| strat_Fail
| strat_Cons
    (dbg_flag : debug_flag)
    (local_transfo : transfo)
    (on_success: transformation_info -> strategy) : strategy
|strat_Cons_Multiple
   (dbg_flag : debug_flag)
   (local_transfo : transfo)
   (list_on_success: list (transformation_info -> strategy)) : strategy
| strat_Orelse
    (first_try:  strategy)
    (second_try: strategy) : strategy.

Definition strat_Try flags transfo on_success on_failure :=
  strat_Orelse (strat_Cons flags transfo on_success) on_failure.



(*For a given constructor of the inductive, finds and compose all constructors of the subcalls.*)
Definition merge_one_constructor
  (lnew_cons :list (list (option term)))
  (proxy_type : term)
  (index_cons : nat)
  (proxy_cons : term) : term :=

  match lnew_cons with
  |[] => proxy_cons
  |_ =>
     let list_opt_subcons := map (fun l => nth_error l index_cons) lnew_cons in
     let list_subcons := concat_options (concat_options list_opt_subcons) in
     match list_subcons with
     | [] => proxy_cons
     |_ => 
        tApp proxy_cons (proxy_type::list_subcons)
     end
  end.

Definition merge_diff (ldiff : list glob_diff) : glob_diff :=
  List.fold_left (fun d1 d2 l => d1 (d2 l)) ldiff (fun l => l).

(*Takes the proxy adapters created by a transformation and compose them with the results of the subcalls.*)
Definition merge_proxy (gdiff0:glob_diff)
  (lresults : list (dependent_proxy * glob_diff))
  (adapter_transfo : proxy_adapter)
  : dependent_proxy * glob_diff :=
  let (adapter_type, ladapter_cons) := adapter_transfo in
  let (lresults_to_adapt, ldiff) := split (lresults) in
  let alldiff:= fun l => merge_diff ldiff (gdiff0 l) in
  let (ldisp, lnew_cons) := split lresults_to_adapt in
  let new_proxy_type := tApp adapter_type ldisp in
  let new_proxy_cons := mapi_list_options'' (merge_one_constructor lnew_cons new_proxy_type) ladapter_cons in
  ((new_proxy_type,new_proxy_cons), alldiff).


Definition glob_def_proxy_type_debug (n:nat) (t:term) :=
  DefConst ("proxy_type_" ^ (string_of_nat n)) t.

Definition glob_def_proxy_cons_debug (i:nat)(n:nat) (t:term) :=
  DefConst ("proxy_cons_" ^ (string_of_nat i) ^ "_" ^(string_of_nat n)) t.

Definition debug_proxy (gdiff0:glob_diff)
  (fuel : nat)
  (ltransfo_info_partial_down : list transformation_info)
  (lresults : list (dependent_proxy * glob_diff))
  (adapter_transfo : proxy_adapter)
  : dependent_proxy * glob_diff :=
  let (proxy_type, lopt_proxy_cons) := adapter_transfo in
  let lproxy_cons := concat_options lopt_proxy_cons in
  let (lresults_to_adapt, ldiff) := split lresults in
  let alldiff:= fun l => merge_diff ldiff (gdiff0 l) in

  let (ldisp, lopt_new_cons) := split lresults_to_adapt in
  
  let new_proxy_type := tApp proxy_type ldisp in
  let new_proxy_cons := 
    mapi_list_options'
      (merge_one_constructor lopt_new_cons new_proxy_type)
      lopt_proxy_cons
  in
  
  let glob_def_adapter_cons :=
    mapi (fun i t => DefConst ("adapter_proxy_cons_" ^ (string_of_nat i)) t) lproxy_cons
  in
  
  let lglob_def_disp := mapi glob_def_proxy_type_debug ldisp in
  let lglob_def_new_cons := mapi (fun i t => mapi_list_options (glob_def_proxy_cons_debug i) t) lopt_new_cons in
  let lnew_diff_part :=
    map
      ( fun t => DefInductive ("depth : "^ string_of_nat fuel) t (recreate_mib t))
      ltransfo_info_partial_down
  in
  let new_diff :=
    fun l =>
      alldiff
        (lnew_diff_part ++
           ((DefConst "adapter_proxy_type" proxy_type )::(glob_def_adapter_cons)) ++
           lglob_def_disp ++
           (concat lglob_def_new_cons)  ++
           l)
  in
  ((new_proxy_type,new_proxy_cons), new_diff).

Definition later_debug_proxy
  (gdiff0:glob_diff)
  (fuel : nat)
  (ltransfo_info_partial_down : list transformation_info)
  (lresults : list (dependent_proxy * glob_diff))
  (adapter_transfo : proxy_adapter)
  : dependent_proxy * glob_diff :=
  let (proxy_type, lopt_proxy_cons) := adapter_transfo in
  let lproxy_cons := concat_options lopt_proxy_cons in
  let (ladapter, ldiff) := split lresults in
  let (ldisp, lopt_new_cons) := split ladapter in

  
  let alldiff:= fun l => merge_diff ldiff (gdiff0 l) in
  
  let glob_def_adapter_cons :=
    mapi_list_options (fun i t =>
                         DefConst ("_"^(string_of_nat fuel)^
                                     "_adapter_proxy_cons_" ^
                                       (string_of_nat i )) t)
      lopt_proxy_cons
  in
  let lglob_def_new_cons := mapi (fun i t => mapi_list_options (glob_def_proxy_cons_debug i) t) lopt_new_cons in
  let lnew_diff_part :=
    map
      ( fun t => DefInductive ("depth : "^ string_of_nat fuel) t (recreate_mib t))
      ltransfo_info_partial_down
  in
  let new_diff :=
    fun l =>
      alldiff
        (lnew_diff_part ++
           ((DefConst ("_"^(string_of_nat fuel)^"_adapter_proxy_type") proxy_type )::(glob_def_adapter_cons)) ++
           (concat lglob_def_new_cons) ++
           l)
  in
  let new_proxy_type := tApp proxy_type ldisp in
  let new_proxy_cons := 
    mapi_list_options'
      (merge_one_constructor lopt_new_cons new_proxy_type)
      lopt_proxy_cons
  in
  ((new_proxy_type,new_proxy_cons), new_diff).


Definition finalize_constructor
  (transfo_info: transformation_info) (index_constructor : nat) (c : constructor_body)
  : term :=
  let lambda_params := rev_params_into_lambdas (pmib transfo_info).(pseudo_params) in
  let lambda_args := rev_params_into_lambdas c.(cstr_args) in
  let dB_args := rev_range_deBruijn (length c.(cstr_args) + (pmib transfo_info).(pseudo_npars)) 0 in
  (lambda_params
     (lambda_args
        (tApp (tConstruct (inductive_transfo transfo_info) index_constructor []) dB_args))).


Definition finalize_proxy
  : transfo :=
  fun transfo_info =>
    let poib := poib transfo_info in
    let prefix := prefix transfo_info in
    let renamed_poib :=
      if isdep transfo_info
      then
        rename_poib prefix "_dep" poib
      else
        rename_poib prefix "" poib
    in
    let renamed_constructors :=
      if isdep transfo_info
      then
        map_list_options (rename_cstr prefix "_dep") (lctors transfo_info)
      else
        map_list_options (rename_cstr prefix "") (lctors transfo_info)
    in
    let renamed_mib := recreate_mib' (pmib transfo_info) renamed_poib renamed_constructors in
    let renamed_transfo_info :=
      recreate_transfo_info
        transfo_info
        (pmib transfo_info)
        renamed_poib
        renamed_constructors
    in
    let renamed_inductive :=
      if isdep transfo_info
      then
        rename_inductive prefix "_dep" (inductive_transfo transfo_info)
      else
        rename_inductive prefix "" (inductive_transfo transfo_info)
    in
    let list_ctors :=
      mapi_list_options'
        (fun n c => ( finalize_constructor renamed_transfo_info n c))
        renamed_constructors
    in
    Success ((tInd renamed_inductive [], list_ctors),[], (fun env => DefInductive "Finalize_proxy" transfo_info renamed_mib :: env) ).

Fixpoint map_and_merge_results {A} (lf: list (A -> ErrorMonad Result)) (lA:list A)
  (m : list (dependent_proxy*glob_diff) -> ErrorMonad Result)
  : ErrorMonad Result :=
  match lf, lA with
  | _, nil => m nil
  | nil, _ => Error "When merging results, not enough strategy continuations."
  | f :: more_f, a :: more_a =>
      '(adapter,tbd,gdiff) <-? f a;;
      map_and_merge_results more_f more_a (fun l => m  ((adapter,tbd,gdiff)::l))
  end.

Fixpoint debug_map_and_merge_results {A} (lf: list (A -> ErrorMonad Result)) (lA:list A)
  (m : list A ->  list (dependent_proxy*glob_diff) -> ErrorMonad Result)
  : ErrorMonad Result :=
  match lf, lA with
  | _, nil => m nil nil
  | nil, _ => Error "When merging results, not enough strategy continuations."
  | f :: more_f, a :: more_a =>
      '(adapter,tbd,gdiff) <-? f a;;
      debug_map_and_merge_results more_f more_a (fun l l' => m (a::l) ((adapter,tbd,gdiff)::l')  )
  end.

Unset Guard Checking.
Fixpoint execute_strategy
  (strat : strategy) (transfo_info : transformation_info) (depth : nat) {struct depth}
  : ErrorMonad Result :=
      match strat with
      |strat_Fail => Error "Strategy Failed : do we actually need this ?"
      |strat_Orelse s1 s2 =>
         match execute_strategy s1 transfo_info (S depth) with
         | Success res => Success res
         | Error e => execute_strategy s2 transfo_info (S depth)
         end
      | strat_Cons dbg_flag transfo success =>
          match transfo transfo_info with
          |Error e => Error e
          |Success (adapter_transfo, l_sub_proxies, gdiff0 ) =>
             match dbg_flag with
             |no_debug =>
                map_and_merge_results
                  (list_const (fun sub => execute_strategy (success sub) sub (S depth)) (length l_sub_proxies))
                  l_sub_proxies
                  (fun l => Success (merge_proxy gdiff0 l adapter_transfo))
             |here_debug =>
                debug_map_and_merge_results
                  (list_const (fun sub => execute_strategy (success sub) sub (S depth)) (length l_sub_proxies))
                  l_sub_proxies
                  (fun l l' => Success (debug_proxy gdiff0 depth l l' adapter_transfo))
             |later_debug =>
                debug_map_and_merge_results
                  (list_const (fun sub => execute_strategy (success sub) sub (S depth)) (length l_sub_proxies))
                  l_sub_proxies
                  (fun l l' => Success(later_debug_proxy gdiff0 depth l l' adapter_transfo))
             end
          end
      | strat_Cons_Multiple dbg_flag transfo l_success =>
          match transfo transfo_info with
          |Error e => Error e
          |Success (adapter_transfo, l_sub_proxies, gdiff0 ) =>
             match dbg_flag with
             |no_debug =>
                map_and_merge_results
                  (map (fun success => (fun sub => execute_strategy (success sub) sub (S depth))) l_success)
                  l_sub_proxies
                  (fun l => Success (merge_proxy gdiff0 l adapter_transfo))
             |here_debug =>
                debug_map_and_merge_results
                  (map (fun success => (fun sub => execute_strategy (success sub) sub (S depth))) l_success)
                  l_sub_proxies
                  (fun l l' => Success (debug_proxy gdiff0 depth l l' adapter_transfo))
             |later_debug =>
                debug_map_and_merge_results
                  (map (fun success => (fun sub => execute_strategy (success sub) sub (S depth))) l_success)
                  l_sub_proxies
                  (fun l l' => Success(later_debug_proxy gdiff0 depth l l' adapter_transfo))
             end
          end

  end.

Fixpoint debug_execute_strategy
  (strat : strategy) (transfo_info : transformation_info) (depth : nat) {struct depth}
  : ErrorMonad Result :=
      match strat with
      |strat_Fail => Error "Strategy Failed : do we actually need this ?"
      |strat_Orelse s1 s2 =>
         match debug_execute_strategy s1 transfo_info (S depth) with
         | Success res => Success res
         | Error e => Error e
         end
      | strat_Cons dbg_flag transfo success =>
          match transfo transfo_info with
          |Error e => Error e
          |Success (adapter_transfo, l_sub_proxies, gdiff0 ) =>
             match dbg_flag with
             |no_debug =>
                map_and_merge_results
                  (list_const (fun sub => debug_execute_strategy (success sub) sub (S depth)) (length l_sub_proxies))
                  l_sub_proxies
                  (fun l => Success (merge_proxy gdiff0 l adapter_transfo))
             |here_debug =>
                debug_map_and_merge_results
                  (list_const (fun sub => debug_execute_strategy (success sub) sub (S depth)) (length l_sub_proxies))
                  l_sub_proxies
                  (fun l l' => Success (debug_proxy gdiff0 depth l l' adapter_transfo))
             |later_debug =>
                debug_map_and_merge_results
                  (list_const (fun sub => debug_execute_strategy (success sub) sub (S depth)) (length l_sub_proxies)) l_sub_proxies
                  (fun l l' => Success(later_debug_proxy gdiff0 depth l l' adapter_transfo))
             end
          end
      | strat_Cons_Multiple dbg_flag transfo l_success =>
          match transfo transfo_info with
          |Error e => Error e
          |Success (adapter_transfo, l_sub_proxies, gdiff0 ) =>
             match dbg_flag with
             |no_debug =>
                map_and_merge_results
                  (map (fun success => (fun sub => debug_execute_strategy (success sub) sub (S depth))) l_success)
                  l_sub_proxies
                  (fun l => Success (merge_proxy gdiff0 l adapter_transfo))
             |here_debug =>
                debug_map_and_merge_results
                  (map (fun success => (fun sub => debug_execute_strategy (success sub) sub (S depth))) l_success)
                  l_sub_proxies
                  (fun l l' => Success (debug_proxy gdiff0 depth l l' adapter_transfo))
             |later_debug =>
                debug_map_and_merge_results
                  (map (fun success => (fun sub => debug_execute_strategy (success sub) sub (S depth))) l_success)
                  l_sub_proxies
                  (fun l l' => Success(later_debug_proxy gdiff0 depth l l' adapter_transfo))
             end
          end

  end.
Set Guard Checking.

Definition finalize_proxy0 (proxy0:term) (r:Result) : ErrorMonad term :=
  let '((proxy_type,lproxy_cons),deps) := r in
  let concat_lcons := concat_options lproxy_cons in
  Success (tApp proxy0 (proxy_type::concat_lcons)).


Definition execute_strategy_err
  (strat : strategy)
  (derec_transfo_info : transformation_info)
  : ErrorMonad (term * list Glob_def) :=
  result_strat <-? execute_strategy strat derec_transfo_info 0;;
  proxy__0 <-? create_proxy0 derec_transfo_info;;
  typeclass <-? finalize_proxy0 proxy__0 result_strat;;
  let (_,gdiff) := result_strat in
  Success (typeclass, gdiff []).

Definition debug_strategy_err  (
    strat : strategy)
  (derec_transfo_info : transformation_info)
  : ErrorMonad (term * list Glob_def) :=
  result_strat <-? debug_execute_strategy strat derec_transfo_info 0;;
  proxy__0 <-? create_proxy0 derec_transfo_info;;
  typeclass <-? finalize_proxy0 proxy__0 result_strat;;
  let (_,gdiff) := result_strat in
  Success (typeclass, gdiff []).
