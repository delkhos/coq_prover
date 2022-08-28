Require Import ast.
Require Import environment.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Init.Decimal.
Require Import Coq.Strings.String.
Require Import Uint63.


Fixpoint eval_aexpr (expr: aexpr) (e: env) : error integer_value :=
match expr  with
|Num v => NoError (Known v)
|Minus lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown , _ => NoError Unknown
      | _, Unknown => NoError Unknown
      |Known val1, Known val2 => NoError (Known (Z.sub val1 val2))
      end
    end
  end
|Plus lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown , _ => NoError Unknown
      | _, Unknown => NoError Unknown
      |Known val1, Known val2 => NoError (Known (Z.add val1 val2))
      end
    end
  end
|Var id =>
  match get_var_env e id with
  |Error s => Error s
  |NoError res => NoError res
  end
|Arr id index =>
  match eval_aexpr index e with
  |Error s => Error s
  |NoError index_val =>
    match index_val with
    |Unknown => Error "tried accessing array with index of unknown value"
    |Known ind_val =>
      match get_arr_env e id ind_val with
      |Error s => Error s
      |NoError res => NoError res
      end
    end
  end
end.

Fixpoint eval_bexpr (expr: bexpr) (e: env): error bool :=
match expr with
|Bool b => NoError b
|Lt lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 => 
      match v1, v2 with
      |Unknown, _ => Error "trying to compare an unknown value"
      |_ , Unknown => Error "trying to compare an unknown value"
      | Known val1, Known val2 => NoError (Z.ltb val1 val2)
      end
    end
  end
|Lte lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown, _ => Error "trying to compare an unknown value"
      |_ , Unknown => Error "trying to compare an unknown value"
      | Known val1, Known val2 => NoError (Z.leb val1 val2)
      end
    end
  end
|Eq lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown, _ => Error "trying to compare an unknown value"
      |_ , Unknown => Error "trying to compare an unknown value"
      | Known val1, Known val2 => NoError (Z.eqb val1 val2)
      end
    end
  end
|Neq lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown, _ => Error "trying to compare an unknown value"
      |_ , Unknown => Error "trying to compare an unknown value"
      | Known val1, Known val2 => NoError (negb (Z.eqb val1 val2))
      end
    end
  end
|Gt lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown, _ => Error "trying to compare an unknown value"
      |_ , Unknown => Error "trying to compare an unknown value"
      | Known val1, Known val2 => NoError (Z.gtb val1 val2)
      end
    end
  end
|Gte lhs rhs =>
  let eval1 := eval_aexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_aexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 =>
      match v1, v2 with
      |Unknown, _ => Error "trying to compare an unknown value"
      |_ , Unknown => Error "trying to compare an unknown value"
      | Known val1, Known val2 => NoError (Z.geb val1 val2)
      end
    end
  end
|Nand lhs rhs =>
  let eval1 := eval_bexpr lhs e in
  match eval1 with
  |Error s => Error s
  |NoError v1 =>
    let eval2 := eval_bexpr rhs e in
    match eval2 with
    |Error s2 => Error s2
    |NoError v2 => NoError (negb (v1 && v2))
    end
  end
end.


Inductive state (A: Type) : Type :=
|State (lbl: A) (e: env)
.

Notation "lbl [[ envi ]]" := (State lbl envi) (at level 40).

Definition trace (A: Type) : Type := ne_list (state A).

Inductive sem_ret (A: Type) : Type :=
|Sem_ret (t: trace A) (n: nat) (broke: bool)
.

Notation "'Trace:' t 'RemainingN:' n 'Broke:' broke" := (Sem_ret t n broke) (at level 110, format "'[' 'Trace:' '//' t '//' '//' 'RemainingN:'  n  '//' '//' 'Broke:'  broke '//' '//' ']'").

Definition get_current_state (A: Type) (pref: trace A): state A :=
match pref with
|Single st => st
|NECons st tail => st
end.

Fixpoint SF_B_P_T_Semantics_stmt (A: Type) (lab_eq: A->A->bool) (pref: trace A) (T: statement A) (n k :nat) (breakable: bool): error (sem_ret A):=
match n,k with
|0 , _ => NoError (Sem_ret A pref 0 false)
|_ , 0 => NoError (Sem_ret A pref 0 false)
|S n' , S k' =>
match T with
|VarAssign _ assignee assigned l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error" (* should add label to the error for better debug *)
    |true => 
      let assigned_ret := eval_aexpr assigned e in
      match assigned_ret with 
      |Error s => Error s
      |NoError assigned_val => 
        match env_set_var e assignee assigned_val with
        |Error s2 => Error s2
        |NoError ne => NoError ( Sem_ret A ((State A (af A l) ne)~~pref) k' false )
        end
      end
    end
  end
|ArrAssign _ assignee index assigned l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      let assigned_ret := eval_aexpr assigned e in
      match assigned_ret with 
      |Error s => Error s
      |NoError assigned_val =>
        let index_ret := eval_aexpr index e in
        match index_ret with 
        |Error s2 => Error s2
        |NoError index_val =>
          match env_set_arr e assignee index_val assigned_val with
          |Error s3 => Error s3
          |NoError ne => NoError ( Sem_ret A ((State A (af A l) ne)~~pref) k' false )
          end
        end
      end
    end
  end
|Emptystmt _ l => 
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      NoError ( Sem_ret A ((State A (af A l) e)~~pref) k' false )
    end
  end
|Break _ l => 
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      NoError ( Sem_ret A ((State A (br A l) e)~~pref) k' true )
    end
  end
|If _ test body l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      let test_ret := eval_bexpr test e in
      match test_ret with 
      |Error s => Error s
      |NoError test_val =>
        match test_val with
        |true =>
          let if_body_lbling := get_stmt_labelling A body in
          SF_B_P_T_Semantics_stmt A lab_eq ((State A (atl A if_body_lbling) e)~~pref) body n' k' breakable(* bien check ici l'étiquette à rajouter *)
        |false => NoError (Sem_ret A ((State A (af A l) e)~~pref) k' false )
        end
      end
    end
  end
|Ifelse _ test ibody ebody l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      let test_ret := eval_bexpr test e in
      match test_ret with 
      |Error s => Error s
      |NoError test_val =>
        match test_val with
        |true =>
          let if_body_lbling := get_stmt_labelling A ibody in
          SF_B_P_T_Semantics_stmt A lab_eq ((State A (atl A if_body_lbling) e)~~pref) ibody n' k' breakable
        |false => 
          let else_body_lbling := get_stmt_labelling A ebody in
          SF_B_P_T_Semantics_stmt A lab_eq ((State A (atl A else_body_lbling) e)~~pref) ebody n' k' breakable
        end
      end
    end
  end
|Compound _ sts l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      match sts with
      |Single st =>
        match get_current_state A pref with
        |State _ lbl e =>
          let stmt_ret := SF_B_P_T_Semantics_stmt A lab_eq pref st n' k breakable in
          match stmt_ret with
          |Error s => Error s
          |NoError (Sem_ret _ new_pref new_n broke) => NoError ( Sem_ret A new_pref new_n broke) (*add pred to new_n ? *)
          end
        end
      |stmt ~~ tail =>
        match get_current_state A pref with
        |State _ lbl e =>
          let stmt_ret := SF_B_P_T_Semantics_stmt A lab_eq pref stmt n' k breakable in
          match stmt_ret with
          |Error s => Error s
          |NoError (Sem_ret _ new_pref new_n broke) =>
            match broke , breakable with
            | true , true => NoError ( Sem_ret A new_pref new_n broke)
            | _ , _ => 
              let new_compound := Compound A tail (mkLabelling A (af A (get_stmt_labelling A stmt))(af A l)(br A l)) in
              SF_B_P_T_Semantics_stmt A lab_eq new_pref new_compound n' new_n breakable
            end
          end
        end
      end
    end
  end
|Breakable _ sts l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true => 
      match sts with
      |Single st =>
        match get_current_state A pref with
        |State _ lbl e =>
          let stmt_ret := SF_B_P_T_Semantics_stmt A lab_eq pref st n' k true in (* k' ? *)
          match stmt_ret with
          |Error s => Error s
          |NoError (Sem_ret _ new_pref new_n broke) => NoError ( Sem_ret A new_pref new_n broke) (*add pred to new_n ? *)
          end
        end
      |stmt ~~ tail =>
        match get_current_state A pref with
        |State _ lbl e =>
          let stmt_ret := SF_B_P_T_Semantics_stmt A lab_eq pref stmt n' k true in
          match stmt_ret with
          |Error s => Error s
          |NoError (Sem_ret _ new_pref new_n broke) =>
            match broke with
            | true => NoError ( Sem_ret A new_pref new_n false) (* do not propagate the break*)
            | false => 
              let new_breakable := Breakable A tail (mkLabelling A (af A (get_stmt_labelling A stmt))(af A l)(br A l)) in
              SF_B_P_T_Semantics_stmt A lab_eq new_pref new_breakable n' new_n true
            end
          end
        end
      end
    end
  end
|While _ test body l =>
  match get_current_state A pref with
  |State _ lbl e =>
    match lab_eq lbl (atl A l) with
    |false => Error "at label error"
    |true =>
      let test_ret := eval_bexpr test e in
      match test_ret with 
      |Error s => Error s
      |NoError test_val =>
        match test_val with
        |true => 
          let body_lbl := get_stmt_labelling A body in
          let body_ret := SF_B_P_T_Semantics_stmt A lab_eq ((State A (atl A body_lbl) e)~~pref) body n' k' true in
          match body_ret with
          |Error s2 => Error s2
          |NoError (Sem_ret _ new_pref new_n broke) =>
            match broke with
            |true => NoError ( Sem_ret A new_pref new_n false) (* get out of while *) (*use pred of new_n ? *)
            |false => SF_B_P_T_Semantics_stmt A lab_eq new_pref T n' new_n true (* continue loop *)
            end
          end
        |false => NoError (Sem_ret A ((State A (af A l) e)~~pref) k' false)
        end
      end
    end
  end
end
end
.

Fixpoint init_env (e: env) (l: list declaration): error env :=
match l with
|nil => NoError e
|head::tail =>
  match head with
  |VarInit id =>
    match env_add_var e id with
    |Error s => Error s
    |NoError ne => init_env ne tail
    end
  |ArrayInit id size =>
    match env_add_arr e id size with
    |Error s => Error s
    |NoError ne => init_env ne tail
    end
  end
end.


(* stateful bounded prefix trace semantics *)
Definition SF_B_P_T_Semantics_prog (A: Type) (lab_eq: A->A->bool) (p: prog A) (n :nat): error (sem_ret A) :=
match p with
|Prog _ vars sts l => 
  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for empty trace"
    | S 0 => NoError ( Sem_ret A (Single (State A (atl A l) start_env)) 0 false)
    | S n' => SF_B_P_T_Semantics_stmt A lab_eq (Single(State A (atl A l) start_env)) sts n' n' false
    end
  end
end.

Definition SF_B_P_T_Semantics_prog_len (A: Type) (lab_eq: A->A->bool) (p: prog A) (n: nat): error nat :=
match (SF_B_P_T_Semantics_prog A lab_eq p n) with
|NoError (Sem_ret _ t _ _ ) => NoError (ne_length t)
|Error s => Error s
end.

