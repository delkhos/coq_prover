Require Import ast.
Require Import environment.
Require Import semantics.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.

Inductive relevant_variables : Type :=
|Rel_Vars (vars arrs : list string)
.

Inductive relevant_state (A: Type) : Type :=
|RState (lbl: A) (e: env) (relevant: bool)
.

Inductive relevant_state_mem (A C: Type) : Type :=
|RMState (lbl: A) (e: env) (relevant: bool) (mem: C)
.

Definition is_state_relevant {A: Type} (s: relevant_state A) : bool :=
match s with
|RState _ _ _ r => r
end.

Definition is_state_mem_relevant {A C: Type} (s: relevant_state_mem A C) : bool :=
match s with
|RMState _ _ _ _ r _ => r
end.

Definition relevant_trace (A: Type) : Type := ne_list (relevant_state A).

Inductive step_return (A: Type) : Type :=
|RelevantVar (lbl: A) (e: env) (var: string)
|RelevantArr (lbl: A) (e: env) (arr: string)
|NotRelevant (lbl: A) (e: env)
|Ret_error (s: string)
|Ret_none
.

Arguments RelevantVar {_} _ _ _.
Arguments RelevantArr {_} _ _ _.
Arguments NotRelevant {_} _ _.
Arguments Ret_error {_} _.
Arguments Ret_none {_}.


Fixpoint SF_B_P_T_Semantics_stmt_step (A: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (curr_lbl: A) (curr_env: env) (T: statement A) : step_return A :=
let fix SF_B_P_T_Semantics_stmtl_step (sts: ne_list(statement A)): step_return A :=
match sts with
|Single st => SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars curr_lbl curr_env st
| st ~~ tail =>
  match SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars curr_lbl curr_env st with
  | Ret_none => SF_B_P_T_Semantics_stmtl_step tail
  | X => X
  end
end
in
match T with
|VarAssign _ assignee assigned l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => 
    let assigned_ret := eval_aexpr assigned curr_env in
    match assigned_ret with 
    |Error s => Ret_error (String.append "Error while evaluating assigned value : " s )
    |NoError assigned_val => 
      match env_set_var curr_env assignee assigned_val with
      |Error s2 => Ret_error (String.append "Error while updating env : " s2 )
      |NoError ne => 
        match rel_vars with
        |Rel_Vars vars _ =>
          match List.existsb (String.eqb assignee) vars with
          |true => RelevantVar (af A l) ne assignee
          |false => NotRelevant (af A l) ne
          end
        end
      end
    end
  end
|ArrAssign _ assignee index assigned l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => 
    let assigned_ret := eval_aexpr assigned curr_env in
    match assigned_ret with 
    |Error s => Ret_error (String.append "Error while evaluating assigned value : " s )
    |NoError assigned_val => 
      let index_ret := eval_aexpr index curr_env in
      match index_ret with 
      |Error s2 => Ret_error (String.append "Error while evaluating index value : " s2 )
      |NoError index_val => 
        match env_set_arr curr_env assignee index_val assigned_val with
        |Error s3 => Ret_error (String.append "Error while updating env : " s3 )
        |NoError ne => 
          match rel_vars with
          |Rel_Vars _ arrs =>
            match List.existsb (String.eqb assignee) arrs with
            |true => RelevantVar (af A l) ne assignee
            |false => NotRelevant (af A l) ne
            end
          end
        end
      end
    end
  end
|Emptystmt _ l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => NotRelevant (af A l) curr_env
  end
|Break _ l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => NotRelevant (br A l) curr_env
  end
|If _ test body l =>
  match lab_eq curr_lbl (atl A l) with
  |false => SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars curr_lbl curr_env body
  |true => 
    let test_ret := eval_bexpr test curr_env in
    match test_ret with 
    |Error s => Ret_error (String.append "Error while evaluating if test : " s )
    |NoError test_val =>
      match test_val with
      |true => 
        let if_body_lbling := get_stmt_labelling A body in
        NotRelevant (atl A if_body_lbling) curr_env
      |false => NotRelevant (af A l) curr_env
      end
    end
  end
|Ifelse _ test ibody ebody l =>
  match lab_eq curr_lbl (atl A l) with
  |false => 
    let ibody_ret := SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars curr_lbl curr_env ibody in
    match ibody_ret with
    | Ret_none => SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars curr_lbl curr_env ebody
    | _ => ibody_ret
    end
  |true => 
    let test_ret := eval_bexpr test curr_env in
    match test_ret with 
    |Error s => Ret_error (String.append "Error while evaluating if test : " s )
    |NoError test_val =>
      match test_val with
      |true => 
        let if_ibody_lbling := get_stmt_labelling A ibody in
        NotRelevant (atl A if_ibody_lbling) curr_env
      |false =>
        let if_ebody_lbling := get_stmt_labelling A ebody in
        NotRelevant (atl A if_ebody_lbling) curr_env
      end
    end
  end
|While _ test body l =>
  match lab_eq curr_lbl (atl A l) with
  |false => SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars curr_lbl curr_env body
  |true => 
    let test_ret := eval_bexpr test curr_env in
    match test_ret with 
    |Error s => Ret_error (String.append "Error while evaluating if test : " s )
    |NoError test_val =>
      match test_val with
      |true => 
        let while_body_lbling := get_stmt_labelling A body in
        NotRelevant (atl A while_body_lbling) curr_env
      |false => NotRelevant (af A l) curr_env
      end
    end
  end
|Compound _ sts l => SF_B_P_T_Semantics_stmtl_step sts
|Breakable _ sts l => SF_B_P_T_Semantics_stmtl_step sts
end
.

Definition SF_B_P_T_Semantics_stmt_step_prefix (A: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (program: prog A) (n: nat) : error (relevant_trace A) :=
match program with
|Prog _ vars sts l => 

  let fix SF_B_P_T_Semantics_stmt_step_prefix_aux (k: nat) (prog_body: statement A) (lbl: A) (e: env) (acc: ne_list (relevant_state A)) : error (relevant_trace A) := 
  match k with
  |0 => NoError acc
  | S k' =>
    match SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars lbl e prog_body with
    |RelevantVar lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux k' prog_body lbl2 e2 ((RState A lbl2 e2 true)~~acc)
    |RelevantArr lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux k' prog_body lbl2 e2 ((RState A lbl2 e2 true)~~acc)
    |NotRelevant lbl2 e2   => SF_B_P_T_Semantics_stmt_step_prefix_aux k' prog_body lbl2 e2 ((RState A lbl2 e2 false)~~acc)
    |Ret_error s => Error (String.append "Error while computing prefix : " s)
    |Ret_none => 
      match lab_eq lbl (af A l) with
      |true => NoError acc
      |false => Error "Error while computing prefix : cannot find statement with at label, but end of program not reached"
      end
    end
  end
  in

  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for empty trace"
    | S 0 => NoError ( Single (RState A (atl A l) start_env true))
    | S n' => SF_B_P_T_Semantics_stmt_step_prefix_aux n' sts (atl A l) start_env (Single (RState A (atl A l) start_env true))
    end
  end

end
.

Definition SF_B_P_T_Semantics_stmt_step_prefix_nth (A: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (program: prog A) (n: nat) : error (relevant_state A) :=
match program with
|Prog _ vars sts l => 

  let fix SF_B_P_T_Semantics_stmt_step_prefix_aux_nth (k: nat) (prog_body: statement A) (lbl: A) (e: env) (relevant: bool) : error (relevant_state A) := 
  match k with
  |0 => NoError (RState A lbl e relevant)
  | S k' =>
    match SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars lbl e prog_body with
    |RelevantVar lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth k' prog_body lbl2 e2 true
    |RelevantArr lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth k' prog_body lbl2 e2 true
    |NotRelevant lbl2 e2   => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth k' prog_body lbl2 e2 false
    |Ret_error s => Error (String.append "Error while computing prefix : " s)
    |Ret_none => 
      match lab_eq lbl (af A l) with
      |true => NoError (RState A lbl e true)
      |false => Error "Error while computing prefix : cannot find statement with at label, but end of program not reached"
      end
    end
  end
  in

  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for 0th state"
    | S 0 => NoError (RState A (atl A l) start_env true)
    | S n' => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth n' sts (atl A l) start_env true
    end
  end

end
.

Definition SF_B_P_T_Semantics_stmt_step_prefix_nth_mem (A C: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (program: prog A) (n: nat) (start_memory: C) (mem_update: (relevant_state A)->C->C) : error (relevant_state_mem A C) :=
match program with
|Prog _ vars sts l => 

  let fix SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_mem (k: nat) (prog_body: statement A) (lbl: A) (e: env) (relevant: bool) (memory: C) : error (relevant_state_mem A C) := 
  match k with
  |0 => NoError (RMState A C lbl e relevant memory)
  | S k' =>
    match SF_B_P_T_Semantics_stmt_step A lab_eq rel_vars lbl e prog_body with
    |RelevantVar lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_mem k' prog_body lbl2 e2 true (mem_update (RState A lbl e relevant) memory)
    |RelevantArr lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_mem k' prog_body lbl2 e2 true (mem_update (RState A lbl e relevant) memory)
    |NotRelevant lbl2 e2   => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_mem k' prog_body lbl2 e2 false (mem_update (RState A lbl e relevant) memory)
    |Ret_error s => Error (String.append "Error while computing prefix : " s)
    |Ret_none => 
      match lab_eq lbl (af A l) with
      |true => NoError (RMState A C lbl e true memory)
      |false => Error "Error while computing prefix : cannot find statement with at label, but end of program not reached"
      end
    end
  end
  in

  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for 0th state"
    | S 0 => NoError (RMState A C (atl A l) start_env true start_memory)
    | S n' => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_mem n' sts (atl A l) start_env true start_memory
    end
  end

end
.


Fixpoint SF_B_P_T_Semantics_stmt_step_U (A: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (curr_lbl: A) (curr_env: env) (T: ustatement A) : step_return A :=
let fix SF_B_P_T_Semantics_stmtl_step_U (sts: ne_list(ustatement A)): step_return A :=
match sts with
|Single st => SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars curr_lbl curr_env st
| st ~~ tail =>
  match SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars curr_lbl curr_env st with
  | Ret_none => SF_B_P_T_Semantics_stmtl_step_U tail
  | X => X
  end
end
in
match T with
|UVarAssign _ assignee assigned l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => 
    let assigned_ret := eval_aexpr assigned curr_env in
    match assigned_ret with 
    |Error s => Ret_error (String.append "Error while evaluating assigned value : " s )
    |NoError assigned_val => 
      match env_set_var curr_env assignee assigned_val with
      |Error s2 => Ret_error (String.append "Error while updating env : " s2 )
      |NoError ne => 
        match rel_vars with
        |Rel_Vars vars _ =>
          match List.existsb (String.eqb assignee) vars with
          |true => RelevantVar (af A l) ne assignee
          |false => NotRelevant (af A l) ne
          end
        end
      end
    end
  end
|UArrAssign _ assignee index assigned l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => 
    let assigned_ret := eval_aexpr assigned curr_env in
    match assigned_ret with 
    |Error s => Ret_error (String.append "Error while evaluating assigned value : " s )
    |NoError assigned_val => 
      let index_ret := eval_aexpr index curr_env in
      match index_ret with 
      |Error s2 => Ret_error (String.append "Error while evaluating index value : " s2 )
      |NoError index_val => 
        match env_set_arr curr_env assignee index_val assigned_val with
        |Error s3 => Ret_error (String.append "Error while updating env : " s3 )
        |NoError ne => 
          match rel_vars with
          |Rel_Vars _ arrs =>
            match List.existsb (String.eqb assignee) arrs with
            |true => RelevantVar (af A l) ne assignee
            |false => NotRelevant (af A l) ne
            end
          end
        end
      end
    end
  end
|UEmptystmt _ l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => NotRelevant (af A l) curr_env
  end
|UErrorStmt _ l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => Ret_error "Reached error statement"
  end
|UBreak _ l =>
  match lab_eq curr_lbl (atl A l) with
  |false => Ret_none
  |true => NotRelevant (br A l) curr_env
  end
|UIf _ test body l =>
  match lab_eq curr_lbl (atl A l) with
  |false => SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars curr_lbl curr_env body
  |true => 
    let test_ret := eval_bexpr test curr_env in
    match test_ret with 
    |Error s => Ret_error (String.append "Error while evaluating if test : " s )
    |NoError test_val =>
      match test_val with
      |true => 
        let if_body_lbling := get_ustmt_labelling A body in
        NotRelevant (atl A if_body_lbling) curr_env
      |false => NotRelevant (af A l) curr_env
      end
    end
  end
|UIfelse _ test ibody ebody l =>
  match lab_eq curr_lbl (atl A l) with
  |false => 
    let ibody_ret := SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars curr_lbl curr_env ibody in
    match ibody_ret with
    | Ret_none => SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars curr_lbl curr_env ebody
    | _ => ibody_ret
    end
  |true => 
    let test_ret := eval_bexpr test curr_env in
    match test_ret with 
    |Error s => Ret_error (String.append "Error while evaluating if test : " s )
    |NoError test_val =>
      match test_val with
      |true => 
        let if_ibody_lbling := get_ustmt_labelling A ibody in
        NotRelevant (atl A if_ibody_lbling) curr_env
      |false =>
        let if_ebody_lbling := get_ustmt_labelling A ebody in
        NotRelevant (atl A if_ebody_lbling) curr_env
      end
    end
  end
|UCompound _ sts l => SF_B_P_T_Semantics_stmtl_step_U sts
|UBreakable _ sts l => SF_B_P_T_Semantics_stmtl_step_U sts
end
.


Definition SF_B_P_T_Semantics_stmt_step_prefix_U (A: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (program: uprog A) (n: nat) : error (relevant_trace A) :=
match program with
|UProg _ vars sts l => 

  let fix SF_B_P_T_Semantics_stmt_step_prefix_aux_U (k: nat) (prog_body: ustatement A) (lbl: A) (e: env) (acc: ne_list (relevant_state A)) : error (relevant_trace A) := 
  match k with
  |0 => NoError acc
  | S k' =>
    match SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars lbl e prog_body with
    |RelevantVar lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_U k' prog_body lbl2 e2 ((RState A lbl2 e2 true)~~acc)
    |RelevantArr lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_U k' prog_body lbl2 e2 ((RState A lbl2 e2 true)~~acc)
    |NotRelevant lbl2 e2   => SF_B_P_T_Semantics_stmt_step_prefix_aux_U k' prog_body lbl2 e2 ((RState A lbl2 e2 false)~~acc)
    |Ret_error s => Error (String.append "Error while computing prefix : " s)
    |Ret_none => 
      match lab_eq lbl (af A l) with
      |true => NoError acc
      |false => Error "Error while computing prefix : cannot find statement with at label, but end of program not reached"
      end
    end
  end
  in

  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for empty trace"
    | S 0 => NoError ( Single (RState A (atl A l) start_env true))
    | S n' => SF_B_P_T_Semantics_stmt_step_prefix_aux_U n' sts (atl A l) start_env (Single (RState A (atl A l) start_env true))
    end
  end

end
.

Definition SF_B_P_T_Semantics_stmt_step_prefix_nth_U (A: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (program: uprog A) (n: nat) : error (relevant_state A) :=
match program with
|UProg _ vars sts l => 

  let fix SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U (k: nat) (prog_body: ustatement A) (lbl: A) (e: env) (relevant: bool): error (relevant_state A) := 
  match k with
  |0 => NoError (RState A lbl e relevant)
  | S k' =>
    match SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars lbl e prog_body with
    |RelevantVar lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U k' prog_body lbl2 e2 true
    |RelevantArr lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U k' prog_body lbl2 e2 true
    |NotRelevant lbl2 e2   => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U k' prog_body lbl2 e2 false
    |Ret_error s => Error (String.append "Error while computing prefix : " s)
    |Ret_none => 
      match lab_eq lbl (af A l) with
      |true => Error "reached end of unrolled program before finding nth state"
      |false => Error "Error while computing prefix : cannot find statement with at label, but end of program not reached"
      end
    end
  end
  in

  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for 0th state"
    | S 0 => NoError (RState A (atl A l) start_env true)
    | S n' => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U n' sts (atl A l) start_env true
    end
  end

end
.

Definition SF_B_P_T_Semantics_stmt_step_prefix_nth_U_mem (A C: Type) (lab_eq: A->A->bool) (rel_vars: relevant_variables) (program: uprog A) (n: nat) (start_memory: C) (mem_update: (relevant_state A)->C->C) : error (relevant_state_mem A C) :=
match program with
|UProg _ vars sts l => 

  let fix SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U_mem (k: nat) (prog_body: ustatement A) (lbl: A) (e: env) (relevant: bool) (memory: C) : error (relevant_state_mem A C) := 
  match k with
  |0 => NoError (RMState A C lbl e relevant memory)
  | S k' =>
    match SF_B_P_T_Semantics_stmt_step_U A lab_eq rel_vars lbl e prog_body with
    |RelevantVar lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U_mem k' prog_body lbl2 e2 true (mem_update (RState A lbl e relevant) memory)
    |RelevantArr lbl2 e2 _ => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U_mem k' prog_body lbl2 e2 true (mem_update (RState A lbl e relevant) memory)
    |NotRelevant lbl2 e2   => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U_mem k' prog_body lbl2 e2 false (mem_update (RState A lbl e relevant) memory)
    |Ret_error s => Error (String.append "Error while computing prefix : " s)
    |Ret_none => 
      match lab_eq lbl (af A l) with
      |true => NoError (RMState A C lbl e true memory)
      |false => Error "Error while computing prefix : cannot find statement with at label, but end of program not reached"
      end
    end
  end
  in

  match init_env empty_env vars with
  |Error s => Error s
  |NoError start_env =>
    match n with 
    | 0 => Error "Can't ask for 0th state"
    | S 0 => NoError (RMState A C (atl A l) start_env true start_memory)
    | S n' => SF_B_P_T_Semantics_stmt_step_prefix_aux_nth_U_mem n' sts (atl A l) start_env true start_memory
    end
  end

end
.

(*

Eval compute in SF_B_P_T_Semantics_stmt_step_prefix classic_label eq_label (Rel_Vars nil nil) test_prog 10.
Eval compute in SF_B_P_T_Semantics_stmt_step_prefix_nth classic_label eq_label (Rel_Vars nil nil) test_prog 7.

*)
