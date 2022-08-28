Require Import ast.
Require Import environment.
Require Import semantics.
Require Import step_semantics.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.


(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
COMMON
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_eq_relevant_vars : checks if a var_env  is included in another regarding a list of variables
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint var_env_included_relevant_vars (e1 e2: var_env) (rel_vars: list string): bool :=
match e1, e2 with
| nil , _ => true
| _ :: _ , nil => false
| entry1::tail , _ :: _ => 
  match entry1 with
  |VarEntry id _ =>
    match List.existsb ( String.eqb id ) rel_vars with
    |false => var_env_included_relevant_vars tail e2 rel_vars
    |true =>
      match List.existsb (var_entry_eqb entry1 ) e2 with
      |true => var_env_included_relevant_vars tail e2 rel_vars
      |false => false
      end
    end
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_env_eq_relevant_vars : checks if an arr_env  is included in another regarding a list of variables
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint arr_env_included_relevant_vars (e1 e2: arr_env) (rel_vars: list string): bool :=
match e1, e2 with
| nil , _ => true
| _ :: _ , nil => false
| entry1::tail , _ :: _ => 
  match entry1 with
  |ArrEntry id _ _ =>
    match List.existsb ( String.eqb id ) rel_vars with
    |false => arr_env_included_relevant_vars tail e2 rel_vars
    |true =>
      match List.existsb (arr_entry_eqb entry1 ) e2 with
      |true => arr_env_included_relevant_vars tail e2 rel_vars
      |false => false
      end
    end
  end
end.


(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_eq_relevant_vars : checks if two envs are equal regarding a list of variables
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_eq_relevant_vars (e1 e2: env) (rel_vars: relevant_variables) : bool :=
match e1, e2 with
|Env v1 a1, Env v2 a2 =>
  match rel_vars with
  |Rel_Vars vars arrs => 
    (var_env_included_relevant_vars v1 v2 vars) && (var_env_included_relevant_vars v2 v1 vars)
    && (arr_env_included_relevant_vars a1 a2 arrs) && (arr_env_included_relevant_vars a2 a1 arrs)
  end
end.

Definition states_are_equivalent {A B C: Type} (s1: relevant_state A) (s2: relevant_state B) (memory: C) (lab_eq_u: B->B->bool) (projection_func: A->C->B) (rel_vars: relevant_variables): bool :=
match s1, s2 with
|RState _ lbl e1 _ , RState _ lbl2 e2 r =>andb (env_eq_relevant_vars e1 e2 rel_vars) (lab_eq_u lbl2 (projection_func lbl memory))  (* check here for relevancy*)
end.

Theorem error_neq_noerror : forall (A: Type), forall (s: string), forall (x: A),
Error s <> NoError x
.
Proof.
intros. discriminate.
Qed.

Theorem noerror_eq : forall (A: Type), forall (x y: A),
NoError x = NoError y
-> 
x = y
.
Proof.
intros.
inversion H.
reflexivity.
Qed.

Inductive equ_ret:=
|Equ_ret (is_eq: bool) (n:nat).

Theorem equret_eq : forall (x y: bool), forall (n m : nat),
Equ_ret x n = Equ_ret y m
-> 
x = y /\ n=m
.
Proof.
intros.
inversion H.
split.
reflexivity.
reflexivity.
Qed.

Theorem rmstate_eq :
forall A, forall C, forall l1, forall l2, forall e1, forall e2, forall r1, forall r2, forall m1, forall m2,

RMState A C l1 e1 r1 m1 = RMState A C l2 e2 r2 m2
->
l1 = l2
/\
e1 = e2
/\
r1 = r2
/\
m1 = m2
.
Proof.
intros.
inversion H.
repeat split.
Qed.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
UNROLLED IS EQUIVALENT TO SOURCE
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)

Definition n_is_equivalent_u {A B C: Type} (source_state: relevant_state A) (unrolled: uprog B) (memory: C) (lab_eq_u: B->B->bool) (projection_func: A->C->B) (rel_vars: relevant_variables) (n: nat): error bool :=
let current_state := SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled n in
match current_state with
| NoError c_state =>
  NoError (states_are_equivalent source_state c_state memory lab_eq_u projection_func rel_vars)
| Error s => Error (String.append "Error while testing equivalence of nth state in unrolled : " s)
end
.

Theorem n_equivalent_u_to_witness :
forall (A B C : Type), forall (unrolled: uprog B), forall (source_state: relevant_state A), forall (rel_vars: relevant_variables), forall (memory: C),
forall (projection_func: A->C->B),
forall (lab_eq_u: B->B->bool), forall (n: nat),

n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars n = NoError true

-> 
(
exists s, 
SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled n = NoError s
/\
states_are_equivalent source_state s memory lab_eq_u projection_func rel_vars = true
)
.
Proof.
intros.
unfold n_is_equivalent_u in H.
edestruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled n).
+ apply error_neq_noerror in H. contradiction.
+ exists val.
  split. reflexivity.
  apply noerror_eq in H.
  assumption.
Qed.

Fixpoint search_equivalent_in_unrolled {A B C: Type} (unrolled: uprog B) (source_state: relevant_state A) (memory: C) (lab_eq_u: B->B->bool) (projection_func: A->C->B) (rel_vars: relevant_variables) (curr_depth: nat) (n: nat) : error equ_ret :=
match curr_depth with
| 0 => 
  match n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars n with
  |Error s => Error (String.append "Error while looking for equivalent : " s)
  |NoError b => NoError (Equ_ret b n)
  end
| S new_depth =>
  match n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars (n + curr_depth) with
    |Error s => Error (String.append "Error while looking for equivalent : " s)
    |NoError true => NoError (Equ_ret true (n+curr_depth))
    |NoError false => search_equivalent_in_unrolled unrolled source_state memory lab_eq_u projection_func rel_vars new_depth n
  end
end.

Theorem search_equivalent_cases_u:
forall (A B C : Type), forall (unrolled: uprog B), forall (source_state: relevant_state A), forall (rel_vars: relevant_variables), forall (memory: C),
forall (projection_func: A->C->B),
forall (lab_eq_u: B->B->bool), forall (n: nat), forall (k:nat),forall (curr_depth : nat),

search_equivalent_in_unrolled unrolled source_state memory lab_eq_u projection_func rel_vars (S curr_depth) n = NoError (Equ_ret true k )
->
search_equivalent_in_unrolled unrolled source_state memory lab_eq_u projection_func rel_vars curr_depth n = NoError (Equ_ret true k )
\/
( n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars (n + (S curr_depth)) = NoError true
/\ (n + (S curr_depth) = k)
)
.
Proof.
induction curr_depth.
+ intro.
  unfold search_equivalent_in_unrolled in H.
  destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars (n + 1)) eqn:Hneq in H.
  - apply error_neq_noerror in H. contradiction.
  - destruct val eqn:Hval in H.
    * apply noerror_eq in H. apply equret_eq in H. destruct H.
      rewrite Hval in Hneq. right. split. assumption. assumption.
    * destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars n) eqn:Hneq0 in H.
      (*1*)    apply error_neq_noerror in H. contradiction.
      (*2*)    unfold search_equivalent_in_unrolled.
               destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars n).
               apply error_neq_noerror in Hneq0. contradiction.
               apply noerror_eq in Hneq0. rewrite Hneq0. left ; assumption.
+ intro.
  unfold search_equivalent_in_unrolled in H.
  destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars (n + S (S curr_depth))) eqn:HSSneq in H.
  - apply error_neq_noerror in H ; contradiction.
  - destruct val eqn:Hval in H.
    * right. rewrite Hval in HSSneq. apply noerror_eq in H. apply equret_eq in H. destruct H.
      split ; assumption ; assumption.
    * left.
      unfold search_equivalent_in_unrolled. assumption.
Qed.

Theorem search_equivalent_increasing_u:
forall (A B C : Type), forall (unrolled: uprog B), forall (source_state: relevant_state A), forall (rel_vars: relevant_variables), forall (memory: C),
forall (projection_func: A->C->B),
forall (lab_eq_u: B->B->bool), forall (n: nat), forall (k:nat),forall (curr_depth : nat), 


search_equivalent_in_unrolled unrolled source_state memory lab_eq_u projection_func rel_vars curr_depth n = NoError (Equ_ret true k )


-> 

n <= k
.
Proof.
induction curr_depth.
- intro. unfold search_equivalent_in_unrolled in H.
  destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars n) in H.
  apply error_neq_noerror in H; contradiction.
  destruct val.
  + apply noerror_eq in H. apply equret_eq in H. destruct H. rewrite H0. apply le_n.
  + apply noerror_eq in H. apply equret_eq in H. destruct H. discriminate H.
- intros.
  unfold search_equivalent_in_unrolled in H.
  destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars (n + S curr_depth)) eqn:Hneq in H.
  + apply error_neq_noerror in H ; contradiction.
  + destruct val.
    * apply noerror_eq in H. apply equret_eq in H. destruct H. rewrite <- H0.
      apply Nat.le_add_r.
    * apply IHcurr_depth in H. assumption.
Qed.

Theorem search_equivalent_witness_u:
forall (A B C : Type), forall (unrolled: uprog B), forall (source_state: relevant_state A), forall (rel_vars: relevant_variables), forall (memory: C),
forall (projection_func: A->C->B),
forall (lab_eq_u: B->B->bool), forall (n: nat), forall (k:nat),forall (curr_depth : nat), 


search_equivalent_in_unrolled unrolled source_state memory lab_eq_u projection_func rel_vars curr_depth n = NoError (Equ_ret true k )


-> 

n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars k = NoError true
.

Proof.
induction curr_depth.
+ intro.
  unfold search_equivalent_in_unrolled in H.
  destruct (n_is_equivalent_u source_state unrolled memory lab_eq_u projection_func rel_vars n) eqn:Hneq in H.
  - apply error_neq_noerror in H. contradiction.
  - apply noerror_eq in H. apply equret_eq in H. 
    destruct H. rewrite H in Hneq. rewrite H0 in Hneq. assumption.
+ intro. apply search_equivalent_cases_u in H. destruct H.
  - apply IHcurr_depth in H. assumption.
  - destruct H. rewrite H0 in H. assumption.
Qed.

Fixpoint step_semantics_eq_prover_u (A B C: Type) (p: prog A) (up: uprog B) (rel_vars: relevant_variables) (start_memory: C) (mem_update: (relevant_state A)->C->C) (projection_func: A->C->B) (lab_eq_s: A->A->bool) (lab_eq_u: B->B->bool) (plength: nat) (max_depth: nat): error equ_ret :=
match plength with
|0 => NoError (Equ_ret true 0)
|S new_plength => 
  match step_semantics_eq_prover_u A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u new_plength max_depth with
  |Error s => Error (String.append "Error while trying to prove unrolled equivalence : " s)
  |NoError (Equ_ret false k) => NoError (Equ_ret false k)
  |NoError (Equ_ret true k) =>
    match SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars p plength start_memory mem_update with
    |Error s => Error (String.append "Error while stepping in source while trying to prove unrolled equivalence : " s)
    |NoError rmstate =>
      match rmstate with
      |RMState _ _ _ _ false mem => NoError (Equ_ret true k) 
      |RMState _ _ l e true mem => search_equivalent_in_unrolled up (RState A l e true) mem lab_eq_u projection_func rel_vars max_depth (S k) 
      end
    end
  end
end
.


Theorem prover_0_true_u :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat),

step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u 0 max_depth = NoError (Equ_ret true 0)
.
Proof.
intros. unfold step_semantics_eq_prover_u. reflexivity.
Qed.

Theorem prover_Sn_implies_n_u :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,

step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u (S prefix_length) max_depth= NoError (Equ_ret true n)

->
(exists n',
step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n')
)
.
Proof.
induction prefix_length.
+ intros. unfold step_semantics_eq_prover_u. exists 0. split.
+ intros.
  unfold step_semantics_eq_prover_u in H.


  unfold step_semantics_eq_prover_u.
  destruct
  (
   match
        (fix step_semantics_eq_prover_u
           (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables) (start_memory : C) (mem_update : relevant_state A -> C -> C)
           (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool) (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} :
             error equ_ret :=
           match plength with
           | 0 => NoError (Equ_ret true 0)
           | S new_plength =>
               match step_semantics_eq_prover_u A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u new_plength max_depth with
               | Error s => Error ("Error while trying to prove unrolled equivalence : " ++ s)
               | NoError (Equ_ret true k) =>
                   match SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars p plength start_memory mem_update with
                   | Error s => Error ("Error while stepping in source while trying to prove unrolled equivalence : " ++ s)
                   | NoError (RMState _ _ l e true mem) =>
                       search_equivalent_in_unrolled up (RState A l e true) mem lab_eq_u projection_func rel_vars max_depth (S k)
                   | NoError (RMState _ _ l e false _) => NoError (Equ_ret true k)
                   end
               | NoError (Equ_ret false k) => NoError (Equ_ret false k)
               end
           end) A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth
      with
      | Error s => Error ("Error while trying to prove unrolled equivalence : " ++ s)
      | NoError (Equ_ret true k) =>
          match SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source (S prefix_length) start_memory mem_update with
          | Error s => Error ("Error while stepping in source while trying to prove unrolled equivalence : " ++ s)
          | NoError (RMState _ _ l e true mem) =>
              search_equivalent_in_unrolled unrolled (RState A l e true) mem lab_eq_u projection_func rel_vars max_depth (S k)
          | NoError (RMState _ _ l e false _) => NoError (Equ_ret true k)
          end
      | NoError (Equ_ret false k) => NoError (Equ_ret false k)
      end
  ) eqn:Hfix in H.
  - apply error_neq_noerror in H. contradiction.
  - destruct val eqn:Hval in H.
    destruct is_eq.
    * exists n0. rewrite Hval in Hfix. assumption.
    * apply noerror_eq in H. apply equret_eq in H. destruct H. discriminate H.
Qed.

Theorem prover_witness_u :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,
forall l, forall e, forall mem,

0 < prefix_length
/\
step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n)
/\
(SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source prefix_length start_memory mem_update = NoError (RMState _ _ l e true mem))
->

n_is_equivalent_u (RState _ l e true) unrolled mem lab_eq_u projection_func rel_vars n = NoError true

.
Proof.
induction prefix_length.
intros.
- destruct H. apply Nat.nlt_0_r in H. contradiction.
- intros.
  destruct H. destruct H0.
  unfold step_semantics_eq_prover_u in H0.
  destruct ((fix step_semantics_eq_prover_u
          (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables) (start_memory : C)
          (mem_update : relevant_state A -> C -> C) (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
          (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} : error equ_ret :=
          match plength with
          | 0 => NoError (Equ_ret true 0)
          | S new_plength =>
              match
                step_semantics_eq_prover_u A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u
                  new_plength max_depth
              with
              | Error s => Error ("Error while trying to prove unrolled equivalence : " ++ s)
              | NoError (Equ_ret true k) =>
                  match
                    SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars p plength start_memory mem_update
                  with
                  | Error s =>
                      Error ("Error while stepping in source while trying to prove unrolled equivalence : " ++ s)
                  | NoError (RMState _ _ l e true mem) =>
                      search_equivalent_in_unrolled up (RState A l e true) mem lab_eq_u projection_func rel_vars
                        max_depth (S k)
                  | NoError (RMState _ _ l e false _) => NoError (Equ_ret true k)
                  end
              | NoError (Equ_ret false k) => NoError (Equ_ret false k)
              end
          end) A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length
         max_depth) in H0.
  + apply error_neq_noerror in H0 ; contradiction.
  + destruct val eqn:Hval in H0.
    destruct is_eq eqn:His_eq in H0.
    destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source (S prefix_length) start_memory
         mem_update) eqn:HSpl in H0.
    * rewrite HSpl in H1. apply error_neq_noerror in H1. contradiction.
    * destruct val0 eqn:Hval0 in H0.
      destruct relevant eqn:Hrelevant in H0.
      1:{
        rewrite HSpl in H1. rewrite Hval0 in H1. 
        apply noerror_eq in H1. rewrite Hrelevant in H1. apply rmstate_eq in H1.
        destruct H1. destruct H2. destruct H3.
        rewrite H4 in H0.
        apply search_equivalent_witness_u in H0. rewrite H1 in H0. rewrite H2 in H0. assumption.
      }
      1:{
        rewrite HSpl in H1. rewrite Hval0 in H1. 
        rewrite Hrelevant in H1.
        apply noerror_eq in H1. apply rmstate_eq in H1. destruct H1; destruct H2; destruct H3.
        discriminate H3.
      }
    * apply noerror_eq in H0 ; apply equret_eq in H0. destruct H0 ; discriminate H0.
Qed.

Theorem prover_irrelevant_eq_u :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,
forall l, forall e, forall mem,

step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u (S prefix_length) max_depth = NoError (Equ_ret true n)
/\
(SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source (S prefix_length) start_memory mem_update = NoError (RMState _ _ l e false mem))
->

step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n)

.
Proof.
intros. destruct H.
unfold step_semantics_eq_prover_u in H.
destruct
(
(fix step_semantics_eq_prover_u
         (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables) (start_memory : C)
         (mem_update : relevant_state A -> C -> C) (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
         (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} : error equ_ret :=
         match plength with
         | 0 => NoError (Equ_ret true 0)
         | S new_plength =>
             match
               step_semantics_eq_prover_u A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u
                 new_plength max_depth
             with
             | Error s => Error ("Error while trying to prove unrolled equivalence : " ++ s)
             | NoError (Equ_ret true k) =>
                 match
                   SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars p plength start_memory mem_update
                 with
                 | Error s =>
                     Error ("Error while stepping in source while trying to prove unrolled equivalence : " ++ s)
                 | NoError (RMState _ _ l e true mem) =>
                     search_equivalent_in_unrolled up (RState A l e true) mem lab_eq_u projection_func rel_vars
                       max_depth (S k)
                 | NoError (RMState _ _ l e false _) => NoError (Equ_ret true k)
                 end
             | NoError (Equ_ret false k) => NoError (Equ_ret false k)
             end
         end) A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length
        max_depth
) eqn:Hfix in H.
- apply error_neq_noerror in H. contradiction.
- destruct val eqn:Hval in H.
  destruct is_eq eqn:His_eq in H.
  + destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source (S prefix_length) start_memory
        mem_update) eqn:HSpn in H.
     (*1*) apply error_neq_noerror in H. contradiction.
     (*2*) destruct val0 eqn:Hval0 in H.
           destruct relevant.
           * rewrite HSpn in H0. rewrite Hval0 in H0.
             apply noerror_eq in H0; apply rmstate_eq in H0.
             destruct H0. destruct H1. destruct H2. discriminate H2.
           * apply noerror_eq in H; apply equret_eq in H ; destruct H.
             rewrite H1 in Hval ; rewrite His_eq in Hval. rewrite Hval in Hfix. assumption.
  + apply noerror_eq in H; apply equret_eq in H ; destruct H. discriminate H.
Qed.

Theorem prover_relevant_gt_u :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,
forall l, forall e, forall mem,

step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u (S prefix_length) max_depth = NoError (Equ_ret true n)
/\
(SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source (S prefix_length) start_memory mem_update = NoError (RMState _ _ l e true mem))
->
(exists n',
step_semantics_eq_prover_u A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n')
/\ n' < n
)
.
Proof.
intros.
destruct H.
unfold step_semantics_eq_prover_u in H.
destruct
(
(fix step_semantics_eq_prover_u
         (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables) (start_memory : C)
         (mem_update : relevant_state A -> C -> C) (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
         (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} : error equ_ret :=
         match plength with
         | 0 => NoError (Equ_ret true 0)
         | S new_plength =>
             match
               step_semantics_eq_prover_u A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u
                 new_plength max_depth
             with
             | Error s => Error ("Error while trying to prove unrolled equivalence : " ++ s)
             | NoError (Equ_ret true k) =>
                 match
                   SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars p plength start_memory mem_update
                 with
                 | Error s =>
                     Error ("Error while stepping in source while trying to prove unrolled equivalence : " ++ s)
                 | NoError (RMState _ _ l e true mem) =>
                     search_equivalent_in_unrolled up (RState A l e true) mem lab_eq_u projection_func rel_vars
                       max_depth (S k)
                 | NoError (RMState _ _ l e false _) => NoError (Equ_ret true k)
                 end
             | NoError (Equ_ret false k) => NoError (Equ_ret false k)
             end
         end) A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length
        max_depth
) eqn:Hfix in H.
- apply error_neq_noerror in H. contradiction.
- destruct val eqn:Hval in H.
  destruct is_eq eqn:His_eq in H.
  + destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source (S prefix_length) start_memory
        mem_update) eqn:HSpn in H.
    (*1*)rewrite HSpn in H0. apply error_neq_noerror in H0. contradiction.
    (*2*)destruct val0 eqn:Hval0 in H. destruct relevant.
        * apply search_equivalent_increasing_u in H.
          rewrite His_eq in Hval. rewrite Hval in Hfix.
          exists n0.
          split.
          (*1*) assumption.
          (*2*) auto.

        *  rewrite HSpn in H0. rewrite Hval0 in H0.
           apply noerror_eq in H0.
           inversion H0.
  + inversion H.
Qed.






(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
SOURCE IS EQUIVALENT TO UNROLLED
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)

Definition n_is_equivalent_s {A B C: Type} (unrolled_state: relevant_state B) (source: prog A) (start_memory: C) (lab_eq_s: A->A->bool) (lab_eq_u: B->B->bool) (mem_update: (relevant_state A)->C->C) (projection_func: A->C->B) (rel_vars: relevant_variables) (n: nat): error bool :=
let current_state := SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source n start_memory mem_update in
match current_state with
| NoError (RMState _ _ lbl e rel mem) =>
  NoError (states_are_equivalent (RState _ lbl e rel) unrolled_state mem lab_eq_u projection_func rel_vars)
| Error s => Error (String.append "Error while testing equivalence of nth state in unrolled : " s)
end
.

Theorem n_equivalent_s_to_witness :
forall (A B C : Type), forall (source: prog A), forall (unrolled_state: relevant_state B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (projection_func: A->C->B), forall (lab_eq_s: A->A->bool), forall (mem_update: (relevant_state A)->C->C),
forall (lab_eq_u: B->B->bool), forall (n: nat),

n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars n = NoError true

-> 
(
exists s,
SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source n start_memory mem_update = NoError s
/\
(
match s with
|RMState _ _ lbl e rel mem => states_are_equivalent (RState A lbl e rel) unrolled_state mem lab_eq_u projection_func rel_vars = true
end
)
)
.
Proof.
intros.
unfold n_is_equivalent_s in H.
destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_mem A C lab_eq_s rel_vars source n start_memory mem_update) eqn:Hnthm.
+ apply error_neq_noerror in H. contradiction.
+ destruct val eqn:Hval. exists val.
  split. rewrite Hval. reflexivity.
  destruct val eqn:Hval1.
  apply noerror_eq in H. inversion Hval. auto.
Qed.

Fixpoint search_equivalent_in_source {A B C: Type} (source: prog A) (unrolled_state: relevant_state B) (start_memory: C) (lab_eq_s: A->A->bool) (lab_eq_u: B->B->bool) (mem_update: (relevant_state A)->C->C) (projection_func: A->C->B) (rel_vars: relevant_variables) (curr_depth: nat) (n: nat) : error equ_ret :=
match curr_depth with
| 0 => 
  match n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars n with
  |Error s => Error (String.append "Error while looking for equivalent : " s)
  |NoError b => NoError (Equ_ret b n)
  end
| S new_depth =>
  match n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars (n + curr_depth) with
    |Error s => Error (String.append "Error while looking for equivalent : " s)
    |NoError true => NoError (Equ_ret true (n+curr_depth))
    |NoError false => search_equivalent_in_source source unrolled_state start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars new_depth n
  end
end.

Theorem search_equivalent_cases_s:
forall (A B C : Type), forall (source: prog A), forall (unrolled_state: relevant_state B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (projection_func: A->C->B), forall (lab_eq_s: A->A->bool), forall (mem_update: (relevant_state A)->C->C),
forall (lab_eq_u: B->B->bool), forall (n: nat), forall (k:nat),forall (curr_depth : nat),

search_equivalent_in_source source unrolled_state start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars (S curr_depth) n = NoError (Equ_ret true k )
->
search_equivalent_in_source source unrolled_state start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars curr_depth n = NoError (Equ_ret true k )
\/
( n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars (n + (S curr_depth)) = NoError true
/\ (n + (S curr_depth) = k)
)
.
Proof.
induction curr_depth.
+ intro.
  unfold search_equivalent_in_source in H.
  destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update
        projection_func rel_vars (n + 1)) eqn:Hneq in H.
  - apply error_neq_noerror in H. contradiction.
  - destruct val eqn:Hval in H.
    * apply noerror_eq in H. apply equret_eq in H. destruct H.
      rewrite Hval in Hneq. right. split. assumption. assumption.
    * destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update
        projection_func rel_vars n) eqn:Hneq0 in H.
      (*1*)    apply error_neq_noerror in H. contradiction.
      (*2*)    unfold search_equivalent_in_source.
               destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update
    projection_func rel_vars n).
               apply error_neq_noerror in Hneq0. contradiction.
               apply noerror_eq in Hneq0. rewrite Hneq0. left ; assumption.
+ intro.
  unfold search_equivalent_in_source in H.
  destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update
        projection_func rel_vars (n + S (S curr_depth))) eqn:HSSneq in H.
  - apply error_neq_noerror in H ; contradiction.
  - destruct val eqn:Hval in H.
    * right. rewrite Hval in HSSneq. apply noerror_eq in H. apply equret_eq in H. destruct H.
      split ; assumption ; assumption.
    * left.
      unfold search_equivalent_in_source. assumption.
Qed.

Theorem search_equivalent_increasing_s:
forall (A B C : Type), forall (source: prog A), forall (unrolled_state: relevant_state B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (projection_func: A->C->B), forall (lab_eq_s: A->A->bool),  forall (mem_update: (relevant_state A)->C->C),
forall (lab_eq_u: B->B->bool), forall (n: nat), forall (k:nat),forall (curr_depth : nat), 


search_equivalent_in_source source unrolled_state start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars curr_depth n = NoError (Equ_ret true k )


-> 

n <= k
.
Proof.
induction curr_depth.
- intro. unfold search_equivalent_in_source in H.
  destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update
        projection_func rel_vars n) in H.
  apply error_neq_noerror in H; contradiction.
  destruct val.
  + apply noerror_eq in H. apply equret_eq in H. destruct H. rewrite H0. apply le_n.
  + apply noerror_eq in H. apply equret_eq in H. destruct H. discriminate H.
- intros.
  unfold search_equivalent_in_source in H.
  destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars (n + S curr_depth)) eqn:Hneq in H.
  + apply error_neq_noerror in H ; contradiction.
  + destruct val.
    * apply noerror_eq in H. apply equret_eq in H. destruct H. rewrite <- H0.
      apply Nat.le_add_r.
    * apply IHcurr_depth in H. assumption.
Qed.

Theorem search_equivalent_witness_s:
forall (A B C : Type), forall (source: prog A), forall (unrolled_state: relevant_state B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (projection_func: A->C->B), forall (lab_eq_s: A->A->bool), forall (mem_update: (relevant_state A)->C->C),
forall (lab_eq_u: B->B->bool), forall (n: nat), forall (k:nat),forall (curr_depth : nat), 


search_equivalent_in_source source unrolled_state start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars curr_depth n = NoError (Equ_ret true k )


-> 

n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars k = NoError true
.

Proof.
induction curr_depth.
+ intro.
  unfold search_equivalent_in_source in H.
  destruct (n_is_equivalent_s unrolled_state source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars n) eqn:Hneq in H.
  - apply error_neq_noerror in H. contradiction.
  - apply noerror_eq in H. apply equret_eq in H. 
    destruct H. rewrite H in Hneq. rewrite H0 in Hneq. assumption.
+ intro. apply search_equivalent_cases_s in H. destruct H.
  - apply IHcurr_depth in H. assumption.
  - destruct H. rewrite H0 in H. assumption.
Qed.


Fixpoint step_semantics_eq_prover_s (A B C: Type) (p: prog A) (up: uprog B) (rel_vars: relevant_variables) (start_memory: C) (mem_update: (relevant_state A)->C->C) (projection_func: A->C->B) (lab_eq_s: A->A->bool) (lab_eq_u: B->B->bool) (plength: nat) (max_depth: nat): error equ_ret :=
match plength with
|0 => NoError (Equ_ret true 0)
|S new_plength => 
  match step_semantics_eq_prover_s A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u new_plength max_depth with
  |Error s => Error (String.append "Error while trying to prove unrolled equivalence : " s)
  |NoError (Equ_ret false k) => NoError (Equ_ret false k)
  |NoError (Equ_ret true k) =>
    match SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars up plength with
    |Error s => Error (String.append "Error while stepping in source while trying to prove unrolled equivalence : " s)
    |NoError rstate =>
      match rstate with
      |RState _  _ _ false => NoError (Equ_ret true k) 
      |RState _  l e true  => search_equivalent_in_source p rstate start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars max_depth (S k) 
      end
    end
  end
end
.


Theorem prover_0_true_s :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat),

step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u 0 max_depth = NoError (Equ_ret true 0)
.
Proof.
intros. unfold step_semantics_eq_prover_u. reflexivity.
Qed.

Theorem prover_Sn_implies_n_s :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,

step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u (S prefix_length) max_depth= NoError (Equ_ret true n)

->
(exists n',
step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n')
)
.
Proof.
induction prefix_length.
+ intros. unfold step_semantics_eq_prover_s. exists 0. split.
+ intros.
  unfold step_semantics_eq_prover_s in H.
  destruct
  (
    match
        (fix step_semantics_eq_prover_s
           (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables)
           (start_memory : C) (mem_update : relevant_state A -> C -> C)
           (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
           (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} :
             error equ_ret :=
           match plength with
           | 0 => NoError (Equ_ret true 0)
           | S new_plength =>
               match
                 step_semantics_eq_prover_s A B C p up rel_vars start_memory mem_update
                   projection_func lab_eq_s lab_eq_u new_plength max_depth
               with
               | Error s =>
                   Error ("Error while trying to prove unrolled equivalence : " ++ s)
               | NoError (Equ_ret true k) =>
                   match
                     SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars up
                       plength
                   with
                   | Error s =>
                       Error
                         ("Error while stepping in source while trying to prove unrolled equivalence : " ++
                          s)
                   | NoError (RState _ _ _ true as rstate) =>
                       search_equivalent_in_source p rstate start_memory lab_eq_s lab_eq_u
                         mem_update projection_func rel_vars max_depth 
                         (S k)
                   | NoError (RState _ _ _ false) => NoError (Equ_ret true k)
                   end
               | NoError (Equ_ret false k) => NoError (Equ_ret false k)
               end
           end) A B C source unrolled rel_vars start_memory mem_update projection_func
          lab_eq_s lab_eq_u prefix_length max_depth
      with
      | Error s => Error ("Error while trying to prove unrolled equivalence : " ++ s)
      | NoError (Equ_ret true k) =>
          match
            SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled
              (S prefix_length)
          with
          | Error s =>
              Error
                ("Error while stepping in source while trying to prove unrolled equivalence : " ++
                 s)
          | NoError (RState _ _ _ true as rstate) =>
              search_equivalent_in_source source rstate start_memory lab_eq_s lab_eq_u
                mem_update projection_func rel_vars max_depth (S k)
          | NoError (RState _ _ _ false) => NoError (Equ_ret true k)
          end
      | NoError (Equ_ret false k) => NoError (Equ_ret false k)
      end
  ) eqn:Hfix in H.
  - apply error_neq_noerror in H. contradiction.
  - destruct val eqn:Hval in H.
    destruct is_eq.
    * exists n0. rewrite Hval in Hfix. assumption.
    * apply noerror_eq in H. apply equret_eq in H. destruct H. discriminate H.
Qed.

Theorem prover_witness_s :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,
forall l, forall e,

0 < prefix_length
/\
step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n)
/\
(SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled prefix_length = NoError (RState _ l e true))
->

n_is_equivalent_s (RState _ l e true) source start_memory lab_eq_s lab_eq_u mem_update projection_func rel_vars n = NoError true

.
Proof.
induction prefix_length.
intros.
- destruct H. apply Nat.nlt_0_r in H. contradiction.
- intros.
  destruct H. destruct H0.
  unfold step_semantics_eq_prover_s in H0.
  destruct 
  (
  (fix step_semantics_eq_prover_s
          (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables)
          (start_memory : C) (mem_update : relevant_state A -> C -> C)
          (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
          (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} :
            error equ_ret :=
          match plength with
          | 0 => NoError (Equ_ret true 0)
          | S new_plength =>
              match
                step_semantics_eq_prover_s A B C p up rel_vars start_memory mem_update
                  projection_func lab_eq_s lab_eq_u new_plength max_depth
              with
              | Error s =>
                  Error ("Error while trying to prove unrolled equivalence : " ++ s)
              | NoError (Equ_ret true k) =>
                  match
                    SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars up
                      plength
                  with
                  | Error s =>
                      Error
                        ("Error while stepping in source while trying to prove unrolled equivalence : " ++
                         s)
                  | NoError (RState _ _ _ true as rstate) =>
                      search_equivalent_in_source p rstate start_memory lab_eq_s lab_eq_u
                        mem_update projection_func rel_vars max_depth 
                        (S k)
                  | NoError (RState _ _ _ false) => NoError (Equ_ret true k)
                  end
              | NoError (Equ_ret false k) => NoError (Equ_ret false k)
              end
          end) A B C source unrolled rel_vars start_memory mem_update projection_func
         lab_eq_s lab_eq_u prefix_length max_depth
  ) in H0.
  + apply error_neq_noerror in H0 ; contradiction.
  + destruct val eqn:Hval in H0.
    destruct is_eq eqn:His_eq in H0.
    destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled
         (S prefix_length)) eqn:HSpl in H0.
    * rewrite HSpl in H1. apply error_neq_noerror in H1. contradiction.
    * destruct val0 eqn:Hval0 in H0.
      destruct relevant eqn:Hrelevant in H0.
      1:{
        rewrite HSpl in H1. rewrite Hval0 in H1. 
        apply noerror_eq in H1. rewrite Hrelevant in H1. rewrite H1 in H0.
        apply search_equivalent_witness_s in H0. assumption.
      }
      1:{
        rewrite HSpl in H1. rewrite Hval0 in H1. 
        rewrite Hrelevant in H1.
        apply noerror_eq in H1. inversion H1.
      }
    * apply noerror_eq in H0 ; apply equret_eq in H0. destruct H0 ; discriminate H0.
Qed.

Theorem prover_irrelevant_eq_s :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,
forall l, forall e,

step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u (S prefix_length) max_depth = NoError (Equ_ret true n)
/\
(SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled (S prefix_length) = NoError (RState _ l e false))
->

step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n)

.
Proof.
intros. destruct H.
unfold step_semantics_eq_prover_s in H.
destruct
(
(fix step_semantics_eq_prover_s
         (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables)
         (start_memory : C) (mem_update : relevant_state A -> C -> C)
         (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
         (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} :
           error equ_ret :=
         match plength with
         | 0 => NoError (Equ_ret true 0)
         | S new_plength =>
             match
               step_semantics_eq_prover_s A B C p up rel_vars start_memory mem_update
                 projection_func lab_eq_s lab_eq_u new_plength max_depth
             with
             | Error s =>
                 Error ("Error while trying to prove unrolled equivalence : " ++ s)
             | NoError (Equ_ret true k) =>
                 match
                   SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars up plength
                 with
                 | Error s =>
                     Error
                       ("Error while stepping in source while trying to prove unrolled equivalence : " ++
                        s)
                 | NoError (RState _ _ _ true as rstate) =>
                     search_equivalent_in_source p rstate start_memory lab_eq_s lab_eq_u
                       mem_update projection_func rel_vars max_depth 
                       (S k)
                 | NoError (RState _ _ _ false) => NoError (Equ_ret true k)
                 end
             | NoError (Equ_ret false k) => NoError (Equ_ret false k)
             end
         end) A B C source unrolled rel_vars start_memory mem_update projection_func
        lab_eq_s lab_eq_u prefix_length max_depth
) eqn:Hfix in H.
- apply error_neq_noerror in H. contradiction.
- destruct val eqn:Hval in H.
  destruct is_eq eqn:His_eq in H.
  + destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled
        (S prefix_length)) eqn:HSpn in H.
     (*1*) apply error_neq_noerror in H. contradiction.
     (*2*) destruct val0 eqn:Hval0 in H.
           destruct relevant.
           * rewrite HSpn in H0. rewrite Hval0 in H0. inversion H0.
           * apply noerror_eq in H; apply equret_eq in H ; destruct H.
             rewrite H1 in Hval ; rewrite His_eq in Hval. rewrite Hval in Hfix. assumption.
  + apply noerror_eq in H; apply equret_eq in H ; destruct H. discriminate H.
Qed.

Theorem prover_relevant_gt_s :
forall (A B C : Type), forall (source: prog A), forall (unrolled: uprog B), forall (rel_vars: relevant_variables), forall (start_memory: C),
forall (mem_update: (relevant_state A)->C->C), forall (projection_func: A->C->B),
forall (lab_eq_s: A->A->bool), forall (lab_eq_u: B->B->bool), forall (max_depth: nat), forall (prefix_length: nat),
forall n,
forall l, forall e,

step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u (S prefix_length) max_depth = NoError (Equ_ret true n)
/\
(SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled (S prefix_length)  = NoError (RState _ l e true))
->
(exists n',
step_semantics_eq_prover_s A B C source unrolled rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u prefix_length max_depth = NoError (Equ_ret true n')
/\ n' < n
)
.
Proof.
intros.
destruct H.
unfold step_semantics_eq_prover_s in H.
destruct
(
(fix step_semantics_eq_prover_s
         (A B C : Type) (p : prog A) (up : uprog B) (rel_vars : relevant_variables)
         (start_memory : C) (mem_update : relevant_state A -> C -> C)
         (projection_func : A -> C -> B) (lab_eq_s : A -> A -> bool)
         (lab_eq_u : B -> B -> bool) (plength max_depth : nat) {struct plength} :
           error equ_ret :=
         match plength with
         | 0 => NoError (Equ_ret true 0)
         | S new_plength =>
             match
               step_semantics_eq_prover_s A B C p up rel_vars start_memory mem_update
                 projection_func lab_eq_s lab_eq_u new_plength max_depth
             with
             | Error s =>
                 Error ("Error while trying to prove unrolled equivalence : " ++ s)
             | NoError (Equ_ret true k) =>
                 match
                   SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars up plength
                 with
                 | Error s =>
                     Error
                       ("Error while stepping in source while trying to prove unrolled equivalence : " ++
                        s)
                 | NoError (RState _ _ _ true as rstate) =>
                     search_equivalent_in_source p rstate start_memory lab_eq_s lab_eq_u
                       mem_update projection_func rel_vars max_depth 
                       (S k)
                 | NoError (RState _ _ _ false) => NoError (Equ_ret true k)
                 end
             | NoError (Equ_ret false k) => NoError (Equ_ret false k)
             end
         end) A B C source unrolled rel_vars start_memory mem_update projection_func
        lab_eq_s lab_eq_u prefix_length max_depth
) eqn:Hfix in H.
- apply error_neq_noerror in H. contradiction.
- destruct val eqn:Hval in H.
  destruct is_eq eqn:His_eq in H.
  + destruct (SF_B_P_T_Semantics_stmt_step_prefix_nth_U B lab_eq_u rel_vars unrolled
        (S prefix_length)) eqn:HSpn in H.
    (*1*)rewrite HSpn in H0. apply error_neq_noerror in H0. contradiction.
    (*2*)destruct val0 eqn:Hval0 in H. destruct relevant.
        * apply search_equivalent_increasing_s in H.
          rewrite His_eq in Hval. rewrite Hval in Hfix.
          exists n0.
          split.
          (*1*) assumption.
          (*2*) auto.

        *  rewrite HSpn in H0. rewrite Hval0 in H0.
           apply noerror_eq in H0.
           inversion H0.
  + inversion H.
Qed.

Definition step_semantics_equivalence (A B C: Type) (p: prog A) (up: uprog B) (rel_vars: relevant_variables) (start_memory: C) (mem_update: (relevant_state A)->C->C) (projection_func: A->C->B) (lab_eq_s: A->A->bool) (lab_eq_u: B->B->bool) (plength_u: nat) (plength_s: nat) (max_depth: nat): error bool :=
match step_semantics_eq_prover_u A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u plength_u max_depth with
|Error s => Error (String.append "Error while checking that unrolled simulates source : " s)
|NoError (Equ_ret false _) => Error "unrolled can't simulate source"
|NoError (Equ_ret true _) => 
  match step_semantics_eq_prover_s A B C p up rel_vars start_memory mem_update projection_func lab_eq_s lab_eq_u plength_s max_depth with
  |Error s => Error (String.append "Error while checking that unrolled simulates source : " s)
  |NoError (Equ_ret true _) => NoError true
  |NoError (Equ_ret false _) => Error "source can't simulate unrolled"
  end
end
.

Definition example_prog := 
Prog nat
(* declarations *)
(
(VarInit "x"%string)
::
(VarInit "y"%string)
::
nil
)
(* statements *)
( Compound _
(
(VarAssign _ "x"%string (Num 0)  (mkLabelling _  1 2 1000 )   )
~~
(VarAssign _ "y"%string (Num 0)  (mkLabelling _ 2 3 1000  ))
~~
[|
(While _ (Bool true) 
  (* body *)
  ( Compound _
  (
    (VarAssign _ "x"%string ( Plus (Var "x"%string) (Num 1) )  (mkLabelling _ 4 5 1000 )   )
    ~~
    [|
      (VarAssign _ "y"%string ( Plus (Var "y"%string) (Num 1) )  (mkLabelling _ 5 3 1000 )   )
    |]
  )
    (mkLabelling _ 4 3 1000 )
  )
  (mkLabelling _ 3 1000 1000 )
)
|]
)
(mkLabelling _ 3 1000 1000 )
)
(mkLabelling _ 1 1000 1000 )
.

Definition make_example_unrolled (n:nat) : uprog (classic_label):=
let fix make_unrolling (k: nat) : ne_list (ustatement classic_label) :=
  match k with
  | 0 => [| (UVarAssign _ "x"%string ( Plus (Var "x"%string) (Num 1) )
     (mkLabelling _ (mkLabel (S n) 4) (mkLabel 0 1000) (mkLabel 0 1000) )   ) |]
  | S k' => 
    (UVarAssign _ "x"%string ( Plus (Var "x"%string) (Num 1) ) 
     (mkLabelling _ (mkLabel ((S n)-k) 4) (mkLabel (S ((S n)-k)) 4) (mkLabel 0 1000) ) )
    ~~ (make_unrolling k')
  end
in

UProg classic_label
(* declarations *)
(
(VarInit "x"%string)
::
nil
)
(* statements *)
( UCompound _
(
(UVarAssign _ "x"%string (Num 0)  (mkLabelling _  (mkLabel 0 1) (mkLabel 1 4) (mkLabel 0 1000) )   )
~~
(make_unrolling n)
)
(mkLabelling _ (mkLabel 0 1) (mkLabel 0 1000) (mkLabel 0 1000) )
)
(mkLabelling _ (mkLabel 0 1) (mkLabel 0 1000) (mkLabel 0 1000) )
.

(*
Eval compute in SF_B_P_T_Semantics_stmt_step_prefix nat Nat.eqb (Rel_Vars ("x"%string::nil) nil) example_prog 10.
Eval compute in SF_B_P_T_Semantics_stmt_step_prefix_U classic_label eq_label (Rel_Vars ("x"%string::nil) nil) (make_example_unrolled 100) 10.
*)

Definition example_mem_update (state : relevant_state nat) (mem: nat) : nat :=
match state with
|RState _ lbl e rel =>
  match lbl with
  | 3 => S mem
  | _ => mem
  end
end.

Definition proj_example (label: nat) (memory: nat) : classic_label :=
match label with
|5 => mkLabel (S memory) 4
|2 => mkLabel 1 4
|_ => mkLabel 0 label
end.

(*
Eval compute in
step_semantics_equivalence nat classic_label nat example_prog (make_example_unrolled 2000) 
(Rel_Vars ("x"%string::nil) nil) 0 example_mem_update proj_example
Nat.eqb eq_label 50 50 10
.
*)
