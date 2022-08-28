Require Import Coq.Array.PArray.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import ast.
Require Import Coq.Lists.List.
Require Import Uint63.
Require Import Coq.Bool.Bool.


(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
error : error type to handle errors
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive error (t: Type) : Type :=
|Error (e:string)
|NoError (val: t)
.

Arguments Error {_}.
Arguments NoError {_} val.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
integer_value : represents an integer of known or unknown value.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive integer_value :=
|Unknown
|Known (n:Z)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
integer_value_eqb : check equality between two integer_value, if one is unknown return false
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition integer_value_eqb (i1 i2: integer_value) : bool := 
match i1, i2 with
|Unknown , Unknown => true
|Unknown , _ => false
|_ , Unknown => false
|Known n1, Known n2 => Z.eqb n1 n2
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_entry : represents a variable and its value in a variable environment
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive var_entry: Type :=
|VarEntry (id: identifier) (val: integer_value).

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_entry : represents an array, its size and its value in a variable environment
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive arr_entry: Type :=
|ArrEntry (id: identifier) (size: int) (val: array integer_value)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env : represents a variable environment
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition var_env: Type := list var_entry.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_env : represents an array environment
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition arr_env: Type := list arr_entry.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env : represents an environment, an array environment and variable environment pair
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive env: Type :=
|Env (vars: var_env) (arrs: arr_env)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
empty_env : the empty environment
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition empty_env: env := Env nil nil.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_eqb_rec : tests equality of n first terms between two arrays
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint arr_eqb_rec (arr1 arr2: array integer_value) (n: nat): bool :=
match n with
|0 => integer_value_eqb arr1.[Uint63.of_Z (Z.of_nat n)] arr2.[Uint63.of_Z (Z.of_nat n)]
|S n2 =>
  match integer_value_eqb arr1.[Uint63.of_Z (Z.of_nat n)] arr2.[ Uint63.of_Z (Z.of_nat n)] with
  |false => false
  |true => arr_eqb_rec arr1 arr2 n2
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_eqb : tests array equality using arr_eqb_rec
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition arr_eqb (arr1 arr2: array integer_value): bool :=
match Uint63.eqb (PArray.length arr1) (PArray.length arr2) with
| false => false
| true => arr_eqb_rec arr1 arr2 ( Z.to_nat ( Uint63.to_Z (pred (PArray.length arr1))))
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_entry_eqb : tests equality between two var_entry
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition var_entry_eqb (v1 v2: var_entry) : bool :=
match v1, v2 with
|VarEntry id1 val1, VarEntry id2 val2 => (integer_value_eqb val1 val2) && (String.eqb id1 id2)
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_entry_eqb : tests equality between two arr_entry
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition arr_entry_eqb (e1 e2: arr_entry) : bool :=
match e1, e2 with
|ArrEntry id1 size1 val1 , ArrEntry id2 size2 val2 => (String.eqb id1 id2) && (Uint63.eqb size1 size2)&& (arr_eqb val1 val2)
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
make_array : creates array of size "size" with all values initialisze to 0
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition make_array (size: int) : array integer_value:= 
PArray.make size Unknown
.

Theorem init_to_unknown : forall (n: int), forall  (i: int),  ltb i n = true -> PArray.get (make_array n) i = Unknown.
Proof.
intro. intro. intro.
apply get_make.
Qed.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
get_var_var_env : gets variable value from a var_env, returns None if variable not found
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint get_var_var_env (e: var_env) (v: identifier) : error integer_value :=
match e with
|nil => Error "var not found"%string
|head :: tail =>
  match head with
  | VarEntry var value =>
    match String.eqb var v with
    |true => NoError value
    |false => get_var_var_env tail v
    end
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
get_var_env : gets variable value from an env, returns None if variable not found
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition get_var_env (e: env) (v: identifier) : error integer_value :=
match e with
|Env vars arrs => get_var_var_env vars v
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
get_arr_var_env : gets rray value from a var_env
                  returns None if array not found or if index out of bound
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint get_arr_arr_env (e: arr_env) (v: identifier) (index: Z) : error integer_value :=
match e with
|nil => Error "arr not found"
|head :: tail =>
  match head with
  | ArrEntry var size arr =>
    match String.eqb var v with
    |true => 
      let max_index := ( Uint63.to_Z size) in
      match ((Z.geb index 0) && (Z.leb index max_index))  with
      |false => Error "arr found, but index out of bounds"
      |true => NoError (PArray.get arr (Uint63.of_Z index))
      end
    |false => get_arr_arr_env tail v index
    end
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
get_arr_env : gets array value from an env
              returns None if variable not found or if index out of bound
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition get_arr_env (e: env) (v: identifier) (index: Z) : error integer_value :=
match e with
|Env vars arrs => get_arr_arr_env arrs v index
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_exists : tests if a variable exists in a var_env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint var_env_exists (e: var_env) (v: identifier): bool :=
match e with
| nil => false
| (VarEntry id _) :: tail => 
  match String.eqb id v with
  | true => true 
  | false => var_env_exists tail v
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_var_exists : tests if a variable exists in an env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_var_exists (e: env) (v: identifier): bool :=
match e with
|Env vars _ => var_env_exists vars v
end
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_add : adds a variable to a var_env, returns None if variable already exists
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition var_env_add (e: var_env) (v: identifier): error var_env :=
match var_env_exists e v with
|true => Error "var already exists"
|false => NoError ( (VarEntry v Unknown)::e )
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_add_var : adds a variable to an env, returns None if variable already exists
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_add_var (e: env) (v: identifier): error env :=
match e with
| Env vars arrs => 
  match var_env_add vars v with
  |Error s => Error s
  |NoError newvars => NoError (Env newvars arrs)
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_env_exists : tests if an array exists in an arr_env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint arr_env_exists (e: arr_env) (v: identifier): bool :=
match e with
| nil => false
| (ArrEntry id _ _) :: tail => 
  match String.eqb id v with
  | true => true 
  | false => arr_env_exists tail v
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_arr_exists : tests if an array exists in an env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_arr_exists (e: env) (v: identifier): bool :=
match e with
|Env _ arrs => arr_env_exists arrs v
end
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_env_add : adds an array to an arr_env, returns None if variable already exists
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition arr_env_add (e: arr_env) (v: identifier) (size: int) : error arr_env :=
match arr_env_exists e v with
|true => Error "arr already exists"
|false => NoError ( (ArrEntry v size (make_array size))::e )
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_add_arr : adds an array to an env, returns None if variable already exists
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_add_arr (e: env) (v: identifier) (size: int) : error env :=
match e with
| Env vars arrs => 
  match arr_env_add arrs v size with
  |Error s => Error s
  |NoError newarrs => NoError (Env vars newarrs)
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_set_rec : helper function to set a variable in a var_env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint var_env_set_rec (e: var_env) (v: identifier) (val: integer_value) (acc: var_env): error var_env :=
match e with
|nil => Error "couldn't set var, var not found"
|(VarEntry id curval) :: tail =>
  match String.eqb id v with
  |true => NoError (List.concat (((VarEntry id val ) :: tail) :: acc :: nil))
  |false => var_env_set_rec tail v val ((VarEntry id curval ) :: acc)
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_set : sets a variable in a var_env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition var_env_set (e: var_env) (v: identifier) (val: integer_value): error var_env :=
var_env_set_rec e v val nil
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_set_var : sets a variable in an env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_set_var (e: env) (v: identifier) (val: integer_value): error env :=
match e with
| Env vars arrs => 
  match var_env_set vars v val with
  | Error s => Error s
  | NoError newvars => NoError (Env newvars arrs)
  end
end
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_env_set_rec : helper function to set an array in a arr_env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint arr_env_set_rec (e: arr_env) (v: identifier) (val: integer_value) (index: Z) (acc: arr_env): error arr_env :=
match e with
|nil => Error "couldn't set arr, arr not found"
|(ArrEntry id size curval) :: tail =>
  match String.eqb id v with
  |true => 
    let max_index := ( Uint63.to_Z size) in
    match ((Z.geb index 0) && (Z.leb index max_index))  with
    |false => Error "couldn't set arr, index out of bounds"
    |true => NoError (List.concat (((ArrEntry id size curval.[ (Uint63.of_Z index) <- val] ) :: tail) :: acc :: nil))
    end
  |false => arr_env_set_rec tail v val index ((ArrEntry id size curval) :: acc)
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
arr_env_set : sets an array in a arr_env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition arr_env_set (e: arr_env) (v: identifier) (val: integer_value) (index: integer_value): error arr_env :=
match index with
|Unknown => Error "tried setting array with unknown index"
|Known ind => arr_env_set_rec e v val ind nil
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_set_arr : sets an array in an env
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_set_arr (e: env) (v: identifier) (val: integer_value) (index: integer_value): error env :=
match e with
| Env vars arrs => 
  match arr_env_set arrs v val index with
  | Error _ => Error "couldn't set var, var not found"
  | NoError newarrs => NoError (Env vars newarrs)
  end
end
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_included : checks if a var_env is included in another
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint var_env_included (e1 e2: var_env): bool :=
match e1, e2 with
| nil , _ => true
| _ :: _ , nil => false
| entry1::tail , _ :: _ => 
  match List.existsb (var_entry_eqb entry1 ) e2 with
  |true => var_env_included tail e2
  |false => false
  end
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
var_env_included : checks if an arr_env is included in another
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Fixpoint arr_env_included (e1 e2: arr_env): bool :=
match e1, e2 with
| nil , _ => true
| _ :: _ , nil => false
| entry1::tail , _ :: _ => 
  match List.existsb (arr_entry_eqb entry1 ) e2 with
  |true => arr_env_included tail e2
  |false => false
  end
end.


(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
env_included : checks if an env is included in another
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition env_included (e1 e2: env): bool :=
match e1, e2 with
|Env v1 a1, Env v2 a2 => (var_env_included v1 v2) && (arr_env_included a1 a2)
end.
