Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Uint63.
Require Import Coq.Init.Nat.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
identifier : type for variable and array names, a string
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition identifier: Type := string.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
aexpr : type representing an arithmetic expression
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive aexpr: Type :=
|Num (v: Z)
|Arr (id: identifier) (idx: aexpr)
|Var (id: identifier)
|Minus (lhs rhs: aexpr)
|Plus (lhs rhs: aexpr)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
bexpr : type representing a boolean expression
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive bexpr: Type :=
|Bool (b: bool)
|Lt (lhs rhs: aexpr)
|Lte (lhs rhs: aexpr)
|Eq (lhs rhs: aexpr)
|Neq (lhs rhs: aexpr)
|Gt (lhs rhs: aexpr)
|Gte (lhs rhs: aexpr)
|Nand (lhs rhs: bexpr)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
aexpr : type representing a label
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Record classic_label: Type := mkLabel
{
  n: nat;
  l: nat;
}.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
eq_label : checks equality between two labels
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition eq_label (l1 l2: classic_label): bool := (Nat.eqb (n l1) (n l2) ) && (Nat.eqb (l l1) (l l2) ) .

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
labelling : type representing a labelling, an at label, an after label
            and a break-to label (which is only used for the break statement)
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Record labelling  (A: Type ): Type := mkLabelling
{
  atl: A;
  af: A;
  br: A;
}.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
declaration : type representing the declaration of variables at the start of a program
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive declaration: Type :=
| ArrayInit (id: identifier) (size: int)
| VarInit (id: identifier)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
ne_list : type representing a list that can't be empty
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive ne_list (A: Type) :=
|Single (t:A)
|NECons (head:A) (tail: ne_list A)
.

Arguments Single {_} t.
Arguments NECons {_} head tail.

Notation "[| x |]" := (Single x ).
Infix "~~" := NECons (at level 60, right associativity) : list_scope.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
ne_length : computes the length of a non-empty list.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition ne_length (A : Type) : ne_list A -> nat :=
  fix ne_length l :=
  match l with
   | [|_|] => S 0
   | NECons _ l' => S (ne_length l')
  end.

Arguments ne_length {_}.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
Quick proof to show that the length of a ne_list > 0.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Theorem ne_list_length : forall (A:Type) , forall (nel: ne_list A), (ne_length nel) > 0.
Proof.
intros.
induction nel.
+ simpl. auto.
+ simpl. apply gt_Sn_O.
Qed.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
statement : type to represent the statements of a program TODO add error.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive statement (A: Type) : Type :=
| VarAssign (assignee: identifier) (assigned: aexpr) (l: labelling A)
| ArrAssign (assignee: identifier) (idx: aexpr) (assigned: aexpr) (l: labelling A)
| Emptystmt (l: labelling A)
| If (test: bexpr) (body: statement A) (l: labelling A)
| Ifelse (test: bexpr) (ibody ebody: statement A) (l: labelling A)
| While (test: bexpr) (body: statement A) (l: labelling A)
| Break (l: labelling A)
| Compound (sts: ne_list (statement A)) (l: labelling A)
| Breakable (sts: ne_list (statement A)) (l: labelling A)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
get_stmt : gets the labelling of a statement.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition get_stmt_labelling (A: Type) (s: statement A) : labelling A :=
match s with
| ArrAssign _ _ _ _ l => l
| VarAssign _ _ _ l => l
| Emptystmt _ l => l
| If _ _ _ l => l
| Ifelse _ _ _ _ l => l
| While _ _ _ l => l
| Break _ l => l
| Compound _ _ l => l
| Breakable _ _ l => l
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
prog: type to represent a program. a list of declared variables,
      a list of statements and a starting label.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive prog (A: Type) : Type :=
|Prog (decls: list declaration) (sts: statement A) (l: labelling A)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
ustatement : type to represent the ustatements of an unrolled program.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive ustatement (A: Type) : Type :=
| UVarAssign (assignee: identifier) (assigned: aexpr) (l: labelling A)
| UArrAssign (assignee: identifier) (idx: aexpr) (assigned: aexpr) (l: labelling A)
| UEmptystmt (l: labelling A)
| UIf (test: bexpr) (body: ustatement A) (l: labelling A)
| UIfelse (test: bexpr) (ibody ebody: ustatement A) (l: labelling A)
| UBreak (l: labelling A)
| UCompound (sts: ne_list (ustatement A)) (l: labelling A)
| UBreakable (sts: ne_list (ustatement A)) (l: labelling A)
| UErrorStmt (l: labelling A)
.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
get_stmt : gets the labelling of a ustatement.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Definition get_ustmt_labelling (A: Type) (s: ustatement A) : labelling A :=
match s with
| UArrAssign _ _ _ _ l => l
| UVarAssign _ _ _ l => l
| UEmptystmt _ l => l
| UIf _ _ _ l => l
| UIfelse _ _ _ _ l => l
| UBreak _ l => l
| UCompound _ _ l => l
| UBreakable _ _ l => l
| UErrorStmt _ l => l
end.

(*<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>
prog: type to represent an unrolled program. a list of declared variables,
      a list of ustatements and a starting label.
<><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><><>*)
Inductive uprog (A: Type) : Type :=
|UProg (decls: list declaration) (sts: ustatement A) (l: labelling A)
.
