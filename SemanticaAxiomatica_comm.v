From Stdlib Require Import Arith.
From Stdlib Require Import Strings.String.

Definition total_map (A : Type) := string -> A.

Definition t_empty {A : Type} (v : A) : total_map A :=
(fun _ => v).

Definition t_update {A : Type} (m : total_map A) (x : string) (v : A) :=
fun x' => if String.eqb x x' then v else m x'.

Notation "'_' '!->' v" := (t_empty v)
(at level 100, right associativity).

Notation "x '!->' v ';' m" := (t_update m x v)
(at level 100, v at next level, right associativity).


Definition state := total_map nat.

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).

Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BNeq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BGt (a1 a2 : aexp)
| BNot (b : bexp)
| BAnd (b1 b2 : bexp).

Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.
Declare Custom Entry com.
Declare Scope com_scope.

Notation "<{ e }>" := e (at level 0, e custom com at level 99) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)

(in custom com at level 0, only parsing,
f constr at level 0, x constr at level 9,
y constr at level 9) : com_scope.

Notation "x + y" := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y" := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y" := (AMult x y) (in custom com at level 40, left associativity).
Notation "'true'" := true (at level 1).
Notation "'true'" := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "x <= y" := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y" := (BGt x y) (in custom com at level 70, no associativity).
Notation "x = y" := (BEq x y) (in custom com at level 70, no associativity).
Notation "x <> y" := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x && y" := (BAnd x y) (in custom com at level 80, left associativity).
Notation "'~' b" := (BNot b) (in custom com at level 75, right associativity).


Open Scope com_scope.


Fixpoint aeval (st : state)  (a : aexp) : nat :=
match a with
| ANum n => n
| AId x => st x 
| <{a1 + a2}> => (aeval st a1) + (aeval st a2)
| <{a1 - a2}> => (aeval st a1) - (aeval st a2)
| <{a1 * a2}> => (aeval st a1) * (aeval st a2)
end.

Fixpoint beval (st : state)  (b : bexp) : bool :=
match b with
| <{true}> => true
| <{false}> => false
| <{a1 = a2}> => (aeval st a1) =? (aeval st a2)
| <{a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
| <{a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
| <{a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
| <{~ b1}> => negb (beval st b1)
| <{b1 && b2}> => andb (beval st b1) (beval st b2)
end.

Definition empty_st := (_ !-> 0).

Notation "x '!->' v" := (x !-> v ; empty_st) (at level 100).


Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com)
| CPrint (a : aexp) (*Nuevo*)
| CNew (x : string) (a : aexp) (c : com). (*Nuevo*)


Notation "'skip'" := CSkip (in custom com at level 0) : com_scope.

Notation "x := y" :=
(CAsgn x y)
(in custom com at level 0, x constr at level 0,
y at level 85, no associativity) : com_scope.

Notation "x ; y" :=
(CSeq x y)
(in custom com at level 90, right associativity) : com_scope.

Notation "'if' x 'then' y 'else' z 'end'" :=

(CIf x y z)
(in custom com at level 89, x at level 99,
y at level 99, z at level 99) : com_scope.

Notation "'while' x 'do' y 'end'" :=

(CWhile x y)
(in custom com at level 89, x at level 99, y at level 99) : com_scope.

Reserved Notation
"st '=[' c ']=>' st'"
(at level 40, c custom com at level 99,
st constr, st' constr at next level).

(*Nuevas notaciones*)
Notation "'print' a" := (CPrint a) (in custom com at level 90) : com_scope.
Notation "'new' x ':=' a 'in' c" := (CNew x a c) (in custom com at level 89, x constr, a at level 85, c at level 99) : com_scope.


Inductive ceval : com -> state -> state -> Prop :=
| E_Skip : forall st,
    st =[ CSkip ]=> st
| E_Asgn : forall st a n x,
    aeval st a = n ->
    st =[ x := a ]=> (x !-> n ; st)
| E_Seq : forall c1 c2 st st' st'',
    st =[ c1 ]=> st' ->
    st' =[ c2 ]=> st'' ->
    st =[ c1 ; c2 ]=> st''
| E_IfTrue : forall st st' b c1 c2,
    beval st b = true ->
    st =[ c1 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_IfFalse : forall st st' b c1 c2,
    beval st b = false ->
    st =[ c2 ]=> st' ->
    st =[ if b then c1 else c2 end]=> st'
| E_WhileFalse : forall b st c,
    beval st b = false ->
st =[ while b do c end ]=> st
| E_WhileTrue : forall st st' st'' b c,
    beval st b = true ->
    st =[ c ]=> st' ->
    st' =[ while b do c end ]=> st'' ->
    st =[ while b do c end ]=> st''
| E_Print : forall st a, (*nuevo*)
    st =[ print a ]=> st
| E_New : forall st st' x a c n o, (*nuevo*)
    aeval st a = n ->
    o = st x ->
    (x !-> n ; st) =[ c ]=> st' ->
    st =[ new x := a in c ]=> (x !-> o ; st')
where "st =[ c ]=> st'" := (ceval c st st').


Module SemanticaAxiomatica.

Definition Assertion := state -> Prop.

Definition Aexp : Type := state -> nat.

Definition assert_of_Prop (P : Prop) : Assertion := fun _ => P.
Definition Aexp_of_nat (n : nat) : Aexp := fun _ => n.

Definition Aexp_of_aexp (a : aexp) : Aexp := fun st => aeval st a.

Coercion assert_of_Prop : Sortclass >-> Assertion.
Coercion Aexp_of_nat : nat >-> Aexp.
Coercion Aexp_of_aexp : aexp >-> Aexp.

Arguments assert_of_Prop /.
Arguments Aexp_of_nat /.
Arguments Aexp_of_aexp /.

Declare Custom Entry assn. (* The grammar for Hoare logic Assertions *)
Declare Scope assertion_scope.
Bind Scope assertion_scope with Assertion.
Bind Scope assertion_scope with Aexp.
Delimit Scope assertion_scope with assertion.


Notation "# f x .. y" := (fun st => (.. (f ((x:Aexp) st)) .. ((y:Aexp) st)))
                  (in custom assn at level 2,
                  f constr at level 0, x custom assn at level 1,
                  y custom assn at level 1) : assertion_scope.

Notation "P -> Q" := (fun st => (P:Assertion) st -> (Q:Assertion) st) (in custom assn at level 99, right associativity) : assertion_scope.
Notation "P <-> Q" := (fun st => (P:Assertion) st <-> (Q:Assertion) st) (in custom assn at level 95) : assertion_scope.

Notation "P \/ Q" := (fun st => (P:Assertion) st \/ (Q:Assertion) st) (in custom assn at level 85, right associativity) : assertion_scope.
Notation "P /\ Q" := (fun st => (P:Assertion) st /\ (Q:Assertion) st) (in custom assn at level 80, right associativity) : assertion_scope.
Notation "~ P" := (fun st => ~ ((P:Assertion) st)) (in custom assn at level 75, right associativity) : assertion_scope.
Notation "a = b" := (fun st => (a:Aexp) st = (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <> b" := (fun st => (a:Aexp) st <> (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a <= b" := (fun st => (a:Aexp) st <= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a < b" := (fun st => (a:Aexp) st < (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a >= b" := (fun st => (a:Aexp) st >= (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "a > b" := (fun st => (a:Aexp) st > (b:Aexp) st) (in custom assn at level 70) : assertion_scope.
Notation "'True'" := True.
Notation "'True'" := (fun st => True) (in custom assn at level 0) : assertion_scope.
Notation "'False'" := False.
Notation "'False'" := (fun st => False) (in custom assn at level 0) : assertion_scope.

Notation "a + b" := (fun st => (a:Aexp) st + (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a - b" := (fun st => (a:Aexp) st - (b:Aexp) st) (in custom assn at level 50, left associativity) : assertion_scope.
Notation "a * b" := (fun st => (a:Aexp) st * (b:Aexp) st) (in custom assn at level 40, left associativity) : assertion_scope.

Notation "( x )" := x (in custom assn at level 0, x at level 99) : assertion_scope.

Notation "$ f" := f (in custom assn at level 0, f constr at level 0) : assertion_scope.
Notation "x" := (x%assertion) (in custom assn at level 0, x constr at level 0) : assertion_scope.

Declare Scope hoare_spec_scope.
Open Scope hoare_spec_scope.

Definition assert_implies (P Q : Assertion) : Prop :=
  forall st, P st -> Q st.

Notation "P ->> Q" := (assert_implies P Q)
                        (at level 80) : hoare_spec_scope.

Notation "P <<->> Q" := (P ->> Q /\ Q ->> P)
                          (at level 80) : hoare_spec_scope.

Definition tripleta_hoare_valida
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.

Notation "{{ P }} c {{ Q }}" :=
  (tripleta_hoare_valida P c Q)
  (at level 90,
   c at next level,
   format "'[' '{{'  P  '}}'  '/' c '/' '{{'  Q  '}}' ']'")
  : hoare_spec_scope.

Definition assertion_sub X (a:aexp) (P:Assertion) : Assertion :=
  fun (st : state) =>
    (P%_assertion) (X !-> ((a:Aexp) st); st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
                              (in custom assn at level 10, left associativity,
                               P custom assn, X global, a custom com)
                          : assertion_scope.

(*
Bajo esta definicion, algunos programas pueden ser equivalentes aunque desde la perspectiva del programador no lo sean
ciertos programas sean indistinguibles para Hoare aunque no sean estructuralmente equivalentes.

ejemplo, new X := 0 in skip es equivalente a   skip 

bajo esta nocion, porque el estado externo no cambia

*)

Definition equiv_axiomatica (c1 c2 : com) : Prop :=
  forall P Q : Assertion,
    ({{ P }} c1 {{ Q }}) <<->>
    ({{ P }} c2 {{ Q }}).


Example if_equiv : 
    forall b S,
    equiv_axiomatica
    <{ if b then S else skip end }>
    <{S}>.
Proof. 

Admitted.


End SemanticaAxiomatica.