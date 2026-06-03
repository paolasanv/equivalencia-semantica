From Stdlib Require Import Arith.
From Stdlib Require Import Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.

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

(*
        Definición de la sintaxis abstracta de COMM.

<AExp> ::= <Nat>
    | <Id>
    | <AExpr> + <AExpr>
    | <AExpr> - <AExpr>
    | <AExpr> * <AExpr>

<BExp> ::= true
    | false
    | <BExp> and <BExp> 
    | not <BExp> 
    | <AExpr> < <AExpr>
    | <AExpr> = <AExpr>

<Comm> ::= skip
    | new <Id> := <Aexp> in <Comm>
    | print <AExp>
    | <Id> := <Aexp>
    | <Comm> ; <Comm>
    | if <BExp> then <Comm> else <Comm> end
*)

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
| CPrint (a : aexp) (*Nuevo*)
| CNew (x : string) (a : aexp) (c : com). (*Nuevo*)

Notation "'skip'"  := CSkip (in custom com at level 0) : com_scope.

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

Reserved Notation
"st '=[' c ']=>' st'"
(at level 40, c custom com at level 99,
st constr, st' constr at next level).

(*Nuevas notaciones*)
Notation "'print' a" := (CPrint a) (in custom com at level 90) : com_scope.
Notation "'new' x ':=' a 'in' c" := (CNew x a c) (in custom com at level 89, x constr, a at level 85, c at level 99) : com_scope.


Module SemanticaDenotativa.

(*Función semántica para expresiones aritméticas*)
Fixpoint A (a : aexp) : state -> nat :=
    fun st =>
        match a with
        | ANum n => n
        | AId X => st X
        | APlus a1 a2 => A a1 st + A a2 st
        | AMinus a1 a2 => A a1 st - A a2 st
        | AMult a1 a2 => A a1 st * A a2 st
        end.
(*Función semántica para expresiones booleanas*)
Fixpoint B (b : bexp) : state -> bool :=
    fun st =>
        match b with
        | BTrue => true
        | BFalse => false
        | BEq a1 a2 => Nat.eqb (A a1 st) (A a2 st)
        | BNeq a1 a2 => negb (Nat.eqb (A a1 st) (A a2 st))
        | BLe a1 a2 => Nat.leb (A a1 st) (A a2 st)
        | BGt a1 a2 => negb (Nat.leb (A a1 st) (A a2 st))
        | BNot b1 => negb (B b1 st)
        | BAnd b1 b2 => andb (B b1 st) (B b2 st)
        end.

(*Función semántica para comandos*)
Fixpoint C (c : com) : state -> state :=
  fun st =>
    match c with
    | CSkip => st
    | CAsgn x a => x !-> (A a st) ; st
    | CSeq c1 c2 => C c2 (C c1 st)
    | CIf b c1 c2 =>
        if B b st
        then C c1 st
        else C c2 st
    | CPrint a => st
    | CNew x a c1 =>
        let old := st x in
        let st' := (x !-> (A a st) ; st) in
        let st'' := C c1 st' in
        (x !-> old ; st'')
    end.

Notation "[[ c ]]" := (C c)
  (at level 0).

(*Definición de equivalencia en semántica denotativa*)
Definition equiv_denotativa (c1 c2 : com) : Prop :=
  forall st,
    [[ c1 ]] st = [[ c2 ]] st.


(*
                        Ejemplo #2
Demostración de equivalencia de programas bajo el enfoque de semántica denotativa 

               if b the S else T ≡ if ~ b then T else S end
*)
Example if_equiv :
  forall b S T,
  equiv_denotativa
    <{if b then S else T end}>
    <{if ~ b then T else S end}>.
Proof.
    intros b S T st.
    simpl.
    destruct (B b st).
    + reflexivity.
    + reflexivity.
Qed. 


(*
                    Programas equivalentes compartido #1
           if b then (S ; T) else (R; T) end ≡ (if b then S else R end); T

Demostración bajo semántica denotativa
*)
Example seq_equiv :
    forall b S T R,
    equiv_denotativa
        <{if b then (S ; T) else (R; T) end}>
        <{(if b then S else R end); T }>.
Proof.
    unfold equiv_denotativa.
    intros.
    simpl.
    destruct (B b st).
    - reflexivity.
    - reflexivity.
Qed. 


(*
                   Programas equivalentes compartido #2
                new x := a in skip ≡ skip

Demostración bajo semántica denotativa
*)
Example equiv_local_skip :
  forall x a,
  equiv_denotativa
    <{new x := a in skip }>
    <{skip}>.
Proof.  
  intros x a st. 
  simpl. 
  unfold t_update. 
  apply functional_extensionality.
  intro x'.
  destruct (String.eqb x x') eqn:H.
  - apply String.eqb_eq in H.
    rewrite H. 
    reflexivity.
  - reflexivity.
Qed.

End SemanticaDenotativa.