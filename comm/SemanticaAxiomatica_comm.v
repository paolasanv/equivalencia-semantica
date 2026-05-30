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

Definition valid_hoare_triple
           (P : Assertion) (c : com) (Q : Assertion) : Prop :=
  forall st st',
     st =[ c ]=> st' ->
     P st  ->
     Q st'.
    
Notation "{{ P }}  c  {{ Q }}" :=
  (valid_hoare_triple P c Q) (at level 90, c custom com at level 99)
  : hoare_spec_scope.



Definition assertion_sub X (a:aexp) (P:Assertion) : Assertion :=
  fun (st : state) =>
    (P%_assertion) (X !-> ((a:Aexp) st); st).

Notation "P [ X |-> a ]" := (assertion_sub X a P)
                              (at level 10, X at next level, a custom com)
                          : assertion_scope.

  (* Sustitución auxiliar *)
(*Definition assn_sub X a (P:Assertion) : Assertion :=
  fun (st : state) =>
    P (X !-> aeval st a ; st).

Notation "P [ X |-> a ]" := (assn_sub X a P)
  (at level 10, X at next level, a custom com).*)



Theorem hoare_asgn : forall Q X (a:aexp),
  {{Q [X |-> a]}} X := a {{Q}}.
Proof.
  intros Q X a st st' HE HQ.
  inversion HE. subst.
  unfold assertion_sub in HQ. simpl in HQ. assumption.  Qed.



Definition bassertion b : Assertion :=
  fun st => (beval st b = true).

Coercion bassertion : bexp >-> Assertion.

Arguments bassertion /.

(** A useful fact about [bassertion]: 

Lemma bexp_eval_false : forall b st,
  beval st b = false -> ~ ((bassertion b) st).
Proof. congruence. Qed.
*)

Inductive derivable : Assertion -> com -> Assertion -> Prop :=
  | H_Skip : forall P,
      derivable P <{skip}> P
  | H_Asgn : forall Q X a,
      derivable (Q [X |-> a]) <{X := a}> Q
  | H_Seq : forall P c Q d R,
      derivable Q d R -> derivable P c Q -> derivable P <{c;d}> R
  | H_If : forall P Q b c1 c2,
    derivable (fun st => P st /\ bassertion b st) c1 Q ->
    derivable (fun st => P st /\ ~(bassertion b st)) c2 Q ->
    derivable P <{if b then c1 else c2 end}> Q
  | H_While : forall P b c,
    derivable (fun st => P st /\ bassertion b st) c P ->
    derivable P <{while b do c end}> (fun st => P st /\ ~ (bassertion b st))
  | H_Consequence : forall (P Q P' Q' : Assertion) c,
    derivable P' c Q' ->
    (forall st, P st -> P' st) ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.


Notation "|- {{ P }} c {{ Q }}" :=
  (derivable P c Q)
  (at level 90).


Definition cequiv (c1 c2 : com) : Prop :=
  forall (st st' : state),
    (st =[ c1 ]=> st') <-> (st =[ c2 ]=> st').


Definition equiv_axiomatica
           (c1 c2 : com) : Prop :=

(forall P Q,
    (|- {{P}} c1 {{Q}})
      <->
    (|- {{P}} c2 {{Q}})).

Lemma H_Consequence_pre : forall (P Q P': Assertion) c,
    derivable P' c Q ->
    (forall st, P st -> P' st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

Lemma H_Consequence_post  : forall (P Q Q' : Assertion) c,
    derivable P c Q' ->
    (forall st, Q' st -> Q st) ->
    derivable P c Q.
Proof. eauto using H_Consequence. Qed.

(*equivalencia usando tripletas de Haore*)
Definition equiv_axiomatica_valida (c1 c2 : com) : Prop :=
  forall P Q,
    {{P}} c1 {{Q}} <-> {{P}} c2 {{Q}}.

(*demo correspondiente en semantica operacional*)
Lemma if_same_branch_cequiv :
  forall b S,
  cequiv
    S
    <{ if b then S else S end }>.
Proof.
  intros b S st st'.
  split.

  - intro H.
    destruct (beval st b) eqn:Hb.
    + apply E_IfTrue.
      * exact Hb.
      * exact H.
    + apply E_IfFalse.
      * exact Hb.
      * exact H.

  - intro H.
    inversion H; subst.
    + assumption.
    + assumption.
Qed.

Lemma cequiv_preserves_valid_hoare :
  forall c1 c2,
  cequiv c1 c2 ->
  forall P Q,
    {{P}} c1 {{Q}} <-> {{P}} c2 {{Q}}.
Proof.
  intros c1 c2 Heq P Q.
  split.

  - unfold valid_hoare_triple.
    intros H st st' Hc HP.
    apply H with (st := st) (st' := st').
    + apply Heq.
      exact Hc.
    + exact HP.

  - unfold valid_hoare_triple.
    intros H st st' Hc HP.
    apply H with (st := st) (st' := st').
    + apply Heq.
      exact Hc.
    + exact HP.
Qed.

Theorem if_equiv_valid :
  forall b S,
  equiv_axiomatica_valida
    S
    <{ if b then S else S end }>.
Proof.
  intros b S.
  unfold equiv_axiomatica_valida.
  intros P Q.
  apply cequiv_preserves_valid_hoare.
  apply if_same_branch_cequiv.
Qed.


(*equivalencia derivable |- *)

Theorem hoare_sound :
  forall P c Q,
  derivable P c Q ->
  {{P}} c {{Q}}.
Proof.
Admitted.

Theorem hoare_complete :
  forall P c Q,
  {{P}} c {{Q}} ->
  derivable P c Q.
  Proof.
Admitted.


Theorem cequiv_implies_axiomatic_equiv :
  forall c1 c2,
  cequiv c1 c2 ->
  equiv_axiomatica c1 c2.
Proof.
  intros c1 c2 Hceq.
  unfold equiv_axiomatica.
  intros P Q.
  split.

  - intro H.
    apply hoare_complete.
    apply cequiv_preserves_valid_hoare with (c1 := c1) (c2 := c2).
    + exact Hceq.
    + apply hoare_sound.
      exact H.

  - intro H.
    apply hoare_complete.
    apply cequiv_preserves_valid_hoare with (c1 := c1) (c2 := c2).
    + intro st.
      intro st'.
      specialize (Hceq st st').
      tauto.
    + apply hoare_sound.
      exact H.
Qed.

Theorem if_equiv :
  forall b S,
  equiv_axiomatica
    S
    <{ if b then S else S end }>.
Proof.
  intros b S.
  apply cequiv_implies_axiomatic_equiv.
  apply if_same_branch_cequiv.
Qed.

(*
Example if_equiv : 
    forall b S,
    equiv_axiomatica
    <{S}>
     <{ if b then S else S end }>.
Proof.
  unfold equiv_axiomatica.
  unfold cequiv.
  split.
  + intros HS.
    apply H_If.
    - eapply H_Consequence_pre.
      *  eassumption. 
      * intros st [HP HBT]. assumption.
    - eapply H_Consequence_pre.
      * eassumption.
      * intros st [HP HBT]. assumption.
  + intros HIF.
    eapply H_Consequence_pre.
    - eapply H_If in HIF.*)

End SemanticaAxiomatica.