Require Export Coq.Bool.Bool.
Require Export Coq.Arith.Arith.
Require Import Coq.Logic.Epsilon.
Require Import Coq.Logic.Classical.
Require Import Coq.Vectors.Vector.
Import VectorNotations.
(* 基本语法 *)
(* 一阶语言符号 *)
(*个体变元*)
Inductive Var : Set :=
  | X : nat -> Var.
(*个体常元*)
Inductive Con : Set :=
  | C : nat -> Con.
(*运算符*)
Inductive Fun : Set :=
  | F : nat -> nat -> Fun.
(*谓词*)
Inductive Rel : Set :=
  | R : nat -> nat -> Rel.
(* 元数（arity）函数 *)
Definition arity_F (f : Fun) : nat :=
  match f with
  | F a b => S a
  end.
Definition arity_R (r : Rel) : nat :=
  match r with
  | R a b => S a
  end.
(* 项 *)
Inductive term : Set :=
  | Tvar : Var -> term
  | Tcon : Con -> term
  | Tfun : forall f: Fun, Vector.t term (arity_F f) -> term.

Definition var_num (v: Var): nat:=
  match v with
  | X n => n
  end.

Definition con_num (v: Con): nat:=
  match v with
  | C n => n
  end.

Definition eqbv (n m: Var) : bool :=
  match n, m with
  | X p, X q => p =? q
  end.

Lemma eqb_reflect : forall x y, reflect (x = y) (x =? y).
Proof.
  intros x y.
  apply iff_reflect. symmetry. apply Nat.eqb_eq.
Qed.

Lemma eqbv_reflect : forall (m n: Var), reflect (m = n) (eqbv m n).
Proof.
  intros. apply iff_reflect. split; intros; destruct m, n.
  - inversion H. simpl. destruct (eqb_reflect n n); auto.
  - inversion H. f_equal. destruct (eqb_reflect n0 n); auto. inversion H1.
Qed.

Definition eqbc (n m: Con) : bool :=
  match n, m with
  | C p, C q => p =? q
  end.

Lemma eqbc_reflect : forall (m n: Con), reflect (m = n) (eqbc m n).
Proof.
  intros. apply iff_reflect. split; intros; destruct m, n.
  - inversion H. simpl. destruct (eqb_reflect n n); auto.
  - inversion H. f_equal. destruct (eqb_reflect n0 n); auto. inversion H1.
Qed.
Global Hint Resolve eqb_reflect eqbv_reflect eqbc_reflect : bdestruct.

Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [eauto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_eq in H]]].

Class Module := {
  M : Type;
  I_c : Con -> M;
  I_f : forall (f: Fun), Vector.t M (arity_F f) -> M;
  I_R : forall (r: Rel), Vector.t M (arity_R r) -> bool
}.

(* 赋值 *)
Definition value (MM: Module):= Var -> M.

Theorem classicT : forall P, {P} + {~P}.
Proof.
  intros. assert { x:bool | if x then P else ~P }.
  { apply constructive_indefinite_description.
    destruct (classic P).
    - exists true. auto.
    - exists false. auto. }
  destruct H,x; auto.
Qed.
(* x重新赋值为m *)
Definition value_v {MM} (v: value MM) (x: Var) (m: M) := 
  fun (y: Var) => match (classicT (y = x)) with
                   | left _ => m
                   | right _ => v y
                  end.
Notation " v [ x |-> m ] " := (value_v v x m) (at level 0).

(*项t的赋值*)
Fixpoint value_term {MM} (v: value MM) (t: term) : M :=
  match t with
  | Tcon c => I_c c
  | Tvar s => v s
  | Tfun f q => I_f f (Vector.map (value_term v) q)
  end.
Notation " v // " := (value_term v) (at level 0).

(* t'对t中x的代入 t'(x;t)*)
Fixpoint substitute_t (t t': term) (x: Var) :=
  match t with
  | Tcon c => Tcon c
  | Tvar y => if (eqbv x y) then t' else Tvar y 
  | Tfun  _ q => let fix substitute_v (n: nat) (r: Vector.t (term) n)
                   (t': term) (x: Var) :=
                   match r with 
                    | [] => []
                    | h :: q => (substitute_t h t' x) :: (substitute_v _ q t' x) 
                   end in (Tfun _ (substitute_v _ q t' x))
  end.
Notation " s { x ; r } ":= (substitute_t r s x)(at level 0).
Fixpoint substitute_v (n: nat) (r: Vector.t term n) 
  (t': term) (x: Var) :=
  match r with 
  | [] => []
  | h :: q => (substitute_t h t' x) :: (substitute_v _ q t' x)
  end.

(* 向量项替换引理*)
Definition sub_v (n: nat) (v: Vector.t (term) n) := 
  forall MM (u:value MM) x t', Vector.map (u//) 
  (substitute_v n v t' x) = Vector.map 
  ((u [x |-> (u // t') ])//) v.
(* 项替换定理 *)
Definition sub_t t := forall MM (u: value MM) t' x,
  u //(t' { x ; t }) = (u [x |-> (u // t')]) // t.


Fact sub_1 : forall (n: Var), sub_t (Tvar n).
Proof.
  red. intros. simpl. destruct(eqbv x n) eqn:E.
  - unfold value_v. bdestruct (eqbv x n). subst.
    destruct classicT.
    + auto. 
    + tauto.
    + inversion E.
  - unfold value_v. bdestruct (eqbv x n).
    destruct classicT.
    + inversion E.
    + tauto.
    + simpl. destruct classicT; try tauto. subst; tauto. 
Qed.

Fact sub_2 : forall (n: Con), sub_t (Tcon n).
Proof.
  red. intros. simpl. auto.
Qed.

Fact sub_3 : forall (t0: Vector.t term 0), sub_v 0 t0.
Proof.
  red. intros. apply case0. set(fun t1 =>
  Vector.map (u//) (substitute_v 0 t1 t' x) = 
  nil M). apply (case0 P). unfold P. simpl. auto. 
Qed.

Fact sub_4 : forall (f: Fun) (v: Vector.t term (arity_F f)),
  sub_v (arity_F f) v -> sub_t (Tfun f v).
Proof.
  intros. red. intros. simpl. f_equal. apply H.
Qed.

Fact sub_5 : forall (n: nat) (t0: term) (t1: Vector.t term n),
  sub_t t0 -> sub_v n t1 -> sub_v (S n) (t0 :: t1).
Proof.
  intros. red. intros. red in H,H0. pose proof (H MM u t' x). 
  pose proof (H0 MM u x t'). simpl. congruence.
Qed.

(* 归纳证明 *)
(* 项的归纳函数 *)
Section term_ind_process.
Variable P : term -> Prop.
Variable P0 : forall n, Vector.t term n -> Prop.
Variable varcase : forall n, P (Tvar n).
Variable concase : forall n, P (Tcon n).
Variable nilcase : forall s, P0 0 s.
Variable applycase :
  forall (f: Fun) (v: t term (arity_F f)), 
  P0 (arity_F f) v -> P (Tfun _ v).
Variable conscase : forall (n: nat) (s: term) (t0: Vector.t term n),
  P s -> P0 n t0 -> P0 (S n) (s :: t0).
Fixpoint Term_ind_new (s: term) : P s :=
  let fix Terms_ind (n: nat) (vec: (Vector.t term n)) 
  {struct vec} : P0 n vec:=
  match vec in (t _ n) return (P0 n vec) with
  | nil _ => nilcase (nil _)
  | cons _ t0 m ts =>
    conscase m t0 ts (Term_ind_new t0) (Terms_ind m ts)
  end in match s with
         | Tvar r => varcase r
         | Tcon r => concase r
         | Tfun f ts => applycase f ts (Terms_ind _ ts)
         end.
End term_ind_process.

Theorem term_substitution_theorem : forall t, sub_t t. 
Proof.
  apply Term_ind_new with sub_v.
  - apply sub_1.
  - apply sub_2.
  - apply sub_3.
  - apply sub_4.
  - apply sub_5.
Qed.
















