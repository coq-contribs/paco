(** * Common notations and definitions *)

(** ** Types of dependent predicates *)

Definition rel0 := Prop.
Implicit Arguments rel0 [].

Definition rel1 A := 
  forall (a: A), Prop.
Implicit Arguments rel1 [].

Definition rel2 A B := 
  forall (a: A) (b: B a), Prop.
Implicit Arguments rel2 [].

Definition rel3 A B C := 
  forall (a: A) (b: B a) (c: C a b), Prop.
Implicit Arguments rel3 [].

Definition rel4 A B C D := 
  forall (a: A) (b: B a) (c: C a b) (d: D a b c), Prop.
Implicit Arguments rel4 [].

Definition rel5 A B C D E := 
  forall (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d), Prop.
Implicit Arguments rel5 [].

Definition rel6 A B C D E F := 
  forall (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d) (f: F a b c d e), Prop.
Implicit Arguments rel6 [].

Definition rel7 A B C D E F G := 
  forall (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d) (f: F a b c d e) (g: G a b c d e f), Prop.
Implicit Arguments rel7 [].

Definition rel8 A B C D E F G H := 
  forall (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d) (f: F a b c d e) (g: G a b c d e f) (h: H a b c d e f g), Prop.
Implicit Arguments rel8 [].

(** ** Less than or equal *)

Notation "p <0= q" := 
  (forall (PR: p : Prop), q : Prop) 
  (at level 50, no associativity).

Notation "p <1= q" := 
  (forall a (PR: p a : Prop), q a : Prop) 
  (at level 50, no associativity).

Notation "p <2= q" := 
  (forall a b (PR: p a b : Prop), q a b : Prop) 
  (at level 50, no associativity).

Notation "p <3= q" := 
  (forall a b c (PR: p a b c : Prop), q a b c : Prop) 
  (at level 50, no associativity).

Notation "p <4= q" := 
  (forall a b c d (PR: p a b c d : Prop), q a b c d : Prop) 
  (at level 50, no associativity).

Notation "p <5= q" := 
  (forall a b c d e (PR: p a b c d e : Prop), q a b c d e : Prop) 
  (at level 50, no associativity).

Notation "p <6= q" := 
  (forall a b c d e f (PR: p a b c d e f : Prop), q a b c d e f : Prop) 
  (at level 50, no associativity).

Notation "p <7= q" := 
  (forall a b c d e f g (PR: p a b c d e f g : Prop), q a b c d e f g : Prop) 
  (at level 50, no associativity).

Notation "p <8= q" := 
  (forall a b c d e f g h (PR: p a b c d e f g h : Prop), q a b c d e f g h : Prop) 
  (at level 50, no associativity).

(** ** Union *)

Notation "p \0/ q" := 
  (p \/ q) 
  (at level 50, no associativity, only parsing).

Notation "p \1/ q" := 
  (fun a => p a \/ q a) 
  (at level 50, no associativity).

Notation "p \2/ q" := 
  (fun a b => p a b \/ q a b) 
  (at level 50, no associativity).

Notation "p \3/ q" := 
  (fun a b c => p a b c \/ q a b c) 
  (at level 50, no associativity).

Notation "p \4/ q" := 
  (fun a b c d => p a b c d \/ q a b c d) 
  (at level 50, no associativity).

Notation "p \5/ q" := 
  (fun a b c d e => p a b c d e \/ q a b c d e) 
  (at level 50, no associativity).

Notation "p \6/ q" := 
  (fun a b c d e f => p a b c d e f \/ q a b c d e f) 
  (at level 50, no associativity).

Notation "p \7/ q" := 
  (fun a b c d e f g => p a b c d e f g \/ q a b c d e f g) 
  (at level 50, no associativity).

Notation "p \8/ q" := 
  (fun a b c d e f g h => p a b c d e f g h \/ q a b c d e f g h) 
  (at level 50, no associativity).

(** ** Bottom *)

Definition bot0 : Prop :=
  False.

Definition bot1 {A} :=
  fun (a: A) => False.

Definition bot2 {A B} := 
  fun (a: A) (b: B a) => False.

Definition bot3 {A B C} := 
  fun (a: A) (b: B a) (c: C a b) => False.

Definition bot4 {A B C D} := 
  fun (a: A) (b: B a) (c: C a b) (d: D a b c) => False.

Definition bot5 {A B C D E} := 
  fun (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d) => False.

Definition bot6 {A B C D E F} := 
  fun (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d)
      (f: F a b c d e) => False.

Definition bot7 {A B C D E F G} := 
  fun (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d)
      (f: F a b c d e) (g: G a b c d e f) => False.

Definition bot8 {A B C D E F G H} :=
  fun (a: A) (b: B a) (c: C a b) (d: D a b c) (e: E a b c d)
      (f: F a b c d e) (g: G a b c d e f) (h: H a b c d e f g) => False.

