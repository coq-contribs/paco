Require Export paconotation.
Require Import pacotac.
Set Implicit Arguments.

(** * Formalization of Parameterized Coinduction: the Internal Approach 

    We support predicates of arity up to 8 and use the strict
    positivization trick (Section 6.1 of the paper) in order to define
    G for arbitrary functions (here called pacoN).
*)

(** Tactics for Internal Use Only *)

Local Ltac paco_cofix_auto :=
  cofix; repeat intro;
  match goal with [H: _ |- _] => destruct H end; econstructor; 
  try (match goal with [H: _|-_] => apply H end); intros; 
  lazymatch goal with [PR: _ |- _] => match goal with [H: _ |- _] => apply H in PR end end; 
  repeat match goal with [ H : _ \/ _ |- _] => destruct H end; first [eauto; fail|eauto 10].

Local Ltac paco_revert := 
  match goal with [H: _ |- _] => revert H end.

(** ** Predicates of arity 0 
*)

(** Single Coinduction *)

Section Arg0Single.

Definition monotone0 (gf: rel0 -> rel0) := 
  forall r r' (IN: gf r) (LE: r <0= r'), gf r'.

Variable gf : rel0 -> rel0.
Implicit Arguments gf [].

CoInductive paco0 r : Prop :=
| paco0_pfold pco
    (LE : pco <0= (paco0 r \0/ r))
    (SIM: gf pco)
.
Implicit Arguments paco0 [].

Theorem paco0_acc: forall
    l r (OBG: forall rr (INC: r <0= rr) (CIH: l <0= rr), l <0= paco0 rr),
  l <0= paco0 r.
Proof.
  intros; assert (SIM: paco0 (r \0/ l)) by eauto.
  clear PR; paco_revert; paco_cofix_auto.
Qed.

Theorem paco0_mon: monotone0 paco0.
Proof. paco_cofix_auto. Qed.

Theorem paco0_mult_strong: forall r,
  paco0 (paco0 r \0/ r) <0= paco0 r.
Proof. paco_cofix_auto. Qed.

Corollary paco0_mult: forall r,
  paco0 (paco0 r) <0= paco0 r.
Proof. intros; eapply paco0_mult_strong, paco0_mon; eauto. Qed.

Theorem paco0_fold: forall r,
  gf (paco0 r \0/ r) <0= paco0 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco0_unfold: forall (MON: monotone0 gf) r,
  paco0 r <0= gf (paco0 r \0/ r).
Proof. unfold monotone0; intros; destruct PR; eauto. Qed.

End Arg0Single.

Hint Unfold monotone0.
Hint Resolve paco0_fold.

Implicit Arguments paco0_mon            [].
Implicit Arguments paco0_mult_strong    [].
Implicit Arguments paco0_mult           [].

(** Two Mutual Coinduction *)

Section Arg0Two.

Definition monotone0' (gf: rel0 -> rel0 -> rel0) := 
  forall ra ra' rb rb' (IN: gf ra rb) (LEa: ra <0= ra') (LEb: rb <0= rb'), gf ra' rb'.

Variables gfa gfb : rel0 -> rel0 -> rel0.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco0'a ra rb : Prop :=
| paco0'a_pfold pcoa pcob
    (LEa : pcoa <0= (paco0'a ra rb \0/ ra))
    (LEb : pcob <0= (paco0'b ra rb \0/ rb))
    (SIM: gfa pcoa pcob)
with paco0'b ra rb : Prop :=
| paco0'b_pfold pcoa pcob
    (LEa : pcoa <0= (paco0'a ra rb \0/ ra))
    (LEb : pcob <0= (paco0'b ra rb \0/ rb))
    (SIM: gfb pcoa pcob)
.
Implicit Arguments paco0'a [].
Implicit Arguments paco0'b [].

Theorem paco0'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <0= rr) (CIH: l <0= rr), l <0= paco0'a rr rb),
  l <0= paco0'a ra rb.
Proof.
  intros; assert (SIM: paco0'a (ra \0/ l) rb) by eauto.
  clear PR; repeat (try left; paco_revert; paco_cofix_auto).
Qed.

Theorem paco0'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <0= rr) (CIH: l <0= rr), l <0= paco0'b ra rr),
  l <0= paco0'b ra rb.
Proof.
  intros; assert (SIM: paco0'b ra (rb \0/ l)) by eauto.
  clear PR; repeat (try left; paco_revert; paco_cofix_auto).
Qed.

Theorem paco0'a_mon: monotone0' paco0'a.
Proof. paco_cofix_auto; left; paco_revert; paco_cofix_auto. Qed.

Theorem paco0'b_mon: monotone0' paco0'b.
Proof. paco_cofix_auto; left; paco_revert; paco_cofix_auto. Qed.

Theorem paco0'a_mult_strong: forall ra rb,
  paco0'a (paco0'a ra rb \0/ ra) (paco0'b ra rb \0/ rb) <0= paco0'a ra rb.
Proof. paco_cofix_auto; left; paco_revert; paco_cofix_auto. Qed.

Theorem paco0'b_mult_strong: forall ra rb,
  paco0'b (paco0'a ra rb \0/ ra) (paco0'b ra rb \0/ rb) <0= paco0'b ra rb.
Proof. paco_cofix_auto; left; paco_revert; paco_cofix_auto. Qed.

Corollary paco0'a_mult: forall ra rb,
  paco0'a (paco0'a ra rb) (paco0'b ra rb) <0= paco0'a ra rb.
Proof. intros; eapply paco0'a_mult_strong, paco0'a_mon; eauto. Qed.

Corollary paco0'b_mult: forall ra rb,
  paco0'b (paco0'a ra rb) (paco0'b ra rb) <0= paco0'b ra rb.
Proof. intros; eapply paco0'b_mult_strong, paco0'b_mon; eauto. Qed.

Theorem paco0'a_fold: forall ra rb,
  gfa (paco0'a ra rb \0/ ra) (paco0'b ra rb \0/ rb) <0= paco0'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco0'b_fold: forall ra rb,
  gfb (paco0'a ra rb \0/ ra) (paco0'b ra rb \0/ rb) <0= paco0'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco0'a_unfold: forall
    (MONa: monotone0' gfa) (MONb: monotone0' gfb) ra rb,
  paco0'a ra rb 
  <0= gfa (paco0'a ra rb \0/ ra) (paco0'b ra rb \0/ rb).
Proof. unfold monotone0'; intros; destruct PR; eauto. Qed.

Theorem paco0'b_unfold: forall
    (MONa: monotone0' gfa) (MONb: monotone0' gfb) ra rb,
  paco0'b ra rb 
  <0= gfb (paco0'a ra rb \0/ ra) (paco0'b ra rb \0/ rb).
Proof. unfold monotone0'; intros; destruct PR; eauto. Qed.

End Arg0Two.

Hint Unfold monotone0'.
Hint Resolve paco0'a_fold.
Hint Resolve paco0'b_fold.

Implicit Arguments paco0'a_mon          [].
Implicit Arguments paco0'b_mon          [].
Implicit Arguments paco0'a_mult_strong  [].
Implicit Arguments paco0'b_mult_strong  [].
Implicit Arguments paco0'a_mult         [].
Implicit Arguments paco0'b_mult         [].

(** Three Mutual Coinduction *)

Section Arg0Three.

Definition monotone0'' (gf: rel0 -> rel0 -> rel0 -> rel0) := 
  forall ra ra' rb rb' rc rc' (IN: gf ra rb rc) (LEa: ra <0= ra') (LEb: rb <0= rb') (LEc: rc <0= rc'), gf ra' rb' rc'.

Variables gfa gfb gfc : rel0 -> rel0 -> rel0 -> rel0.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco0''a ra rb rc : Prop :=
| paco0''a_pfold pcoa pcob pcoc
    (LEa : pcoa <0= (paco0''a ra rb rc \0/ ra))
    (LEb : pcob <0= (paco0''b ra rb rc \0/ rb))
    (LEc : pcoc <0= (paco0''c ra rb rc \0/ rc))
    (SIM: gfa pcoa pcob pcoc)
with paco0''b ra rb rc : Prop :=
| paco0''b_pfold pcoa pcob pcoc
    (LEa : pcoa <0= (paco0''a ra rb rc \0/ ra))
    (LEb : pcob <0= (paco0''b ra rb rc \0/ rb))
    (LEc : pcoc <0= (paco0''c ra rb rc \0/ rc))
    (SIM: gfb pcoa pcob pcoc)
with paco0''c ra rb rc : Prop :=
| paco0''c_pfold pcoa pcob pcoc
    (LEa : pcoa <0= (paco0''a ra rb rc \0/ ra))
    (LEb : pcob <0= (paco0''b ra rb rc \0/ rb))
    (LEc : pcoc <0= (paco0''c ra rb rc \0/ rc))
    (SIM: gfc pcoa pcob pcoc)
.
Implicit Arguments paco0''a [].
Implicit Arguments paco0''b [].
Implicit Arguments paco0''c [].

Theorem paco0''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <0= rr) (CIH: l <0= rr), l <0= paco0''a rr rb rc),
  l <0= paco0''a ra rb rc.
Proof.
  intros; assert (SIM: paco0''a (ra \0/ l) rb rc) by eauto.
  clear PR; repeat (try left; paco_revert; paco_cofix_auto).
Qed.

Theorem paco0''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <0= rr) (CIH: l <0= rr), l <0= paco0''b ra rr rc),
  l <0= paco0''b ra rb rc.
Proof.
  intros; assert (SIM: paco0''b ra (rb \0/ l) rc) by eauto.
  clear PR; repeat (try left; paco_revert; paco_cofix_auto).
Qed.

Theorem paco0''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <0= rr) (CIH: l <0= rr), l <0= paco0''c ra rb rr),
  l <0= paco0''c ra rb rc.
Proof.
  intros; assert (SIM: paco0''c ra rb (rc \0/ l)) by eauto.
  clear PR; repeat (try left; paco_revert; paco_cofix_auto).
Qed.

Theorem paco0''a_mon: monotone0'' paco0''a.
Proof. paco_cofix_auto; repeat (left; paco_revert; paco_cofix_auto). Qed.

Theorem paco0''b_mon: monotone0'' paco0''b.
Proof. paco_cofix_auto; repeat (left; paco_revert; paco_cofix_auto). Qed.

Theorem paco0''c_mon: monotone0'' paco0''c.
Proof. paco_cofix_auto; repeat (left; paco_revert; paco_cofix_auto). Qed.

Theorem paco0''a_mult_strong: forall ra rb rc,
  paco0''a (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc)
  <0= paco0''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; paco_revert; paco_cofix_auto). Qed.

Theorem paco0''b_mult_strong: forall ra rb rc,
  paco0''b (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc)
  <0= paco0''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; paco_revert; paco_cofix_auto). Qed.

Theorem paco0''c_mult_strong: forall ra rb rc,
  paco0''c (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc)
  <0= paco0''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; paco_revert; paco_cofix_auto). Qed.

Corollary paco0''a_mult: forall ra rb rc,
  paco0''a (paco0''a ra rb rc) (paco0''b ra rb rc) (paco0''c ra rb rc)
  <0= paco0''a ra rb rc.
Proof. intros; eapply paco0''a_mult_strong, paco0''a_mon; eauto. Qed.

Corollary paco0''b_mult: forall ra rb rc,
  paco0''b (paco0''a ra rb rc) (paco0''b ra rb rc) (paco0''c ra rb rc)
  <0= paco0''b ra rb rc.
Proof. intros; eapply paco0''b_mult_strong, paco0''b_mon; eauto. Qed.

Corollary paco0''c_mult: forall ra rb rc,
  paco0''c (paco0''a ra rb rc) (paco0''b ra rb rc) (paco0''c ra rb rc)
  <0= paco0''c ra rb rc.
Proof. intros; eapply paco0''c_mult_strong, paco0''c_mon; eauto. Qed.

Theorem paco0''a_fold: forall ra rb rc,
  gfa (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc) 
  <0= paco0''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco0''b_fold: forall ra rb rc,
  gfb (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc) 
  <0= paco0''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco0''c_fold: forall ra rb rc,
  gfc (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc) 
  <0= paco0''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco0''a_unfold: forall
    (MONa: monotone0'' gfa) (MONb: monotone0'' gfb) (MONc: monotone0'' gfc) ra rb rc,
  paco0''a ra rb rc
  <0= gfa (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc).
Proof. unfold monotone0''; intros; destruct PR; eauto. Qed.

Theorem paco0''b_unfold: forall
    (MONa: monotone0'' gfa) (MONb: monotone0'' gfb) (MONc: monotone0'' gfc) ra rb rc,
  paco0''b ra rb rc
  <0= gfb (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc).
Proof. unfold monotone0''; intros; destruct PR; eauto. Qed.

Theorem paco0''c_unfold: forall
    (MONa: monotone0'' gfa) (MONb: monotone0'' gfb) (MONc: monotone0'' gfc) ra rb rc,
  paco0''c ra rb rc
  <0= gfc (paco0''a ra rb rc \0/ ra) (paco0''b ra rb rc \0/ rb) (paco0''c ra rb rc \0/ rc).
Proof. unfold monotone0''; intros; destruct PR; eauto. Qed.

End Arg0Three.

Hint Unfold monotone0''.
Hint Resolve paco0''a_fold.
Hint Resolve paco0''b_fold.
Hint Resolve paco0''c_fold.

Implicit Arguments paco0''a_mon         [].
Implicit Arguments paco0''b_mon         [].
Implicit Arguments paco0''c_mon         [].
Implicit Arguments paco0''a_mult_strong [].
Implicit Arguments paco0''b_mult_strong [].
Implicit Arguments paco0''c_mult_strong [].
Implicit Arguments paco0''a_mult        [].
Implicit Arguments paco0''b_mult        [].
Implicit Arguments paco0''c_mult        [].

(** ** Predicates of arity 1 
*)

(** Single Coinduction *)

Section Arg1Single.

Definition monotone1 A (gf: rel1 A -> rel1 A) := 
  forall a r r' (IN: gf r a) (LE: r <1= r'), gf r' a.

Variable A : Type.
Variable gf : rel1 A -> rel1 A.
Implicit Arguments gf [].

CoInductive paco1 r a : Prop :=
| paco1_pfold pco
    (LE : pco <1= (paco1 r \1/ r))
    (SIM: gf pco a)
.
Implicit Arguments paco1 [].

Theorem paco1_acc: forall
    l r (OBG: forall rr (INC: r <1= rr) (CIH: l <1= rr), l <1= paco1 rr),
  l <1= paco1 r.
Proof.
  intros; assert (SIM: paco1 (r \1/ l) a) by eauto.
  clear PR; do 2 paco_revert; paco_cofix_auto.
Qed.

Theorem paco1_mon: monotone1 paco1.
Proof. paco_cofix_auto. Qed.

Theorem paco1_mult_strong: forall r,
  paco1 (paco1 r \1/ r) <1= paco1 r.
Proof. paco_cofix_auto. Qed.

Corollary paco1_mult: forall r,
  paco1 (paco1 r) <1= paco1 r.
Proof. intros; eapply paco1_mult_strong, paco1_mon; eauto. Qed.

Theorem paco1_fold: forall r,
  gf (paco1 r \1/ r) <1= paco1 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco1_unfold: forall (MON: monotone1 gf) r,
  paco1 r <1= gf (paco1 r \1/ r).
Proof. unfold monotone1; intros; destruct PR; eauto. Qed.

End Arg1Single.

Hint Unfold monotone1.
Hint Resolve paco1_fold.

Implicit Arguments paco1_mon            [A].
Implicit Arguments paco1_mult_strong    [A].
Implicit Arguments paco1_mult           [A].

(** Two Mutual Coinduction *)

Section Arg1Two.

Definition monotone1' A (gf: rel1 A -> rel1 A -> rel1 A) := 
  forall a ra ra' rb rb' (IN: gf ra rb a) (LEa: ra <1= ra') (LEb: rb <1= rb'), gf ra' rb' a.

Variable A : Type.
Variables gfa gfb : rel1 A -> rel1 A -> rel1 A.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco1'a ra rb a : Prop :=
| paco1'a_pfold pcoa pcob
    (LEa : pcoa <1= (paco1'a ra rb \1/ ra))
    (LEb : pcob <1= (paco1'b ra rb \1/ rb))
    (SIM: gfa pcoa pcob a)
with paco1'b ra rb a : Prop :=
| paco1'b_pfold pcoa pcob
    (LEa : pcoa <1= (paco1'a ra rb \1/ ra))
    (LEb : pcob <1= (paco1'b ra rb \1/ rb))
    (SIM: gfb pcoa pcob a)
.
Implicit Arguments paco1'a [].
Implicit Arguments paco1'b [].

Theorem paco1'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <1= rr) (CIH: l <1= rr), l <1= paco1'a rr rb),
  l <1= paco1'a ra rb.
Proof.
  intros; assert (SIM: paco1'a (ra \1/ l) rb a) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <1= rr) (CIH: l <1= rr), l <1= paco1'b ra rr),
  l <1= paco1'b ra rb.
Proof.
  intros; assert (SIM: paco1'b ra (rb \1/ l) a) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1'a_mon: monotone1' paco1'a.
Proof. paco_cofix_auto; left; do 2 paco_revert; paco_cofix_auto. Qed.

Theorem paco1'b_mon: monotone1' paco1'b.
Proof. paco_cofix_auto; left; do 2 paco_revert; paco_cofix_auto. Qed.

Theorem paco1'a_mult_strong: forall ra rb,
  paco1'a (paco1'a ra rb \1/ ra) (paco1'b ra rb \1/ rb) <1= paco1'a ra rb.
Proof. paco_cofix_auto; left; do 2 paco_revert; paco_cofix_auto. Qed.

Theorem paco1'b_mult_strong: forall ra rb,
  paco1'b (paco1'a ra rb \1/ ra) (paco1'b ra rb \1/ rb) <1= paco1'b ra rb.
Proof. paco_cofix_auto; left; do 2 paco_revert; paco_cofix_auto. Qed.

Corollary paco1'a_mult: forall ra rb,
  paco1'a (paco1'a ra rb) (paco1'b ra rb) <1= paco1'a ra rb.
Proof. intros; eapply paco1'a_mult_strong, paco1'a_mon; eauto. Qed.

Corollary paco1'b_mult: forall ra rb,
  paco1'b (paco1'a ra rb) (paco1'b ra rb) <1= paco1'b ra rb.
Proof. intros; eapply paco1'b_mult_strong, paco1'b_mon; eauto. Qed.

Theorem paco1'a_fold: forall ra rb,
  gfa (paco1'a ra rb \1/ ra) (paco1'b ra rb \1/ rb) <1= paco1'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco1'b_fold: forall ra rb,
  gfb (paco1'a ra rb \1/ ra) (paco1'b ra rb \1/ rb) <1= paco1'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco1'a_unfold: forall
    (MONa: monotone1' gfa) (MONb: monotone1' gfb) ra rb,
  paco1'a ra rb 
  <1= gfa (paco1'a ra rb \1/ ra) (paco1'b ra rb \1/ rb).
Proof. unfold monotone1'; intros; destruct PR; eauto. Qed.

Theorem paco1'b_unfold: forall
    (MONa: monotone1' gfa) (MONb: monotone1' gfb) ra rb,
  paco1'b ra rb 
  <1= gfb (paco1'a ra rb \1/ ra) (paco1'b ra rb \1/ rb).
Proof. unfold monotone1'; intros; destruct PR; eauto. Qed.

End Arg1Two.

Hint Unfold monotone1'.
Hint Resolve paco1'a_fold.
Hint Resolve paco1'b_fold.

Implicit Arguments paco1'a_mon          [A].
Implicit Arguments paco1'b_mon          [A].
Implicit Arguments paco1'a_mult_strong  [A].
Implicit Arguments paco1'b_mult_strong  [A].
Implicit Arguments paco1'a_mult         [A].
Implicit Arguments paco1'b_mult         [A].

(** Three Mutual Coinduction *)

Section Arg1Three.

Definition monotone1'' A (gf: rel1 A -> rel1 A -> rel1 A -> rel1 A) := 
  forall a ra ra' rb rb' rc rc' (IN: gf ra rb rc a) (LEa: ra <1= ra') (LEb: rb <1= rb') (LEc: rc <1= rc'), gf ra' rb' rc' a.

Variable A : Type.
Variables gfa gfb gfc : rel1 A -> rel1 A -> rel1 A -> rel1 A.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco1''a ra rb rc a : Prop :=
| paco1''a_pfold pcoa pcob pcoc
    (LEa : pcoa <1= (paco1''a ra rb rc \1/ ra))
    (LEb : pcob <1= (paco1''b ra rb rc \1/ rb))
    (LEc : pcoc <1= (paco1''c ra rb rc \1/ rc))
    (SIM: gfa pcoa pcob pcoc a)
with paco1''b ra rb rc a : Prop :=
| paco1''b_pfold pcoa pcob pcoc
    (LEa : pcoa <1= (paco1''a ra rb rc \1/ ra))
    (LEb : pcob <1= (paco1''b ra rb rc \1/ rb))
    (LEc : pcoc <1= (paco1''c ra rb rc \1/ rc))
    (SIM: gfb pcoa pcob pcoc a)
with paco1''c ra rb rc a : Prop :=
| paco1''c_pfold pcoa pcob pcoc
    (LEa : pcoa <1= (paco1''a ra rb rc \1/ ra))
    (LEb : pcob <1= (paco1''b ra rb rc \1/ rb))
    (LEc : pcoc <1= (paco1''c ra rb rc \1/ rc))
    (SIM: gfc pcoa pcob pcoc a)
.
Implicit Arguments paco1''a [].
Implicit Arguments paco1''b [].
Implicit Arguments paco1''c [].

Theorem paco1''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <1= rr) (CIH: l <1= rr), l <1= paco1''a rr rb rc),
  l <1= paco1''a ra rb rc.
Proof.
  intros; assert (SIM: paco1''a (ra \1/ l) rb rc a) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <1= rr) (CIH: l <1= rr), l <1= paco1''b ra rr rc),
  l <1= paco1''b ra rb rc.
Proof.
  intros; assert (SIM: paco1''b ra (rb \1/ l) rc a) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <1= rr) (CIH: l <1= rr), l <1= paco1''c ra rb rr),
  l <1= paco1''c ra rb rc.
Proof.
  intros; assert (SIM: paco1''c ra rb (rc \1/ l) a) by eauto.
  clear PR; repeat (try left; do 2 paco_revert; paco_cofix_auto).
Qed.

Theorem paco1''a_mon: monotone1'' paco1''a.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1''b_mon: monotone1'' paco1''b.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1''c_mon: monotone1'' paco1''c.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1''a_mult_strong: forall ra rb rc,
  paco1''a (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc)
  <1= paco1''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1''b_mult_strong: forall ra rb rc,
  paco1''b (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc)
  <1= paco1''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Theorem paco1''c_mult_strong: forall ra rb rc,
  paco1''c (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc)
  <1= paco1''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 2 paco_revert; paco_cofix_auto). Qed.

Corollary paco1''a_mult: forall ra rb rc,
  paco1''a (paco1''a ra rb rc) (paco1''b ra rb rc) (paco1''c ra rb rc)
  <1= paco1''a ra rb rc.
Proof. intros; eapply paco1''a_mult_strong, paco1''a_mon; eauto. Qed.

Corollary paco1''b_mult: forall ra rb rc,
  paco1''b (paco1''a ra rb rc) (paco1''b ra rb rc) (paco1''c ra rb rc)
  <1= paco1''b ra rb rc.
Proof. intros; eapply paco1''b_mult_strong, paco1''b_mon; eauto. Qed.

Corollary paco1''c_mult: forall ra rb rc,
  paco1''c (paco1''a ra rb rc) (paco1''b ra rb rc) (paco1''c ra rb rc)
  <1= paco1''c ra rb rc.
Proof. intros; eapply paco1''c_mult_strong, paco1''c_mon; eauto. Qed.

Theorem paco1''a_fold: forall ra rb rc,
  gfa (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc) 
  <1= paco1''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco1''b_fold: forall ra rb rc,
  gfb (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc) 
  <1= paco1''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco1''c_fold: forall ra rb rc,
  gfc (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc) 
  <1= paco1''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco1''a_unfold: forall
    (MONa: monotone1'' gfa) (MONb: monotone1'' gfb) (MONc: monotone1'' gfc) ra rb rc,
  paco1''a ra rb rc
  <1= gfa (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc).
Proof. unfold monotone1''; intros; destruct PR; eauto. Qed.

Theorem paco1''b_unfold: forall
    (MONa: monotone1'' gfa) (MONb: monotone1'' gfb) (MONc: monotone1'' gfc) ra rb rc,
  paco1''b ra rb rc
  <1= gfb (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc).
Proof. unfold monotone1''; intros; destruct PR; eauto. Qed.

Theorem paco1''c_unfold: forall
    (MONa: monotone1'' gfa) (MONb: monotone1'' gfb) (MONc: monotone1'' gfc) ra rb rc,
  paco1''c ra rb rc
  <1= gfc (paco1''a ra rb rc \1/ ra) (paco1''b ra rb rc \1/ rb) (paco1''c ra rb rc \1/ rc).
Proof. unfold monotone1''; intros; destruct PR; eauto. Qed.

End Arg1Three.

Hint Unfold monotone1''.
Hint Resolve paco1''a_fold.
Hint Resolve paco1''b_fold.
Hint Resolve paco1''c_fold.

Implicit Arguments paco1''a_mon         [A].
Implicit Arguments paco1''b_mon         [A].
Implicit Arguments paco1''c_mon         [A].
Implicit Arguments paco1''a_mult_strong [A].
Implicit Arguments paco1''b_mult_strong [A].
Implicit Arguments paco1''c_mult_strong [A].
Implicit Arguments paco1''a_mult        [A].
Implicit Arguments paco1''b_mult        [A].
Implicit Arguments paco1''c_mult        [A].

(** ** Predicates of arity 2 
*)

(** Single Coinduction *)

Section Arg2Single.

Definition monotone2 A B (gf: rel2 A B -> rel2 A B) := 
  forall a b r r' (IN: gf r a b) (LE: r <2= r'), gf r' a b.

Variable A : Type.
Variable B : forall a: A, Type.
Variable gf : rel2 A B -> rel2 A B.
Implicit Arguments gf [].

CoInductive paco2 r a b : Prop :=
| paco2_pfold pco
    (LE : pco <2= (paco2 r \2/ r))
    (SIM: gf pco a b)
.
Implicit Arguments paco2 [].

Theorem paco2_acc: forall
    l r (OBG: forall rr (INC: r <2= rr) (CIH: l <2= rr), l <2= paco2 rr),
  l <2= paco2 r.
Proof.
  intros; assert (SIM: paco2 (r \2/ l) a b) by eauto.
  clear PR; do 3 paco_revert; paco_cofix_auto.
Qed.

Theorem paco2_mon: monotone2 paco2.
Proof. paco_cofix_auto. Qed.

Theorem paco2_mult_strong: forall r,
  paco2 (paco2 r \2/ r) <2= paco2 r.
Proof. paco_cofix_auto. Qed.

Corollary paco2_mult: forall r,
  paco2 (paco2 r) <2= paco2 r.
Proof. intros; eapply paco2_mult_strong, paco2_mon; eauto. Qed.

Theorem paco2_fold: forall r,
  gf (paco2 r \2/ r) <2= paco2 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco2_unfold: forall (MON: monotone2 gf) r,
  paco2 r <2= gf (paco2 r \2/ r).
Proof. unfold monotone2; intros; destruct PR; eauto. Qed.

End Arg2Single.

Hint Unfold monotone2.
Hint Resolve paco2_fold.

Implicit Arguments paco2_mon            [A B].
Implicit Arguments paco2_mult_strong    [A B].
Implicit Arguments paco2_mult           [A B].

(** Two Mutual Coinduction *)

Section Arg2Two.

Definition monotone2' A B (gf: rel2 A B -> rel2 A B -> rel2 A B) := 
  forall a b ra ra' rb rb' (IN: gf ra rb a b) (LEa: ra <2= ra') (LEb: rb <2= rb'), gf ra' rb' a b.

Variable A : Type.
Variable B : forall a: A, Type.
Variables gfa gfb : rel2 A B -> rel2 A B -> rel2 A B.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco2'a ra rb a b : Prop :=
| paco2'a_pfold pcoa pcob
    (LEa : pcoa <2= (paco2'a ra rb \2/ ra))
    (LEb : pcob <2= (paco2'b ra rb \2/ rb))
    (SIM: gfa pcoa pcob a b)
with paco2'b ra rb a b : Prop :=
| paco2'b_pfold pcoa pcob
    (LEa : pcoa <2= (paco2'a ra rb \2/ ra))
    (LEb : pcob <2= (paco2'b ra rb \2/ rb))
    (SIM: gfb pcoa pcob a b)
.
Implicit Arguments paco2'a [].
Implicit Arguments paco2'b [].

Theorem paco2'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <2= rr) (CIH: l <2= rr), l <2= paco2'a rr rb),
  l <2= paco2'a ra rb.
Proof.
  intros; assert (SIM: paco2'a (ra \2/ l) rb a b) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <2= rr) (CIH: l <2= rr), l <2= paco2'b ra rr),
  l <2= paco2'b ra rb.
Proof.
  intros; assert (SIM: paco2'b ra (rb \2/ l) a b) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2'a_mon: monotone2' paco2'a.
Proof. paco_cofix_auto; left; do 3 paco_revert; paco_cofix_auto. Qed.

Theorem paco2'b_mon: monotone2' paco2'b.
Proof. paco_cofix_auto; left; do 3 paco_revert; paco_cofix_auto. Qed.

Theorem paco2'a_mult_strong: forall ra rb,
  paco2'a (paco2'a ra rb \2/ ra) (paco2'b ra rb \2/ rb) <2= paco2'a ra rb.
Proof. paco_cofix_auto; left; do 3 paco_revert; paco_cofix_auto. Qed.

Theorem paco2'b_mult_strong: forall ra rb,
  paco2'b (paco2'a ra rb \2/ ra) (paco2'b ra rb \2/ rb) <2= paco2'b ra rb.
Proof. paco_cofix_auto; left; do 3 paco_revert; paco_cofix_auto. Qed.

Corollary paco2'a_mult: forall ra rb,
  paco2'a (paco2'a ra rb) (paco2'b ra rb) <2= paco2'a ra rb.
Proof. intros; eapply paco2'a_mult_strong, paco2'a_mon; eauto. Qed.

Corollary paco2'b_mult: forall ra rb,
  paco2'b (paco2'a ra rb) (paco2'b ra rb) <2= paco2'b ra rb.
Proof. intros; eapply paco2'b_mult_strong, paco2'b_mon; eauto. Qed.

Theorem paco2'a_fold: forall ra rb,
  gfa (paco2'a ra rb \2/ ra) (paco2'b ra rb \2/ rb) <2= paco2'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco2'b_fold: forall ra rb,
  gfb (paco2'a ra rb \2/ ra) (paco2'b ra rb \2/ rb) <2= paco2'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco2'a_unfold: forall
    (MONa: monotone2' gfa) (MONb: monotone2' gfb) ra rb,
  paco2'a ra rb 
  <2= gfa (paco2'a ra rb \2/ ra) (paco2'b ra rb \2/ rb).
Proof. unfold monotone2'; intros; destruct PR; eauto. Qed.

Theorem paco2'b_unfold: forall
    (MONa: monotone2' gfa) (MONb: monotone2' gfb) ra rb,
  paco2'b ra rb 
  <2= gfb (paco2'a ra rb \2/ ra) (paco2'b ra rb \2/ rb).
Proof. unfold monotone2'; intros; destruct PR; eauto. Qed.

End Arg2Two.

Hint Unfold monotone2'.
Hint Resolve paco2'a_fold.
Hint Resolve paco2'b_fold.

Implicit Arguments paco2'a_mon          [A B].
Implicit Arguments paco2'b_mon          [A B].
Implicit Arguments paco2'a_mult_strong  [A B].
Implicit Arguments paco2'b_mult_strong  [A B].
Implicit Arguments paco2'a_mult         [A B].
Implicit Arguments paco2'b_mult         [A B].

(** Three Mutual Coinduction *)

Section Arg2Three.

Definition monotone2'' A B (gf: rel2 A B -> rel2 A B -> rel2 A B -> rel2 A B) := 
  forall a b ra ra' rb rb' rc rc' (IN: gf ra rb rc a b) (LEa: ra <2= ra') (LEb: rb <2= rb') (LEc: rc <2= rc'), gf ra' rb' rc' a b.

Variable A : Type.
Variable B : forall a: A, Type.
Variables gfa gfb gfc : rel2 A B -> rel2 A B -> rel2 A B -> rel2 A B.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco2''a ra rb rc a b : Prop :=
| paco2''a_pfold pcoa pcob pcoc
    (LEa : pcoa <2= (paco2''a ra rb rc \2/ ra))
    (LEb : pcob <2= (paco2''b ra rb rc \2/ rb))
    (LEc : pcoc <2= (paco2''c ra rb rc \2/ rc))
    (SIM: gfa pcoa pcob pcoc a b )
with paco2''b ra rb rc a b : Prop :=
| paco2''b_pfold pcoa pcob pcoc
    (LEa : pcoa <2= (paco2''a ra rb rc \2/ ra))
    (LEb : pcob <2= (paco2''b ra rb rc \2/ rb))
    (LEc : pcoc <2= (paco2''c ra rb rc \2/ rc))
    (SIM: gfb pcoa pcob pcoc a b)
with paco2''c ra rb rc a b : Prop :=
| paco2''c_pfold pcoa pcob pcoc
    (LEa : pcoa <2= (paco2''a ra rb rc \2/ ra))
    (LEb : pcob <2= (paco2''b ra rb rc \2/ rb))
    (LEc : pcoc <2= (paco2''c ra rb rc \2/ rc))
    (SIM: gfc pcoa pcob pcoc a b)
.
Implicit Arguments paco2''a [].
Implicit Arguments paco2''b [].
Implicit Arguments paco2''c [].

Theorem paco2''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <2= rr) (CIH: l <2= rr), l <2= paco2''a rr rb rc),
  l <2= paco2''a ra rb rc.
Proof.
  intros; assert (SIM: paco2''a (ra \2/ l) rb rc a b) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <2= rr) (CIH: l <2= rr), l <2= paco2''b ra rr rc),
  l <2= paco2''b ra rb rc.
Proof.
  intros; assert (SIM: paco2''b ra (rb \2/ l) rc a b) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <2= rr) (CIH: l <2= rr), l <2= paco2''c ra rb rr),
  l <2= paco2''c ra rb rc.
Proof.
  intros; assert (SIM: paco2''c ra rb (rc \2/ l) a b) by eauto.
  clear PR; repeat (try left; do 3 paco_revert; paco_cofix_auto).
Qed.

Theorem paco2''a_mon: monotone2'' paco2''a.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2''b_mon: monotone2'' paco2''b.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2''c_mon: monotone2'' paco2''c.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2''a_mult_strong: forall ra rb rc,
  paco2''a (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc)
  <2= paco2''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2''b_mult_strong: forall ra rb rc,
  paco2''b (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc)
  <2= paco2''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Theorem paco2''c_mult_strong: forall ra rb rc,
  paco2''c (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc)
  <2= paco2''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 3 paco_revert; paco_cofix_auto). Qed.

Corollary paco2''a_mult: forall ra rb rc,
  paco2''a (paco2''a ra rb rc) (paco2''b ra rb rc) (paco2''c ra rb rc)
  <2= paco2''a ra rb rc.
Proof. intros; eapply paco2''a_mult_strong, paco2''a_mon; eauto. Qed.

Corollary paco2''b_mult: forall ra rb rc,
  paco2''b (paco2''a ra rb rc) (paco2''b ra rb rc) (paco2''c ra rb rc)
  <2= paco2''b ra rb rc.
Proof. intros; eapply paco2''b_mult_strong, paco2''b_mon; eauto. Qed.

Corollary paco2''c_mult: forall ra rb rc,
  paco2''c (paco2''a ra rb rc) (paco2''b ra rb rc) (paco2''c ra rb rc)
  <2= paco2''c ra rb rc.
Proof. intros; eapply paco2''c_mult_strong, paco2''c_mon; eauto. Qed.

Theorem paco2''a_fold: forall ra rb rc,
  gfa (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc) 
  <2= paco2''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco2''b_fold: forall ra rb rc,
  gfb (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc) 
  <2= paco2''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco2''c_fold: forall ra rb rc,
  gfc (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc) 
  <2= paco2''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco2''a_unfold: forall
    (MONa: monotone2'' gfa) (MONb: monotone2'' gfb) (MONc: monotone2'' gfc) ra rb rc,
  paco2''a ra rb rc
  <2= gfa (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc).
Proof. unfold monotone2''; intros; destruct PR; eauto. Qed.

Theorem paco2''b_unfold: forall
    (MONa: monotone2'' gfa) (MONb: monotone2'' gfb) (MONc: monotone2'' gfc) ra rb rc,
  paco2''b ra rb rc
  <2= gfb (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc).
Proof. unfold monotone2''; intros; destruct PR; eauto. Qed.

Theorem paco2''c_unfold: forall
    (MONa: monotone2'' gfa) (MONb: monotone2'' gfb) (MONc: monotone2'' gfc) ra rb rc,
  paco2''c ra rb rc
  <2= gfc (paco2''a ra rb rc \2/ ra) (paco2''b ra rb rc \2/ rb) (paco2''c ra rb rc \2/ rc).
Proof. unfold monotone2''; intros; destruct PR; eauto. Qed.

End Arg2Three.

Hint Unfold monotone2''.
Hint Resolve paco2''a_fold.
Hint Resolve paco2''b_fold.
Hint Resolve paco2''c_fold.

Implicit Arguments paco2''a_mon         [A B].
Implicit Arguments paco2''b_mon         [A B].
Implicit Arguments paco2''c_mon         [A B].
Implicit Arguments paco2''a_mult_strong [A B].
Implicit Arguments paco2''b_mult_strong [A B].
Implicit Arguments paco2''c_mult_strong [A B].
Implicit Arguments paco2''a_mult        [A B].
Implicit Arguments paco2''b_mult        [A B].
Implicit Arguments paco2''c_mult        [A B].

(** ** Predicates of arity 3 
*)

(** Single Coinduction *)

Section Arg3Single.

Definition monotone3 A B C (gf: rel3 A B C -> rel3 A B C) := 
  forall a b c r r' (IN: gf r a b c) (LE: r <3= r'), gf r' a b c.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable gf : rel3 A B C -> rel3 A B C.
Implicit Arguments gf [].

CoInductive paco3 r a b c : Prop :=
| paco3_pfold pco
    (LE : pco <3= (paco3 r \3/ r))
    (SIM: gf pco a b c)
.
Implicit Arguments paco3 [].

Theorem paco3_acc: forall
    l r (OBG: forall rr (INC: r <3= rr) (CIH: l <3= rr), l <3= paco3 rr),
  l <3= paco3 r.
Proof.
  intros; assert (SIM: paco3 (r \3/ l) a b c) by eauto.
  clear PR; do 4 paco_revert; paco_cofix_auto.
Qed.

Theorem paco3_mon: monotone3 paco3.
Proof. paco_cofix_auto. Qed.

Theorem paco3_mult_strong: forall r,
  paco3 (paco3 r \3/ r) <3= paco3 r.
Proof. paco_cofix_auto. Qed.

Corollary paco3_mult: forall r,
  paco3 (paco3 r) <3= paco3 r.
Proof. intros; eapply paco3_mult_strong, paco3_mon; eauto. Qed.

Theorem paco3_fold: forall r,
  gf (paco3 r \3/ r) <3= paco3 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco3_unfold: forall (MON: monotone3 gf) r,
  paco3 r <3= gf (paco3 r \3/ r).
Proof. unfold monotone3; intros; destruct PR; eauto. Qed.

End Arg3Single.

Hint Unfold monotone3.
Hint Resolve paco3_fold.

Implicit Arguments paco3_mon            [A B C].
Implicit Arguments paco3_mult_strong    [A B C].
Implicit Arguments paco3_mult           [A B C].

(** Two Mutual Coinduction *)

Section Arg3Two.

Definition monotone3' A B C (gf: rel3 A B C -> rel3 A B C -> rel3 A B C) := 
  forall a b c ra ra' rb rb' (IN: gf ra rb a b c) (LEa: ra <3= ra') (LEb: rb <3= rb'), gf ra' rb' a b c.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variables gfa gfb : rel3 A B C -> rel3 A B C -> rel3 A B C.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco3'a ra rb a b c : Prop :=
| paco3'a_pfold pcoa pcob
    (LEa : pcoa <3= (paco3'a ra rb \3/ ra))
    (LEb : pcob <3= (paco3'b ra rb \3/ rb))
    (SIM: gfa pcoa pcob a b c)
with paco3'b ra rb a b c : Prop :=
| paco3'b_pfold pcoa pcob
    (LEa : pcoa <3= (paco3'a ra rb \3/ ra))
    (LEb : pcob <3= (paco3'b ra rb \3/ rb))
    (SIM: gfb pcoa pcob a b c)
.
Implicit Arguments paco3'a [].
Implicit Arguments paco3'b [].

Theorem paco3'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <3= rr) (CIH: l <3= rr), l <3= paco3'a rr rb),
  l <3= paco3'a ra rb.
Proof.
  intros; assert (SIM: paco3'a (ra \3/ l) rb a b c) by eauto.
  clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
Qed.

Theorem paco3'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <3= rr) (CIH: l <3= rr), l <3= paco3'b ra rr),
  l <3= paco3'b ra rb.
Proof.
  intros; assert (SIM: paco3'b ra (rb \3/ l) a b c) by eauto.
  clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
Qed.

Theorem paco3'a_mon: monotone3' paco3'a.
Proof. paco_cofix_auto; left; do 4 paco_revert; paco_cofix_auto. Qed.

Theorem paco3'b_mon: monotone3' paco3'b.
Proof. paco_cofix_auto; left; do 4 paco_revert; paco_cofix_auto. Qed.

Theorem paco3'a_mult_strong: forall ra rb,
  paco3'a (paco3'a ra rb \3/ ra) (paco3'b ra rb \3/ rb) <3= paco3'a ra rb.
Proof. paco_cofix_auto; left; do 4 paco_revert; paco_cofix_auto. Qed.

Theorem paco3'b_mult_strong: forall ra rb,
  paco3'b (paco3'a ra rb \3/ ra) (paco3'b ra rb \3/ rb) <3= paco3'b ra rb.
Proof. paco_cofix_auto; left; do 4 paco_revert; paco_cofix_auto. Qed.

Corollary paco3'a_mult: forall ra rb,
  paco3'a (paco3'a ra rb) (paco3'b ra rb) <3= paco3'a ra rb.
Proof. intros; eapply paco3'a_mult_strong, paco3'a_mon; eauto. Qed.

Corollary paco3'b_mult: forall ra rb,
  paco3'b (paco3'a ra rb) (paco3'b ra rb) <3= paco3'b ra rb.
Proof. intros; eapply paco3'b_mult_strong, paco3'b_mon; eauto. Qed.

Theorem paco3'a_fold: forall ra rb,
  gfa (paco3'a ra rb \3/ ra) (paco3'b ra rb \3/ rb) <3= paco3'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco3'b_fold: forall ra rb,
  gfb (paco3'a ra rb \3/ ra) (paco3'b ra rb \3/ rb) <3= paco3'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco3'a_unfold: forall
    (MONa: monotone3' gfa) (MONb: monotone3' gfb) ra rb,
  paco3'a ra rb 
  <3= gfa (paco3'a ra rb \3/ ra) (paco3'b ra rb \3/ rb).
Proof. unfold monotone3'; intros; destruct PR; eauto. Qed.

Theorem paco3'b_unfold: forall
    (MONa: monotone3' gfa) (MONb: monotone3' gfb) ra rb,
  paco3'b ra rb 
  <3= gfb (paco3'a ra rb \3/ ra) (paco3'b ra rb \3/ rb).
Proof. unfold monotone3'; intros; destruct PR; eauto. Qed.

End Arg3Two.

Hint Unfold monotone3'.
Hint Resolve paco3'a_fold.
Hint Resolve paco3'b_fold.

Implicit Arguments paco3'a_mon          [A B C].
Implicit Arguments paco3'b_mon          [A B C].
Implicit Arguments paco3'a_mult_strong  [A B C].
Implicit Arguments paco3'b_mult_strong  [A B C].
Implicit Arguments paco3'a_mult         [A B C].
Implicit Arguments paco3'b_mult         [A B C].

(** Three Mutual Coinduction *)

Section Arg3Three.

Definition monotone3'' A B C (gf: rel3 A B C -> rel3 A B C -> rel3 A B C -> rel3 A B C) := 
  forall a b c ra ra' rb rb' rc rc' (IN: gf ra rb rc a b c) (LEa: ra <3= ra') (LEb: rb <3= rb') (LEc: rc <3= rc'), gf ra' rb' rc' a b c.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variables gfa gfb gfc : rel3 A B C -> rel3 A B C -> rel3 A B C -> rel3 A B C.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco3''a ra rb rc a b c: Prop :=
| paco3''a_pfold pcoa pcob pcoc
    (LEa : pcoa <3= (paco3''a ra rb rc \3/ ra))
    (LEb : pcob <3= (paco3''b ra rb rc \3/ rb))
    (LEc : pcoc <3= (paco3''c ra rb rc \3/ rc))
    (SIM: gfa pcoa pcob pcoc a b c)
with paco3''b ra rb rc a b c: Prop :=
| paco3''b_pfold pcoa pcob pcoc
    (LEa : pcoa <3= (paco3''a ra rb rc \3/ ra))
    (LEb : pcob <3= (paco3''b ra rb rc \3/ rb))
    (LEc : pcoc <3= (paco3''c ra rb rc \3/ rc))
    (SIM: gfb pcoa pcob pcoc a b c)
with paco3''c ra rb rc a b c: Prop :=
| paco3''c_pfold pcoa pcob pcoc
    (LEa : pcoa <3= (paco3''a ra rb rc \3/ ra))
    (LEb : pcob <3= (paco3''b ra rb rc \3/ rb))
    (LEc : pcoc <3= (paco3''c ra rb rc \3/ rc))
    (SIM: gfc pcoa pcob pcoc a b c)
.
Implicit Arguments paco3''a [].
Implicit Arguments paco3''b [].
Implicit Arguments paco3''c [].

Theorem paco3''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <3= rr) (CIH: l <3= rr), l <3= paco3''a rr rb rc),
  l <3= paco3''a ra rb rc.
Proof.
  intros; assert (SIM: paco3''a (ra \3/ l) rb rc a b c) by eauto.
  clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
Qed.

Theorem paco3''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <3= rr) (CIH: l <3= rr), l <3= paco3''b ra rr rc),
  l <3= paco3''b ra rb rc.
Proof.
  intros; assert (SIM: paco3''b ra (rb \3/ l) rc a b c) by eauto.
  clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
Qed.

Theorem paco3''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <3= rr) (CIH: l <3= rr), l <3= paco3''c ra rb rr),
  l <3= paco3''c ra rb rc.
Proof.
  intros; assert (SIM: paco3''c ra rb (rc \3/ l) a b c) by eauto.
  clear PR; repeat (try left; do 4 paco_revert; paco_cofix_auto).
Qed.

Theorem paco3''a_mon: monotone3'' paco3''a.
Proof. paco_cofix_auto; repeat (left; do 4 paco_revert; paco_cofix_auto). Qed.

Theorem paco3''b_mon: monotone3'' paco3''b.
Proof. paco_cofix_auto; repeat (left; do 4 paco_revert; paco_cofix_auto). Qed.

Theorem paco3''c_mon: monotone3'' paco3''c.
Proof. paco_cofix_auto; repeat (left; do 4 paco_revert; paco_cofix_auto). Qed.

Theorem paco3''a_mult_strong: forall ra rb rc,
  paco3''a (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc)
  <3= paco3''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 4 paco_revert; paco_cofix_auto). Qed.

Theorem paco3''b_mult_strong: forall ra rb rc,
  paco3''b (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc)
  <3= paco3''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 4 paco_revert; paco_cofix_auto). Qed.

Theorem paco3''c_mult_strong: forall ra rb rc,
  paco3''c (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc)
  <3= paco3''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 4 paco_revert; paco_cofix_auto). Qed.

Corollary paco3''a_mult: forall ra rb rc,
  paco3''a (paco3''a ra rb rc) (paco3''b ra rb rc) (paco3''c ra rb rc)
  <3= paco3''a ra rb rc.
Proof. intros; eapply paco3''a_mult_strong, paco3''a_mon; eauto. Qed.

Corollary paco3''b_mult: forall ra rb rc,
  paco3''b (paco3''a ra rb rc) (paco3''b ra rb rc) (paco3''c ra rb rc)
  <3= paco3''b ra rb rc.
Proof. intros; eapply paco3''b_mult_strong, paco3''b_mon; eauto. Qed.

Corollary paco3''c_mult: forall ra rb rc,
  paco3''c (paco3''a ra rb rc) (paco3''b ra rb rc) (paco3''c ra rb rc)
  <3= paco3''c ra rb rc.
Proof. intros; eapply paco3''c_mult_strong, paco3''c_mon; eauto. Qed.

Theorem paco3''a_fold: forall ra rb rc,
  gfa (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc) 
  <3= paco3''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco3''b_fold: forall ra rb rc,
  gfb (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc) 
  <3= paco3''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco3''c_fold: forall ra rb rc,
  gfc (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc) 
  <3= paco3''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco3''a_unfold: forall
    (MONa: monotone3'' gfa) (MONb: monotone3'' gfb) (MONc: monotone3'' gfc) ra rb rc,
  paco3''a ra rb rc
  <3= gfa (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc).
Proof. unfold monotone3''; intros; destruct PR; eauto. Qed.

Theorem paco3''b_unfold: forall
    (MONa: monotone3'' gfa) (MONb: monotone3'' gfb) (MONc: monotone3'' gfc) ra rb rc,
  paco3''b ra rb rc
  <3= gfb (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc).
Proof. unfold monotone3''; intros; destruct PR; eauto. Qed.

Theorem paco3''c_unfold: forall
    (MONa: monotone3'' gfa) (MONb: monotone3'' gfb) (MONc: monotone3'' gfc) ra rb rc,
  paco3''c ra rb rc
  <3= gfc (paco3''a ra rb rc \3/ ra) (paco3''b ra rb rc \3/ rb) (paco3''c ra rb rc \3/ rc).
Proof. unfold monotone3''; intros; destruct PR; eauto. Qed.

End Arg3Three.

Hint Unfold monotone3''.
Hint Resolve paco3''a_fold.
Hint Resolve paco3''b_fold.
Hint Resolve paco3''c_fold.

Implicit Arguments paco3''a_mon         [A B C].
Implicit Arguments paco3''b_mon         [A B C].
Implicit Arguments paco3''c_mon         [A B C].
Implicit Arguments paco3''a_mult_strong [A B C].
Implicit Arguments paco3''b_mult_strong [A B C].
Implicit Arguments paco3''c_mult_strong [A B C].
Implicit Arguments paco3''a_mult        [A B C].
Implicit Arguments paco3''b_mult        [A B C].
Implicit Arguments paco3''c_mult        [A B C].

(** ** Predicates of arity 4 
*)

(** Single Coinduction *)

Section Arg4Single.

Definition monotone4 A B C D (gf: rel4 A B C D -> rel4 A B C D) := 
  forall a b c d r r' (IN: gf r a b c d) (LE: r <4= r'), gf r' a b c d.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable gf : rel4 A B C D -> rel4 A B C D.
Implicit Arguments gf [].

CoInductive paco4 r a b c d : Prop :=
| paco4_pfold pco
    (LE : pco <4= (paco4 r \4/ r))
    (SIM: gf pco a b c d)
.
Implicit Arguments paco4 [].

Theorem paco4_acc: forall
    l r (OBG: forall rr (INC: r <4= rr) (CIH: l <4= rr), l <4= paco4 rr),
  l <4= paco4 r.
Proof.
  intros; assert (SIM: paco4 (r \4/ l) a b c d) by eauto.
  clear PR; do 5 paco_revert; paco_cofix_auto.
Qed.

Theorem paco4_mon: monotone4 paco4.
Proof. paco_cofix_auto. Qed.

Theorem paco4_mult_strong: forall r,
  paco4 (paco4 r \4/ r) <4= paco4 r.
Proof. paco_cofix_auto. Qed.

Corollary paco4_mult: forall r,
  paco4 (paco4 r) <4= paco4 r.
Proof. intros; eapply paco4_mult_strong, paco4_mon; eauto. Qed.

Theorem paco4_fold: forall r,
  gf (paco4 r \4/ r) <4= paco4 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco4_unfold: forall (MON: monotone4 gf) r,
  paco4 r <4= gf (paco4 r \4/ r).
Proof. unfold monotone4; intros; destruct PR; eauto. Qed.

End Arg4Single.

Hint Unfold monotone4.
Hint Resolve paco4_fold.

Implicit Arguments paco4_mon            [A B C D].
Implicit Arguments paco4_mult_strong    [A B C D].
Implicit Arguments paco4_mult           [A B C D].

(** Two Mutual Coinduction *)

Section Arg4Two.

Definition monotone4' A B C D (gf: rel4 A B C D -> rel4 A B C D -> rel4 A B C D) := 
  forall a b c d ra ra' rb rb' (IN: gf ra rb a b c d) (LEa: ra <4= ra') (LEb: rb <4= rb'), gf ra' rb' a b c d.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variables gfa gfb : rel4 A B C D -> rel4 A B C D -> rel4 A B C D.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco4'a ra rb a b c d : Prop :=
| paco4'a_pfold pcoa pcob
    (LEa : pcoa <4= (paco4'a ra rb \4/ ra))
    (LEb : pcob <4= (paco4'b ra rb \4/ rb))
    (SIM: gfa pcoa pcob a b c d)
with paco4'b ra rb a b c d : Prop :=
| paco4'b_pfold pcoa pcob
    (LEa : pcoa <4= (paco4'a ra rb \4/ ra))
    (LEb : pcob <4= (paco4'b ra rb \4/ rb))
    (SIM: gfb pcoa pcob a b c d)
.
Implicit Arguments paco4'a [].
Implicit Arguments paco4'b [].

Theorem paco4'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <4= rr) (CIH: l <4= rr), l <4= paco4'a rr rb),
  l <4= paco4'a ra rb.
Proof.
  intros; assert (SIM: paco4'a (ra \4/ l) rb a b c d) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <4= rr) (CIH: l <4= rr), l <4= paco4'b ra rr),
  l <4= paco4'b ra rb.
Proof.
  intros; assert (SIM: paco4'b ra (rb \4/ l) a b c d) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4'a_mon: monotone4' paco4'a.
Proof. paco_cofix_auto; left; do 5 paco_revert; paco_cofix_auto. Qed.

Theorem paco4'b_mon: monotone4' paco4'b.
Proof. paco_cofix_auto; left; do 5 paco_revert; paco_cofix_auto. Qed.

Theorem paco4'a_mult_strong: forall ra rb,
  paco4'a (paco4'a ra rb \4/ ra) (paco4'b ra rb \4/ rb) <4= paco4'a ra rb.
Proof. paco_cofix_auto; left; do 5 paco_revert; paco_cofix_auto. Qed.

Theorem paco4'b_mult_strong: forall ra rb,
  paco4'b (paco4'a ra rb \4/ ra) (paco4'b ra rb \4/ rb) <4= paco4'b ra rb.
Proof. paco_cofix_auto; left; do 5 paco_revert; paco_cofix_auto. Qed.

Corollary paco4'a_mult: forall ra rb,
  paco4'a (paco4'a ra rb) (paco4'b ra rb) <4= paco4'a ra rb.
Proof. intros; eapply paco4'a_mult_strong, paco4'a_mon; eauto. Qed.

Corollary paco4'b_mult: forall ra rb,
  paco4'b (paco4'a ra rb) (paco4'b ra rb) <4= paco4'b ra rb.
Proof. intros; eapply paco4'b_mult_strong, paco4'b_mon; eauto. Qed.

Theorem paco4'a_fold: forall ra rb,
  gfa (paco4'a ra rb \4/ ra) (paco4'b ra rb \4/ rb) <4= paco4'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco4'b_fold: forall ra rb,
  gfb (paco4'a ra rb \4/ ra) (paco4'b ra rb \4/ rb) <4= paco4'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco4'a_unfold: forall
    (MONa: monotone4' gfa) (MONb: monotone4' gfb) ra rb,
  paco4'a ra rb 
  <4= gfa (paco4'a ra rb \4/ ra) (paco4'b ra rb \4/ rb).
Proof. unfold monotone4'; intros; destruct PR; eauto. Qed.

Theorem paco4'b_unfold: forall
    (MONa: monotone4' gfa) (MONb: monotone4' gfb) ra rb,
  paco4'b ra rb 
  <4= gfb (paco4'a ra rb \4/ ra) (paco4'b ra rb \4/ rb).
Proof. unfold monotone4'; intros; destruct PR; eauto. Qed.

End Arg4Two.

Hint Unfold monotone4'.
Hint Resolve paco4'a_fold.
Hint Resolve paco4'b_fold.

Implicit Arguments paco4'a_mon          [A B C D].
Implicit Arguments paco4'b_mon          [A B C D].
Implicit Arguments paco4'a_mult_strong  [A B C D].
Implicit Arguments paco4'b_mult_strong  [A B C D].
Implicit Arguments paco4'a_mult         [A B C D].
Implicit Arguments paco4'b_mult         [A B C D].

(** Three Mutual Coinduction *)

Section Arg4Three.

Definition monotone4'' A B C D (gf: rel4 A B C D -> rel4 A B C D -> rel4 A B C D -> rel4 A B C D) := 
  forall a b c d ra ra' rb rb' rc rc' (IN: gf ra rb rc a b c d) (LEa: ra <4= ra') (LEb: rb <4= rb') (LEc: rc <4= rc'), gf ra' rb' rc' a b c d.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variables gfa gfb gfc : rel4 A B C D -> rel4 A B C D -> rel4 A B C D -> rel4 A B C D.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco4''a ra rb rc a b c d : Prop :=
| paco4''a_pfold pcoa pcob pcoc
    (LEa : pcoa <4= (paco4''a ra rb rc \4/ ra))
    (LEb : pcob <4= (paco4''b ra rb rc \4/ rb))
    (LEc : pcoc <4= (paco4''c ra rb rc \4/ rc))
    (SIM: gfa pcoa pcob pcoc a b c d)
with paco4''b ra rb rc a b c d : Prop :=
| paco4''b_pfold pcoa pcob pcoc
    (LEa : pcoa <4= (paco4''a ra rb rc \4/ ra))
    (LEb : pcob <4= (paco4''b ra rb rc \4/ rb))
    (LEc : pcoc <4= (paco4''c ra rb rc \4/ rc))
    (SIM: gfb pcoa pcob pcoc a b c d)
with paco4''c ra rb rc a b c d : Prop :=
| paco4''c_pfold pcoa pcob pcoc
    (LEa : pcoa <4= (paco4''a ra rb rc \4/ ra))
    (LEb : pcob <4= (paco4''b ra rb rc \4/ rb))
    (LEc : pcoc <4= (paco4''c ra rb rc \4/ rc))
    (SIM: gfc pcoa pcob pcoc a b c d)
.
Implicit Arguments paco4''a [].
Implicit Arguments paco4''b [].
Implicit Arguments paco4''c [].

Theorem paco4''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <4= rr) (CIH: l <4= rr), l <4= paco4''a rr rb rc),
  l <4= paco4''a ra rb rc.
Proof.
  intros; assert (SIM: paco4''a (ra \4/ l) rb rc a b c d) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <4= rr) (CIH: l <4= rr), l <4= paco4''b ra rr rc),
  l <4= paco4''b ra rb rc.
Proof.
  intros; assert (SIM: paco4''b ra (rb \4/ l) rc a b c d) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <4= rr) (CIH: l <4= rr), l <4= paco4''c ra rb rr),
  l <4= paco4''c ra rb rc.
Proof.
  intros; assert (SIM: paco4''c ra rb (rc \4/ l) a b c d) by eauto.
  clear PR; repeat (try left; do 5 paco_revert; paco_cofix_auto).
Qed.

Theorem paco4''a_mon: monotone4'' paco4''a.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4''b_mon: monotone4'' paco4''b.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4''c_mon: monotone4'' paco4''c.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4''a_mult_strong: forall ra rb rc,
  paco4''a (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc)
  <4= paco4''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4''b_mult_strong: forall ra rb rc,
  paco4''b (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc)
  <4= paco4''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Theorem paco4''c_mult_strong: forall ra rb rc,
  paco4''c (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc)
  <4= paco4''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 5 paco_revert; paco_cofix_auto). Qed.

Corollary paco4''a_mult: forall ra rb rc,
  paco4''a (paco4''a ra rb rc) (paco4''b ra rb rc) (paco4''c ra rb rc)
  <4= paco4''a ra rb rc.
Proof. intros; eapply paco4''a_mult_strong, paco4''a_mon; eauto. Qed.

Corollary paco4''b_mult: forall ra rb rc,
  paco4''b (paco4''a ra rb rc) (paco4''b ra rb rc) (paco4''c ra rb rc)
  <4= paco4''b ra rb rc.
Proof. intros; eapply paco4''b_mult_strong, paco4''b_mon; eauto. Qed.

Corollary paco4''c_mult: forall ra rb rc,
  paco4''c (paco4''a ra rb rc) (paco4''b ra rb rc) (paco4''c ra rb rc)
  <4= paco4''c ra rb rc.
Proof. intros; eapply paco4''c_mult_strong, paco4''c_mon; eauto. Qed.

Theorem paco4''a_fold: forall ra rb rc,
  gfa (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc) 
  <4= paco4''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco4''b_fold: forall ra rb rc,
  gfb (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc) 
  <4= paco4''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco4''c_fold: forall ra rb rc,
  gfc (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc) 
  <4= paco4''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco4''a_unfold: forall
    (MONa: monotone4'' gfa) (MONb: monotone4'' gfb) (MONc: monotone4'' gfc) ra rb rc,
  paco4''a ra rb rc
  <4= gfa (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc).
Proof. unfold monotone4''; intros; destruct PR; eauto. Qed.

Theorem paco4''b_unfold: forall
    (MONa: monotone4'' gfa) (MONb: monotone4'' gfb) (MONc: monotone4'' gfc) ra rb rc,
  paco4''b ra rb rc
  <4= gfb (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc).
Proof. unfold monotone4''; intros; destruct PR; eauto. Qed.

Theorem paco4''c_unfold: forall
    (MONa: monotone4'' gfa) (MONb: monotone4'' gfb) (MONc: monotone4'' gfc) ra rb rc,
  paco4''c ra rb rc
  <4= gfc (paco4''a ra rb rc \4/ ra) (paco4''b ra rb rc \4/ rb) (paco4''c ra rb rc \4/ rc).
Proof. unfold monotone4''; intros; destruct PR; eauto. Qed.

End Arg4Three.

Hint Unfold monotone4''.
Hint Resolve paco4''a_fold.
Hint Resolve paco4''b_fold.
Hint Resolve paco4''c_fold.

Implicit Arguments paco4''a_mon         [A B C D].
Implicit Arguments paco4''b_mon         [A B C D].
Implicit Arguments paco4''c_mon         [A B C D].
Implicit Arguments paco4''a_mult_strong [A B C D].
Implicit Arguments paco4''b_mult_strong [A B C D].
Implicit Arguments paco4''c_mult_strong [A B C D].
Implicit Arguments paco4''a_mult        [A B C D].
Implicit Arguments paco4''b_mult        [A B C D].
Implicit Arguments paco4''c_mult        [A B C D].

(** ** Predicates of arity 5 
*)

(** Single Coinduction *)

Section Arg5Single.

Definition monotone5 A B C D E (gf: rel5 A B C D E -> rel5 A B C D E) := 
  forall a b c d e r r' (IN: gf r a b c d e) (LE: r <5= r'), gf r' a b c d e.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable gf : rel5 A B C D E -> rel5 A B C D E.
Implicit Arguments gf [].

CoInductive paco5 r a b c d e : Prop :=
| paco5_pfold pco
    (LE : pco <5= (paco5 r \5/ r))
    (SIM: gf pco a b c d e)
.
Implicit Arguments paco5 [].

Theorem paco5_acc: forall
    l r (OBG: forall rr (INC: r <5= rr) (CIH: l <5= rr), l <5= paco5 rr),
  l <5= paco5 r.
Proof.
  intros; assert (SIM: paco5 (r \5/ l) a b c d e) by eauto.
  clear PR; do 6 paco_revert; paco_cofix_auto.
Qed.

Theorem paco5_mon: monotone5 paco5.
Proof. paco_cofix_auto. Qed.

Theorem paco5_mult_strong: forall r,
  paco5 (paco5 r \5/ r) <5= paco5 r.
Proof. paco_cofix_auto. Qed.

Corollary paco5_mult: forall r,
  paco5 (paco5 r) <5= paco5 r.
Proof. intros; eapply paco5_mult_strong, paco5_mon; eauto. Qed.

Theorem paco5_fold: forall r,
  gf (paco5 r \5/ r) <5= paco5 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco5_unfold: forall (MON: monotone5 gf) r,
  paco5 r <5= gf (paco5 r \5/ r).
Proof. unfold monotone5; intros; destruct PR; eauto. Qed.

End Arg5Single.

Hint Unfold monotone5.
Hint Resolve paco5_fold.

Implicit Arguments paco5_mon            [A B C D E].
Implicit Arguments paco5_mult_strong    [A B C D E].
Implicit Arguments paco5_mult           [A B C D E].

(** Two Mutual Coinduction *)

Section Arg5Two.

Definition monotone5' A B C D E (gf: rel5 A B C D E -> rel5 A B C D E -> rel5 A B C D E) := 
  forall a b c d e ra ra' rb rb' (IN: gf ra rb a b c d e) (LEa: ra <5= ra') (LEb: rb <5= rb'), gf ra' rb' a b c d e.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variables gfa gfb : rel5 A B C D E -> rel5 A B C D E -> rel5 A B C D E.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco5'a ra rb a b c d e : Prop :=
| paco5'a_pfold pcoa pcob
    (LEa : pcoa <5= (paco5'a ra rb \5/ ra))
    (LEb : pcob <5= (paco5'b ra rb \5/ rb))
    (SIM: gfa pcoa pcob a b c d e)
with paco5'b ra rb a b c d e : Prop :=
| paco5'b_pfold pcoa pcob
    (LEa : pcoa <5= (paco5'a ra rb \5/ ra))
    (LEb : pcob <5= (paco5'b ra rb \5/ rb))
    (SIM: gfb pcoa pcob a b c d e)
.
Implicit Arguments paco5'a [].
Implicit Arguments paco5'b [].

Theorem paco5'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <5= rr) (CIH: l <5= rr), l <5= paco5'a rr rb),
  l <5= paco5'a ra rb.
Proof.
  intros; assert (SIM: paco5'a (ra \5/ l) rb a b c d e) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <5= rr) (CIH: l <5= rr), l <5= paco5'b ra rr),
  l <5= paco5'b ra rb.
Proof.
  intros; assert (SIM: paco5'b ra (rb \5/ l) a b c d e) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5'a_mon: monotone5' paco5'a.
Proof. paco_cofix_auto; left; do 6 paco_revert; paco_cofix_auto. Qed.

Theorem paco5'b_mon: monotone5' paco5'b.
Proof. paco_cofix_auto; left; do 6 paco_revert; paco_cofix_auto. Qed.

Theorem paco5'a_mult_strong: forall ra rb,
  paco5'a (paco5'a ra rb \5/ ra) (paco5'b ra rb \5/ rb) <5= paco5'a ra rb.
Proof. paco_cofix_auto; left; do 6 paco_revert; paco_cofix_auto. Qed.

Theorem paco5'b_mult_strong: forall ra rb,
  paco5'b (paco5'a ra rb \5/ ra) (paco5'b ra rb \5/ rb) <5= paco5'b ra rb.
Proof. paco_cofix_auto; left; do 6 paco_revert; paco_cofix_auto. Qed.

Corollary paco5'a_mult: forall ra rb,
  paco5'a (paco5'a ra rb) (paco5'b ra rb) <5= paco5'a ra rb.
Proof. intros; eapply paco5'a_mult_strong, paco5'a_mon; eauto. Qed.

Corollary paco5'b_mult: forall ra rb,
  paco5'b (paco5'a ra rb) (paco5'b ra rb) <5= paco5'b ra rb.
Proof. intros; eapply paco5'b_mult_strong, paco5'b_mon; eauto. Qed.

Theorem paco5'a_fold: forall ra rb,
  gfa (paco5'a ra rb \5/ ra) (paco5'b ra rb \5/ rb) <5= paco5'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco5'b_fold: forall ra rb,
  gfb (paco5'a ra rb \5/ ra) (paco5'b ra rb \5/ rb) <5= paco5'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco5'a_unfold: forall
    (MONa: monotone5' gfa) (MONb: monotone5' gfb) ra rb,
  paco5'a ra rb 
  <5= gfa (paco5'a ra rb \5/ ra) (paco5'b ra rb \5/ rb).
Proof. unfold monotone5'; intros; destruct PR; eauto. Qed.

Theorem paco5'b_unfold: forall
    (MONa: monotone5' gfa) (MONb: monotone5' gfb) ra rb,
  paco5'b ra rb 
  <5= gfb (paco5'a ra rb \5/ ra) (paco5'b ra rb \5/ rb).
Proof. unfold monotone5'; intros; destruct PR; eauto. Qed.

End Arg5Two.

Hint Unfold monotone5'.
Hint Resolve paco5'a_fold.
Hint Resolve paco5'b_fold.

Implicit Arguments paco5'a_mon          [A B C D E].
Implicit Arguments paco5'b_mon          [A B C D E].
Implicit Arguments paco5'a_mult_strong  [A B C D E].
Implicit Arguments paco5'b_mult_strong  [A B C D E].
Implicit Arguments paco5'a_mult         [A B C D E].
Implicit Arguments paco5'b_mult         [A B C D E].

(** Three Mutual Coinduction *)

Section Arg5Three.

Definition monotone5'' A B C D E (gf: rel5 A B C D E -> rel5 A B C D E -> rel5 A B C D E -> rel5 A B C D E) := 
  forall a b c d e ra ra' rb rb' rc rc' (IN: gf ra rb rc a b c d e) (LEa: ra <5= ra') (LEb: rb <5= rb') (LEc: rc <5= rc'), gf ra' rb' rc' a b c d e.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variables gfa gfb gfc : rel5 A B C D E -> rel5 A B C D E -> rel5 A B C D E -> rel5 A B C D E.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco5''a ra rb rc a b c d e : Prop :=
| paco5''a_pfold pcoa pcob pcoc
    (LEa : pcoa <5= (paco5''a ra rb rc \5/ ra))
    (LEb : pcob <5= (paco5''b ra rb rc \5/ rb))
    (LEc : pcoc <5= (paco5''c ra rb rc \5/ rc))
    (SIM: gfa pcoa pcob pcoc a b c d e)
with paco5''b ra rb rc a b c d e : Prop :=
| paco5''b_pfold pcoa pcob pcoc
    (LEa : pcoa <5= (paco5''a ra rb rc \5/ ra))
    (LEb : pcob <5= (paco5''b ra rb rc \5/ rb))
    (LEc : pcoc <5= (paco5''c ra rb rc \5/ rc))
    (SIM: gfb pcoa pcob pcoc a b c d e)
with paco5''c ra rb rc a b c d e : Prop :=
| paco5''c_pfold pcoa pcob pcoc
    (LEa : pcoa <5= (paco5''a ra rb rc \5/ ra))
    (LEb : pcob <5= (paco5''b ra rb rc \5/ rb))
    (LEc : pcoc <5= (paco5''c ra rb rc \5/ rc))
    (SIM: gfc pcoa pcob pcoc a b c d e)
.
Implicit Arguments paco5''a [].
Implicit Arguments paco5''b [].
Implicit Arguments paco5''c [].

Theorem paco5''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <5= rr) (CIH: l <5= rr), l <5= paco5''a rr rb rc),
  l <5= paco5''a ra rb rc.
Proof.
  intros; assert (SIM: paco5''a (ra \5/ l) rb rc a b c d e) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <5= rr) (CIH: l <5= rr), l <5= paco5''b ra rr rc),
  l <5= paco5''b ra rb rc.
Proof.
  intros; assert (SIM: paco5''b ra (rb \5/ l) rc a b c d e) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <5= rr) (CIH: l <5= rr), l <5= paco5''c ra rb rr),
  l <5= paco5''c ra rb rc.
Proof.
  intros; assert (SIM: paco5''c ra rb (rc \5/ l) a b c d e) by eauto.
  clear PR; repeat (try left; do 6 paco_revert; paco_cofix_auto).
Qed.

Theorem paco5''a_mon: monotone5'' paco5''a.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5''b_mon: monotone5'' paco5''b.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5''c_mon: monotone5'' paco5''c.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5''a_mult_strong: forall ra rb rc,
  paco5''a (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc)
  <5= paco5''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5''b_mult_strong: forall ra rb rc,
  paco5''b (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc)
  <5= paco5''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Theorem paco5''c_mult_strong: forall ra rb rc,
  paco5''c (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc)
  <5= paco5''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 6 paco_revert; paco_cofix_auto). Qed.

Corollary paco5''a_mult: forall ra rb rc,
  paco5''a (paco5''a ra rb rc) (paco5''b ra rb rc) (paco5''c ra rb rc)
  <5= paco5''a ra rb rc.
Proof. intros; eapply paco5''a_mult_strong, paco5''a_mon; eauto. Qed.

Corollary paco5''b_mult: forall ra rb rc,
  paco5''b (paco5''a ra rb rc) (paco5''b ra rb rc) (paco5''c ra rb rc)
  <5= paco5''b ra rb rc.
Proof. intros; eapply paco5''b_mult_strong, paco5''b_mon; eauto. Qed.

Corollary paco5''c_mult: forall ra rb rc,
  paco5''c (paco5''a ra rb rc) (paco5''b ra rb rc) (paco5''c ra rb rc)
  <5= paco5''c ra rb rc.
Proof. intros; eapply paco5''c_mult_strong, paco5''c_mon; eauto. Qed.

Theorem paco5''a_fold: forall ra rb rc,
  gfa (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc) 
  <5= paco5''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco5''b_fold: forall ra rb rc,
  gfb (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc) 
  <5= paco5''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco5''c_fold: forall ra rb rc,
  gfc (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc) 
  <5= paco5''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco5''a_unfold: forall
    (MONa: monotone5'' gfa) (MONb: monotone5'' gfb) (MONc: monotone5'' gfc) ra rb rc,
  paco5''a ra rb rc
  <5= gfa (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc).
Proof. unfold monotone5''; intros; destruct PR; eauto. Qed.

Theorem paco5''b_unfold: forall
    (MONa: monotone5'' gfa) (MONb: monotone5'' gfb) (MONc: monotone5'' gfc) ra rb rc,
  paco5''b ra rb rc
  <5= gfb (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc).
Proof. unfold monotone5''; intros; destruct PR; eauto. Qed.

Theorem paco5''c_unfold: forall
    (MONa: monotone5'' gfa) (MONb: monotone5'' gfb) (MONc: monotone5'' gfc) ra rb rc,
  paco5''c ra rb rc
  <5= gfc (paco5''a ra rb rc \5/ ra) (paco5''b ra rb rc \5/ rb) (paco5''c ra rb rc \5/ rc).
Proof. unfold monotone5''; intros; destruct PR; eauto. Qed.

End Arg5Three.

Hint Unfold monotone5''.
Hint Resolve paco5''a_fold.
Hint Resolve paco5''b_fold.
Hint Resolve paco5''c_fold.

Implicit Arguments paco5''a_mon         [A B C D E].
Implicit Arguments paco5''b_mon         [A B C D E].
Implicit Arguments paco5''c_mon         [A B C D E].
Implicit Arguments paco5''a_mult_strong [A B C D E].
Implicit Arguments paco5''b_mult_strong [A B C D E].
Implicit Arguments paco5''c_mult_strong [A B C D E].
Implicit Arguments paco5''a_mult        [A B C D E].
Implicit Arguments paco5''b_mult        [A B C D E].
Implicit Arguments paco5''c_mult        [A B C D E].

(** ** Predicates of arity 6 
*)

(** Single Coinduction *)

Section Arg6Single.

Definition monotone6 A B C D E F (gf: rel6 A B C D E F -> rel6 A B C D E F) := 
  forall a b c d e f r r' (IN: gf r a b c d e f) (LE: r <6= r'), gf r' a b c d e f.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable gf : rel6 A B C D E F -> rel6 A B C D E F.
Implicit Arguments gf [].

CoInductive paco6 r a b c d e f : Prop :=
| paco6_pfold pco
    (LE : pco <6= (paco6 r \6/ r))
    (SIM: gf pco a b c d e f)
.
Implicit Arguments paco6 [].

Theorem paco6_acc: forall
    l r (OBG: forall rr (INC: r <6= rr) (CIH: l <6= rr), l <6= paco6 rr),
  l <6= paco6 r.
Proof.
  intros; assert (SIM: paco6 (r \6/ l) a b c d e f) by eauto.
  clear PR; do 7 paco_revert; paco_cofix_auto.
Qed.

Theorem paco6_mon: monotone6 paco6.
Proof. paco_cofix_auto. Qed.

Theorem paco6_mult_strong: forall r,
  paco6 (paco6 r \6/ r) <6= paco6 r.
Proof. paco_cofix_auto. Qed.

Corollary paco6_mult: forall r,
  paco6 (paco6 r) <6= paco6 r.
Proof. intros; eapply paco6_mult_strong, paco6_mon; eauto. Qed.

Theorem paco6_fold: forall r,
  gf (paco6 r \6/ r) <6= paco6 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco6_unfold: forall (MON: monotone6 gf) r,
  paco6 r <6= gf (paco6 r \6/ r).
Proof. unfold monotone6; intros; destruct PR; eauto. Qed.

End Arg6Single.

Hint Unfold monotone6.
Hint Resolve paco6_fold.

Implicit Arguments paco6_mon            [A B C D E F].
Implicit Arguments paco6_mult_strong    [A B C D E F].
Implicit Arguments paco6_mult           [A B C D E F].

(** Two Mutual Coinduction *)

Section Arg6Two.

Definition monotone6' A B C D E F (gf: rel6 A B C D E F -> rel6 A B C D E F -> rel6 A B C D E F) := 
  forall a b c d e f ra ra' rb rb' (IN: gf ra rb a b c d e f) (LEa: ra <6= ra') (LEb: rb <6= rb'), gf ra' rb' a b c d e f.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variables gfa gfb : rel6 A B C D E F -> rel6 A B C D E F -> rel6 A B C D E F.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco6'a ra rb a b c d e f : Prop :=
| paco6'a_pfold pcoa pcob
    (LEa : pcoa <6= (paco6'a ra rb \6/ ra))
    (LEb : pcob <6= (paco6'b ra rb \6/ rb))
    (SIM: gfa pcoa pcob a b c d e f)
with paco6'b ra rb a b c d e f : Prop :=
| paco6'b_pfold pcoa pcob
    (LEa : pcoa <6= (paco6'a ra rb \6/ ra))
    (LEb : pcob <6= (paco6'b ra rb \6/ rb))
    (SIM: gfb pcoa pcob a b c d e f)
.
Implicit Arguments paco6'a [].
Implicit Arguments paco6'b [].

Theorem paco6'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <6= rr) (CIH: l <6= rr), l <6= paco6'a rr rb),
  l <6= paco6'a ra rb.
Proof.
  intros; assert (SIM: paco6'a (ra \6/ l) rb a b c d e f) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <6= rr) (CIH: l <6= rr), l <6= paco6'b ra rr),
  l <6= paco6'b ra rb.
Proof.
  intros; assert (SIM: paco6'b ra (rb \6/ l) a b c d e f) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6'a_mon: monotone6' paco6'a.
Proof. paco_cofix_auto; left; do 7 paco_revert; paco_cofix_auto. Qed.

Theorem paco6'b_mon: monotone6' paco6'b.
Proof. paco_cofix_auto; left; do 7 paco_revert; paco_cofix_auto. Qed.

Theorem paco6'a_mult_strong: forall ra rb,
  paco6'a (paco6'a ra rb \6/ ra) (paco6'b ra rb \6/ rb) <6= paco6'a ra rb.
Proof. paco_cofix_auto; left; do 7 paco_revert; paco_cofix_auto. Qed.

Theorem paco6'b_mult_strong: forall ra rb,
  paco6'b (paco6'a ra rb \6/ ra) (paco6'b ra rb \6/ rb) <6= paco6'b ra rb.
Proof. paco_cofix_auto; left; do 7 paco_revert; paco_cofix_auto. Qed.

Corollary paco6'a_mult: forall ra rb,
  paco6'a (paco6'a ra rb) (paco6'b ra rb) <6= paco6'a ra rb.
Proof. intros; eapply paco6'a_mult_strong, paco6'a_mon; eauto. Qed.

Corollary paco6'b_mult: forall ra rb,
  paco6'b (paco6'a ra rb) (paco6'b ra rb) <6= paco6'b ra rb.
Proof. intros; eapply paco6'b_mult_strong, paco6'b_mon; eauto. Qed.

Theorem paco6'a_fold: forall ra rb,
  gfa (paco6'a ra rb \6/ ra) (paco6'b ra rb \6/ rb) <6= paco6'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco6'b_fold: forall ra rb,
  gfb (paco6'a ra rb \6/ ra) (paco6'b ra rb \6/ rb) <6= paco6'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco6'a_unfold: forall
    (MONa: monotone6' gfa) (MONb: monotone6' gfb) ra rb,
  paco6'a ra rb 
  <6= gfa (paco6'a ra rb \6/ ra) (paco6'b ra rb \6/ rb).
Proof. unfold monotone6'; intros; destruct PR; eauto. Qed.

Theorem paco6'b_unfold: forall
    (MONa: monotone6' gfa) (MONb: monotone6' gfb) ra rb,
  paco6'b ra rb 
  <6= gfb (paco6'a ra rb \6/ ra) (paco6'b ra rb \6/ rb).
Proof. unfold monotone6'; intros; destruct PR; eauto. Qed.

End Arg6Two.

Hint Unfold monotone6'.
Hint Resolve paco6'a_fold.
Hint Resolve paco6'b_fold.

Implicit Arguments paco6'a_mon          [A B C D E F].
Implicit Arguments paco6'b_mon          [A B C D E F].
Implicit Arguments paco6'a_mult_strong  [A B C D E F].
Implicit Arguments paco6'b_mult_strong  [A B C D E F].
Implicit Arguments paco6'a_mult         [A B C D E F].
Implicit Arguments paco6'b_mult         [A B C D E F].

(** Three Mutual Coinduction *)

Section Arg6Three.

Definition monotone6'' A B C D E F (gf: rel6 A B C D E F -> rel6 A B C D E F -> rel6 A B C D E F -> rel6 A B C D E F) := 
  forall a b c d e f ra ra' rb rb' rc rc' (IN: gf ra rb rc a b c d e f) (LEa: ra <6= ra') (LEb: rb <6= rb') (LEc: rc <6= rc'), gf ra' rb' rc' a b c d e f.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variables gfa gfb gfc : rel6 A B C D E F -> rel6 A B C D E F -> rel6 A B C D E F -> rel6 A B C D E F.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco6''a ra rb rc a b c d e f : Prop :=
| paco6''a_pfold pcoa pcob pcoc
    (LEa : pcoa <6= (paco6''a ra rb rc \6/ ra))
    (LEb : pcob <6= (paco6''b ra rb rc \6/ rb))
    (LEc : pcoc <6= (paco6''c ra rb rc \6/ rc))
    (SIM: gfa pcoa pcob pcoc a b c d e f)
with paco6''b ra rb rc a b c d e f : Prop :=
| paco6''b_pfold pcoa pcob pcoc
    (LEa : pcoa <6= (paco6''a ra rb rc \6/ ra))
    (LEb : pcob <6= (paco6''b ra rb rc \6/ rb))
    (LEc : pcoc <6= (paco6''c ra rb rc \6/ rc))
    (SIM: gfb pcoa pcob pcoc a b c d e f)
with paco6''c ra rb rc a b c d e f : Prop :=
| paco6''c_pfold pcoa pcob pcoc
    (LEa : pcoa <6= (paco6''a ra rb rc \6/ ra))
    (LEb : pcob <6= (paco6''b ra rb rc \6/ rb))
    (LEc : pcoc <6= (paco6''c ra rb rc \6/ rc))
    (SIM: gfc pcoa pcob pcoc a b c d e f)
.
Implicit Arguments paco6''a [].
Implicit Arguments paco6''b [].
Implicit Arguments paco6''c [].

Theorem paco6''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <6= rr) (CIH: l <6= rr), l <6= paco6''a rr rb rc),
  l <6= paco6''a ra rb rc.
Proof.
  intros; assert (SIM: paco6''a (ra \6/ l) rb rc a b c d e f) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <6= rr) (CIH: l <6= rr), l <6= paco6''b ra rr rc),
  l <6= paco6''b ra rb rc.
Proof.
  intros; assert (SIM: paco6''b ra (rb \6/ l) rc a b c d e f) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <6= rr) (CIH: l <6= rr), l <6= paco6''c ra rb rr),
  l <6= paco6''c ra rb rc.
Proof.
  intros; assert (SIM: paco6''c ra rb (rc \6/ l) a b c d e f) by eauto.
  clear PR; repeat (try left; do 7 paco_revert; paco_cofix_auto).
Qed.

Theorem paco6''a_mon: monotone6'' paco6''a.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6''b_mon: monotone6'' paco6''b.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6''c_mon: monotone6'' paco6''c.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6''a_mult_strong: forall ra rb rc,
  paco6''a (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc)
  <6= paco6''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6''b_mult_strong: forall ra rb rc,
  paco6''b (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc)
  <6= paco6''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Theorem paco6''c_mult_strong: forall ra rb rc,
  paco6''c (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc)
  <6= paco6''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 7 paco_revert; paco_cofix_auto). Qed.

Corollary paco6''a_mult: forall ra rb rc,
  paco6''a (paco6''a ra rb rc) (paco6''b ra rb rc) (paco6''c ra rb rc)
  <6= paco6''a ra rb rc.
Proof. intros; eapply paco6''a_mult_strong, paco6''a_mon; eauto. Qed.

Corollary paco6''b_mult: forall ra rb rc,
  paco6''b (paco6''a ra rb rc) (paco6''b ra rb rc) (paco6''c ra rb rc)
  <6= paco6''b ra rb rc.
Proof. intros; eapply paco6''b_mult_strong, paco6''b_mon; eauto. Qed.

Corollary paco6''c_mult: forall ra rb rc,
  paco6''c (paco6''a ra rb rc) (paco6''b ra rb rc) (paco6''c ra rb rc)
  <6= paco6''c ra rb rc.
Proof. intros; eapply paco6''c_mult_strong, paco6''c_mon; eauto. Qed.

Theorem paco6''a_fold: forall ra rb rc,
  gfa (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc) 
  <6= paco6''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco6''b_fold: forall ra rb rc,
  gfb (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc) 
  <6= paco6''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco6''c_fold: forall ra rb rc,
  gfc (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc) 
  <6= paco6''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco6''a_unfold: forall
    (MONa: monotone6'' gfa) (MONb: monotone6'' gfb) (MONc: monotone6'' gfc) ra rb rc,
  paco6''a ra rb rc
  <6= gfa (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc).
Proof. unfold monotone6''; intros; destruct PR; eauto. Qed.

Theorem paco6''b_unfold: forall
    (MONa: monotone6'' gfa) (MONb: monotone6'' gfb) (MONc: monotone6'' gfc) ra rb rc,
  paco6''b ra rb rc
  <6= gfb (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc).
Proof. unfold monotone6''; intros; destruct PR; eauto. Qed.

Theorem paco6''c_unfold: forall
    (MONa: monotone6'' gfa) (MONb: monotone6'' gfb) (MONc: monotone6'' gfc) ra rb rc,
  paco6''c ra rb rc
  <6= gfc (paco6''a ra rb rc \6/ ra) (paco6''b ra rb rc \6/ rb) (paco6''c ra rb rc \6/ rc).
Proof. unfold monotone6''; intros; destruct PR; eauto. Qed.

End Arg6Three.

Hint Unfold monotone6''.
Hint Resolve paco6''a_fold.
Hint Resolve paco6''b_fold.
Hint Resolve paco6''c_fold.

Implicit Arguments paco6''a_mon         [A B C D E F].
Implicit Arguments paco6''b_mon         [A B C D E F].
Implicit Arguments paco6''c_mon         [A B C D E F].
Implicit Arguments paco6''a_mult_strong [A B C D E F].
Implicit Arguments paco6''b_mult_strong [A B C D E F].
Implicit Arguments paco6''c_mult_strong [A B C D E F].
Implicit Arguments paco6''a_mult        [A B C D E F].
Implicit Arguments paco6''b_mult        [A B C D E F].
Implicit Arguments paco6''c_mult        [A B C D E F].

(** ** Predicates of arity 7 
*)

(** Single Coinduction *)

Section Arg7Single.

Definition monotone7 A B C D E F G (gf: rel7 A B C D E F G -> rel7 A B C D E F G) := 
  forall a b c d e f g r r' (IN: gf r a b c d e f g) (LE: r <7= r'), gf r' a b c d e f g.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable G : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e), Type.
Variable gf : rel7 A B C D E F G -> rel7 A B C D E F G.
Implicit Arguments gf [].

CoInductive paco7 r a b c d e f g : Prop :=
| paco7_pfold pco
    (LE : pco <7= (paco7 r \7/ r))
    (SIM: gf pco a b c d e f g)
.
Implicit Arguments paco7 [].

Theorem paco7_acc: forall
    l r (OBG: forall rr (INC: r <7= rr) (CIH: l <7= rr), l <7= paco7 rr),
  l <7= paco7 r.
Proof.
  intros; assert (SIM: paco7 (r \7/ l) a b c d e f g) by eauto.
  clear PR; do 8 paco_revert; paco_cofix_auto.
Qed.

Theorem paco7_mon: monotone7 paco7.
Proof. paco_cofix_auto. Qed.

Theorem paco7_mult_strong: forall r,
  paco7 (paco7 r \7/ r) <7= paco7 r.
Proof. paco_cofix_auto. Qed.

Corollary paco7_mult: forall r,
  paco7 (paco7 r) <7= paco7 r.
Proof. intros; eapply paco7_mult_strong, paco7_mon; eauto. Qed.

Theorem paco7_fold: forall r,
  gf (paco7 r \7/ r) <7= paco7 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco7_unfold: forall (MON: monotone7 gf) r,
  paco7 r <7= gf (paco7 r \7/ r).
Proof. unfold monotone7; intros; destruct PR; eauto. Qed.

End Arg7Single.

Hint Unfold monotone7.
Hint Resolve paco7_fold.

Implicit Arguments paco7_mon            [A B C D E F G].
Implicit Arguments paco7_mult_strong    [A B C D E F G].
Implicit Arguments paco7_mult           [A B C D E F G].

(** Two Mutual Coinduction *)

Section Arg7Two.

Definition monotone7' A B C D E F G (gf: rel7 A B C D E F G -> rel7 A B C D E F G -> rel7 A B C D E F G) := 
  forall a b c d e f g ra ra' rb rb' (IN: gf ra rb a b c d e f g) (LEa: ra <7= ra') (LEb: rb <7= rb'), gf ra' rb' a b c d e f g.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable G : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e), Type.
Variables gfa gfb : rel7 A B C D E F G -> rel7 A B C D E F G -> rel7 A B C D E F G.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco7'a ra rb a b c d e f g : Prop :=
| paco7'a_pfold pcoa pcob
    (LEa : pcoa <7= (paco7'a ra rb \7/ ra))
    (LEb : pcob <7= (paco7'b ra rb \7/ rb))
    (SIM: gfa pcoa pcob a b c d e f g)
with paco7'b ra rb a b c d e f g : Prop :=
| paco7'b_pfold pcoa pcob
    (LEa : pcoa <7= (paco7'a ra rb \7/ ra))
    (LEb : pcob <7= (paco7'b ra rb \7/ rb))
    (SIM: gfb pcoa pcob a b c d e f g)
.
Implicit Arguments paco7'a [].
Implicit Arguments paco7'b [].

Theorem paco7'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <7= rr) (CIH: l <7= rr), l <7= paco7'a rr rb),
  l <7= paco7'a ra rb.
Proof.
  intros; assert (SIM: paco7'a (ra \7/ l) rb a b c d e f g) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <7= rr) (CIH: l <7= rr), l <7= paco7'b ra rr),
  l <7= paco7'b ra rb.
Proof.
  intros; assert (SIM: paco7'b ra (rb \7/ l) a b c d e f g) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7'a_mon: monotone7' paco7'a.
Proof. paco_cofix_auto; left; do 8 paco_revert; paco_cofix_auto. Qed.

Theorem paco7'b_mon: monotone7' paco7'b.
Proof. paco_cofix_auto; left; do 8 paco_revert; paco_cofix_auto. Qed.

Theorem paco7'a_mult_strong: forall ra rb,
  paco7'a (paco7'a ra rb \7/ ra) (paco7'b ra rb \7/ rb) <7= paco7'a ra rb.
Proof. paco_cofix_auto; left; do 8 paco_revert; paco_cofix_auto. Qed.

Theorem paco7'b_mult_strong: forall ra rb,
  paco7'b (paco7'a ra rb \7/ ra) (paco7'b ra rb \7/ rb) <7= paco7'b ra rb.
Proof. paco_cofix_auto; left; do 8 paco_revert; paco_cofix_auto. Qed.

Corollary paco7'a_mult: forall ra rb,
  paco7'a (paco7'a ra rb) (paco7'b ra rb) <7= paco7'a ra rb.
Proof. intros; eapply paco7'a_mult_strong, paco7'a_mon; eauto. Qed.

Corollary paco7'b_mult: forall ra rb,
  paco7'b (paco7'a ra rb) (paco7'b ra rb) <7= paco7'b ra rb.
Proof. intros; eapply paco7'b_mult_strong, paco7'b_mon; eauto. Qed.

Theorem paco7'a_fold: forall ra rb,
  gfa (paco7'a ra rb \7/ ra) (paco7'b ra rb \7/ rb) <7= paco7'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco7'b_fold: forall ra rb,
  gfb (paco7'a ra rb \7/ ra) (paco7'b ra rb \7/ rb) <7= paco7'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco7'a_unfold: forall
    (MONa: monotone7' gfa) (MONb: monotone7' gfb) ra rb,
  paco7'a ra rb 
  <7= gfa (paco7'a ra rb \7/ ra) (paco7'b ra rb \7/ rb).
Proof. unfold monotone7'; intros; destruct PR; eauto. Qed.

Theorem paco7'b_unfold: forall
    (MONa: monotone7' gfa) (MONb: monotone7' gfb) ra rb,
  paco7'b ra rb 
  <7= gfb (paco7'a ra rb \7/ ra) (paco7'b ra rb \7/ rb).
Proof. unfold monotone7'; intros; destruct PR; eauto. Qed.

End Arg7Two.

Hint Unfold monotone7'.
Hint Resolve paco7'a_fold.
Hint Resolve paco7'b_fold.

Implicit Arguments paco7'a_mon          [A B C D E F G].
Implicit Arguments paco7'b_mon          [A B C D E F G].
Implicit Arguments paco7'a_mult_strong  [A B C D E F G].
Implicit Arguments paco7'b_mult_strong  [A B C D E F G].
Implicit Arguments paco7'a_mult         [A B C D E F G].
Implicit Arguments paco7'b_mult         [A B C D E F G].

(** Three Mutual Coinduction *)

Section Arg7Three.

Definition monotone7'' A B C D E F G (gf: rel7 A B C D E F G -> rel7 A B C D E F G -> rel7 A B C D E F G -> rel7 A B C D E F G) := 
  forall a b c d e f g ra ra' rb rb' rc rc' (IN: gf ra rb rc a b c d e f g) (LEa: ra <7= ra') (LEb: rb <7= rb') (LEc: rc <7= rc'), gf ra' rb' rc' a b c d e f g.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable G : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e), Type.
Variables gfa gfb gfc : rel7 A B C D E F G -> rel7 A B C D E F G -> rel7 A B C D E F G -> rel7 A B C D E F G.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco7''a ra rb rc a b c d e f g : Prop :=
| paco7''a_pfold pcoa pcob pcoc
    (LEa : pcoa <7= (paco7''a ra rb rc \7/ ra))
    (LEb : pcob <7= (paco7''b ra rb rc \7/ rb))
    (LEc : pcoc <7= (paco7''c ra rb rc \7/ rc))
    (SIM: gfa pcoa pcob pcoc a b c d e f g)
with paco7''b ra rb rc a b c d e f g : Prop :=
| paco7''b_pfold pcoa pcob pcoc
    (LEa : pcoa <7= (paco7''a ra rb rc \7/ ra))
    (LEb : pcob <7= (paco7''b ra rb rc \7/ rb))
    (LEc : pcoc <7= (paco7''c ra rb rc \7/ rc))
    (SIM: gfb pcoa pcob pcoc a b c d e f g)
with paco7''c ra rb rc a b c d e f g : Prop :=
| paco7''c_pfold pcoa pcob pcoc
    (LEa : pcoa <7= (paco7''a ra rb rc \7/ ra))
    (LEb : pcob <7= (paco7''b ra rb rc \7/ rb))
    (LEc : pcoc <7= (paco7''c ra rb rc \7/ rc))
    (SIM: gfc pcoa pcob pcoc a b c d e f g)
.
Implicit Arguments paco7''a [].
Implicit Arguments paco7''b [].
Implicit Arguments paco7''c [].

Theorem paco7''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <7= rr) (CIH: l <7= rr), l <7= paco7''a rr rb rc),
  l <7= paco7''a ra rb rc.
Proof.
  intros; assert (SIM: paco7''a (ra \7/ l) rb rc a b c d e f g) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <7= rr) (CIH: l <7= rr), l <7= paco7''b ra rr rc),
  l <7= paco7''b ra rb rc.
Proof.
  intros; assert (SIM: paco7''b ra (rb \7/ l) rc a b c d e f g) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <7= rr) (CIH: l <7= rr), l <7= paco7''c ra rb rr),
  l <7= paco7''c ra rb rc.
Proof.
  intros; assert (SIM: paco7''c ra rb (rc \7/ l) a b c d e f g) by eauto.
  clear PR; repeat (try left; do 8 paco_revert; paco_cofix_auto).
Qed.

Theorem paco7''a_mon: monotone7'' paco7''a.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7''b_mon: monotone7'' paco7''b.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7''c_mon: monotone7'' paco7''c.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7''a_mult_strong: forall ra rb rc,
  paco7''a (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc)
  <7= paco7''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7''b_mult_strong: forall ra rb rc,
  paco7''b (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc)
  <7= paco7''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Theorem paco7''c_mult_strong: forall ra rb rc,
  paco7''c (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc)
  <7= paco7''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 8 paco_revert; paco_cofix_auto). Qed.

Corollary paco7''a_mult: forall ra rb rc,
  paco7''a (paco7''a ra rb rc) (paco7''b ra rb rc) (paco7''c ra rb rc)
  <7= paco7''a ra rb rc.
Proof. intros; eapply paco7''a_mult_strong, paco7''a_mon; eauto. Qed.

Corollary paco7''b_mult: forall ra rb rc,
  paco7''b (paco7''a ra rb rc) (paco7''b ra rb rc) (paco7''c ra rb rc)
  <7= paco7''b ra rb rc.
Proof. intros; eapply paco7''b_mult_strong, paco7''b_mon; eauto. Qed.

Corollary paco7''c_mult: forall ra rb rc,
  paco7''c (paco7''a ra rb rc) (paco7''b ra rb rc) (paco7''c ra rb rc)
  <7= paco7''c ra rb rc.
Proof. intros; eapply paco7''c_mult_strong, paco7''c_mon; eauto. Qed.

Theorem paco7''a_fold: forall ra rb rc,
  gfa (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc) 
  <7= paco7''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco7''b_fold: forall ra rb rc,
  gfb (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc) 
  <7= paco7''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco7''c_fold: forall ra rb rc,
  gfc (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc) 
  <7= paco7''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco7''a_unfold: forall
    (MONa: monotone7'' gfa) (MONb: monotone7'' gfb) (MONc: monotone7'' gfc) ra rb rc,
  paco7''a ra rb rc
  <7= gfa (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc).
Proof. unfold monotone7''; intros; destruct PR; eauto. Qed.

Theorem paco7''b_unfold: forall
    (MONa: monotone7'' gfa) (MONb: monotone7'' gfb) (MONc: monotone7'' gfc) ra rb rc,
  paco7''b ra rb rc
  <7= gfb (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc).
Proof. unfold monotone7''; intros; destruct PR; eauto. Qed.

Theorem paco7''c_unfold: forall
    (MONa: monotone7'' gfa) (MONb: monotone7'' gfb) (MONc: monotone7'' gfc) ra rb rc,
  paco7''c ra rb rc
  <7= gfc (paco7''a ra rb rc \7/ ra) (paco7''b ra rb rc \7/ rb) (paco7''c ra rb rc \7/ rc).
Proof. unfold monotone7''; intros; destruct PR; eauto. Qed.

End Arg7Three.

Hint Unfold monotone7''.
Hint Resolve paco7''a_fold.
Hint Resolve paco7''b_fold.
Hint Resolve paco7''c_fold.

Implicit Arguments paco7''a_mon         [A B C D E F G].
Implicit Arguments paco7''b_mon         [A B C D E F G].
Implicit Arguments paco7''c_mon         [A B C D E F G].
Implicit Arguments paco7''a_mult_strong [A B C D E F G].
Implicit Arguments paco7''b_mult_strong [A B C D E F G].
Implicit Arguments paco7''c_mult_strong [A B C D E F G].
Implicit Arguments paco7''a_mult        [A B C D E F G].
Implicit Arguments paco7''b_mult        [A B C D E F G].
Implicit Arguments paco7''c_mult        [A B C D E F G].

(** ** Predicates of arity 8 
*)

(** Single Coinduction *)

Section Arg8Single.

Definition monotone8 A B C D E F G H (gf: rel8 A B C D E F G H -> rel8 A B C D E F G H) := 
  forall a b c d e f g h r r' (IN: gf r a b c d e f g h) (LE: r <8= r'), gf r' a b c d e f g h.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable G : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e), Type.
Variable H : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e) (g: G f), Type.
Variable gf : rel8 A B C D E F G H -> rel8 A B C D E F G H.
Implicit Arguments gf [].

CoInductive paco8 r a b c d e f g h : Prop :=
| paco8_pfold pco
    (LE : pco <8= (paco8 r \8/ r))
    (SIM: gf pco a b c d e f g h)
.
Implicit Arguments paco8 [].

Theorem paco8_acc: forall
    l r (OBG: forall rr (INC: r <8= rr) (CIH: l <8= rr), l <8= paco8 rr),
  l <8= paco8 r.
Proof.
  intros; assert (SIM: paco8 (r \8/ l) a b c d e f g h) by eauto.
  clear PR; do 9 paco_revert; paco_cofix_auto.
Qed.

Theorem paco8_mon: monotone8 paco8.
Proof. paco_cofix_auto. Qed.

Theorem paco8_mult_strong: forall r,
  paco8 (paco8 r \8/ r) <8= paco8 r.
Proof. paco_cofix_auto. Qed.

Corollary paco8_mult: forall r,
  paco8 (paco8 r) <8= paco8 r.
Proof. intros; eapply paco8_mult_strong, paco8_mon; eauto. Qed.

Theorem paco8_fold: forall r,
  gf (paco8 r \8/ r) <8= paco8 r.
Proof. intros; econstructor; [|eauto]; eauto. Qed.    

Theorem paco8_unfold: forall (MON: monotone8 gf) r,
  paco8 r <8= gf (paco8 r \8/ r).
Proof. unfold monotone8; intros; destruct PR; eauto. Qed.

End Arg8Single.

Hint Unfold monotone8.
Hint Resolve paco8_fold.

Implicit Arguments paco8_mon            [A B C D E F G H].
Implicit Arguments paco8_mult_strong    [A B C D E F G H].
Implicit Arguments paco8_mult           [A B C D E F G H].

(** Two Mutual Coinduction *)

Section Arg8Two.

Definition monotone8' A B C D E F G H (gf: rel8 A B C D E F G H -> rel8 A B C D E F G H -> rel8 A B C D E F G H) := 
  forall a b c d e f g h ra ra' rb rb' (IN: gf ra rb a b c d e f g h) (LEa: ra <8= ra') (LEb: rb <8= rb'), gf ra' rb' a b c d e f g h.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable G : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e), Type.
Variable H : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e) (g: G f), Type.
Variables gfa gfb : rel8 A B C D E F G H -> rel8 A B C D E F G H -> rel8 A B C D E F G H.
Implicit Arguments gfa [].
Implicit Arguments gfb [].

CoInductive paco8'a ra rb a b c d e f g h : Prop :=
| paco8'a_pfold pcoa pcob
    (LEa : pcoa <8= (paco8'a ra rb \8/ ra))
    (LEb : pcob <8= (paco8'b ra rb \8/ rb))
    (SIM: gfa pcoa pcob a b c d e f g h)
with paco8'b ra rb a b c d e f g h : Prop :=
| paco8'b_pfold pcoa pcob
    (LEa : pcoa <8= (paco8'a ra rb \8/ ra))
    (LEb : pcob <8= (paco8'b ra rb \8/ rb))
    (SIM: gfb pcoa pcob a b c d e f g h)
.
Implicit Arguments paco8'a [].
Implicit Arguments paco8'b [].

Theorem paco8'a_acc: forall
    l ra rb (OBG: forall rr (INC: ra <8= rr) (CIH: l <8= rr), l <8= paco8'a rr rb),
  l <8= paco8'a ra rb.
Proof.
  intros; assert (SIM: paco8'a (ra \8/ l) rb a b c d e f g h) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8'b_acc: forall
    l ra rb (OBG: forall rr (INC: rb <8= rr) (CIH: l <8= rr), l <8= paco8'b ra rr),
  l <8= paco8'b ra rb.
Proof.
  intros; assert (SIM: paco8'b ra (rb \8/ l) a b c d e f g h) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8'a_mon: monotone8' paco8'a.
Proof. paco_cofix_auto; left; do 9 paco_revert; paco_cofix_auto. Qed.

Theorem paco8'b_mon: monotone8' paco8'b.
Proof. paco_cofix_auto; left; do 9 paco_revert; paco_cofix_auto. Qed.

Theorem paco8'a_mult_strong: forall ra rb,
  paco8'a (paco8'a ra rb \8/ ra) (paco8'b ra rb \8/ rb) <8= paco8'a ra rb.
Proof. paco_cofix_auto; left; do 9 paco_revert; paco_cofix_auto. Qed.

Theorem paco8'b_mult_strong: forall ra rb,
  paco8'b (paco8'a ra rb \8/ ra) (paco8'b ra rb \8/ rb) <8= paco8'b ra rb.
Proof. paco_cofix_auto; left; do 9 paco_revert; paco_cofix_auto. Qed.

Corollary paco8'a_mult: forall ra rb,
  paco8'a (paco8'a ra rb) (paco8'b ra rb) <8= paco8'a ra rb.
Proof. intros; eapply paco8'a_mult_strong, paco8'a_mon; eauto. Qed.

Corollary paco8'b_mult: forall ra rb,
  paco8'b (paco8'a ra rb) (paco8'b ra rb) <8= paco8'b ra rb.
Proof. intros; eapply paco8'b_mult_strong, paco8'b_mon; eauto. Qed.

Theorem paco8'a_fold: forall ra rb,
  gfa (paco8'a ra rb \8/ ra) (paco8'b ra rb \8/ rb) <8= paco8'a ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco8'b_fold: forall ra rb,
  gfb (paco8'a ra rb \8/ ra) (paco8'b ra rb \8/ rb) <8= paco8'b ra rb.
Proof. intros; econstructor; [| |eauto]; eauto. Qed.    

Theorem paco8'a_unfold: forall
    (MONa: monotone8' gfa) (MONb: monotone8' gfb) ra rb,
  paco8'a ra rb 
  <8= gfa (paco8'a ra rb \8/ ra) (paco8'b ra rb \8/ rb).
Proof. unfold monotone8'; intros; destruct PR; eauto. Qed.

Theorem paco8'b_unfold: forall
    (MONa: monotone8' gfa) (MONb: monotone8' gfb) ra rb,
  paco8'b ra rb 
  <8= gfb (paco8'a ra rb \8/ ra) (paco8'b ra rb \8/ rb).
Proof. unfold monotone8'; intros; destruct PR; eauto. Qed.

End Arg8Two.

Hint Unfold monotone8'.
Hint Resolve paco8'a_fold.
Hint Resolve paco8'b_fold.

Implicit Arguments paco8'a_mon          [A B C D E F G H].
Implicit Arguments paco8'b_mon          [A B C D E F G H].
Implicit Arguments paco8'a_mult_strong  [A B C D E F G H].
Implicit Arguments paco8'b_mult_strong  [A B C D E F G H].
Implicit Arguments paco8'a_mult         [A B C D E F G H].
Implicit Arguments paco8'b_mult         [A B C D E F G H].

(** Three Mutual Coinduction *)

Section Arg8Three.

Definition monotone8'' A B C D E F G H (gf: rel8 A B C D E F G H -> rel8 A B C D E F G H -> rel8 A B C D E F G H -> rel8 A B C D E F G H) := 
  forall a b c d e f g h ra ra' rb rb' rc rc' (IN: gf ra rb rc a b c d e f g h) (LEa: ra <8= ra') (LEb: rb <8= rb') (LEc: rc <8= rc'), gf ra' rb' rc' a b c d e f g h.

Variable A : Type.
Variable B : forall a: A, Type.
Variable C : forall (a: A) (b: B a), Type.
Variable D : forall (a: A) (b: B a) (c: C b), Type.
Variable E : forall (a: A) (b: B a) (c: C b) (d: D c), Type.
Variable F : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d), Type.
Variable G : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e), Type.
Variable H : forall (a: A) (b: B a) (c: C b) (d: D c) (e: E d) (f: F e) (g: G f), Type.
Variables gfa gfb gfc : rel8 A B C D E F G H -> rel8 A B C D E F G H -> rel8 A B C D E F G H -> rel8 A B C D E F G H.
Implicit Arguments gfa [].
Implicit Arguments gfb [].
Implicit Arguments gfc [].

CoInductive paco8''a ra rb rc a b c d e f g h : Prop :=
| paco8''a_pfold pcoa pcob pcoc
    (LEa : pcoa <8= (paco8''a ra rb rc \8/ ra))
    (LEb : pcob <8= (paco8''b ra rb rc \8/ rb))
    (LEc : pcoc <8= (paco8''c ra rb rc \8/ rc))
    (SIM: gfa pcoa pcob pcoc a b c d e f g h)
with paco8''b ra rb rc a b c d e f g h : Prop :=
| paco8''b_pfold pcoa pcob pcoc
    (LEa : pcoa <8= (paco8''a ra rb rc \8/ ra))
    (LEb : pcob <8= (paco8''b ra rb rc \8/ rb))
    (LEc : pcoc <8= (paco8''c ra rb rc \8/ rc))
    (SIM: gfb pcoa pcob pcoc a b c d e f g h)
with paco8''c ra rb rc a b c d e f g h : Prop :=
| paco8''c_pfold pcoa pcob pcoc
    (LEa : pcoa <8= (paco8''a ra rb rc \8/ ra))
    (LEb : pcob <8= (paco8''b ra rb rc \8/ rb))
    (LEc : pcoc <8= (paco8''c ra rb rc \8/ rc))
    (SIM: gfc pcoa pcob pcoc a b c d e f g h)
.
Implicit Arguments paco8''a [].
Implicit Arguments paco8''b [].
Implicit Arguments paco8''c [].

Theorem paco8''a_acc: forall
    l ra rb rc (OBG: forall rr (INC: ra <8= rr) (CIH: l <8= rr), l <8= paco8''a rr rb rc),
  l <8= paco8''a ra rb rc.
Proof.
  intros; assert (SIM: paco8''a (ra \8/ l) rb rc a b c d e f g h) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8''b_acc: forall
    l ra rb rc (OBG: forall rr (INC: rb <8= rr) (CIH: l <8= rr), l <8= paco8''b ra rr rc),
  l <8= paco8''b ra rb rc.
Proof.
  intros; assert (SIM: paco8''b ra (rb \8/ l) rc a b c d e f g h) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8''c_acc: forall
    l ra rb rc (OBG: forall rr (INC: rc <8= rr) (CIH: l <8= rr), l <8= paco8''c ra rb rr),
  l <8= paco8''c ra rb rc.
Proof.
  intros; assert (SIM: paco8''c ra rb (rc \8/ l) a b c d e f g h) by eauto.
  clear PR; repeat (try left; do 9 paco_revert; paco_cofix_auto).
Qed.

Theorem paco8''a_mon: monotone8'' paco8''a.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8''b_mon: monotone8'' paco8''b.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8''c_mon: monotone8'' paco8''c.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8''a_mult_strong: forall ra rb rc,
  paco8''a (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc)
  <8= paco8''a ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8''b_mult_strong: forall ra rb rc,
  paco8''b (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc)
  <8= paco8''b ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Theorem paco8''c_mult_strong: forall ra rb rc,
  paco8''c (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc)
  <8= paco8''c ra rb rc.
Proof. paco_cofix_auto; repeat (left; do 9 paco_revert; paco_cofix_auto). Qed.

Corollary paco8''a_mult: forall ra rb rc,
  paco8''a (paco8''a ra rb rc) (paco8''b ra rb rc) (paco8''c ra rb rc)
  <8= paco8''a ra rb rc.
Proof. intros; eapply paco8''a_mult_strong, paco8''a_mon; eauto. Qed.

Corollary paco8''b_mult: forall ra rb rc,
  paco8''b (paco8''a ra rb rc) (paco8''b ra rb rc) (paco8''c ra rb rc)
  <8= paco8''b ra rb rc.
Proof. intros; eapply paco8''b_mult_strong, paco8''b_mon; eauto. Qed.

Corollary paco8''c_mult: forall ra rb rc,
  paco8''c (paco8''a ra rb rc) (paco8''b ra rb rc) (paco8''c ra rb rc)
  <8= paco8''c ra rb rc.
Proof. intros; eapply paco8''c_mult_strong, paco8''c_mon; eauto. Qed.

Theorem paco8''a_fold: forall ra rb rc,
  gfa (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc) 
  <8= paco8''a ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco8''b_fold: forall ra rb rc,
  gfb (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc) 
  <8= paco8''b ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco8''c_fold: forall ra rb rc,
  gfc (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc) 
  <8= paco8''c ra rb rc.
Proof. intros; econstructor; [| | |eauto]; eauto. Qed.    

Theorem paco8''a_unfold: forall
    (MONa: monotone8'' gfa) (MONb: monotone8'' gfb) (MONc: monotone8'' gfc) ra rb rc,
  paco8''a ra rb rc
  <8= gfa (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc).
Proof. unfold monotone8''; intros; destruct PR; eauto. Qed.

Theorem paco8''b_unfold: forall
    (MONa: monotone8'' gfa) (MONb: monotone8'' gfb) (MONc: monotone8'' gfc) ra rb rc,
  paco8''b ra rb rc
  <8= gfb (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc).
Proof. unfold monotone8''; intros; destruct PR; eauto. Qed.

Theorem paco8''c_unfold: forall
    (MONa: monotone8'' gfa) (MONb: monotone8'' gfb) (MONc: monotone8'' gfc) ra rb rc,
  paco8''c ra rb rc
  <8= gfc (paco8''a ra rb rc \8/ ra) (paco8''b ra rb rc \8/ rb) (paco8''c ra rb rc \8/ rc).
Proof. unfold monotone8''; intros; destruct PR; eauto. Qed.

End Arg8Three.

Hint Unfold monotone8''.
Hint Resolve paco8''a_fold.
Hint Resolve paco8''b_fold.
Hint Resolve paco8''c_fold.

Implicit Arguments paco8''a_mon         [A B C D E F G H].
Implicit Arguments paco8''b_mon         [A B C D E F G H].
Implicit Arguments paco8''c_mon         [A B C D E F G H].
Implicit Arguments paco8''a_mult_strong [A B C D E F G H].
Implicit Arguments paco8''b_mult_strong [A B C D E F G H].
Implicit Arguments paco8''c_mult_strong [A B C D E F G H].
Implicit Arguments paco8''a_mult        [A B C D E F G H].
Implicit Arguments paco8''b_mult        [A B C D E F G H].
Implicit Arguments paco8''c_mult        [A B C D E F G H].

(** ** pcofix tactic 
*)

Tactic Notation "pcofix" ident(CIH) "with" ident(r) :=
  generalize _pcfix_mark_cons; repeat intro; repeat red; 
  match goal with 
  | [|- @paco1 _ _ _            ?e1] => pcfix_cont1 e1; eapply paco1_acc ; pcpost1 CIH with r   
  | [|- @paco1'a _ _ _ _ _      ?e1] => pcfix_cont1 e1; eapply paco1'a_acc ; pcpost1 CIH with r 
  | [|- @paco1'b _ _ _ _ _      ?e1] => pcfix_cont1 e1; eapply paco1'b_acc ; pcpost1 CIH with r 
  | [|- @paco1''a _ _ _ _ _ _ _ ?e1] => pcfix_cont1 e1; eapply paco1''a_acc ; pcpost1 CIH with r
  | [|- @paco1''b _ _ _ _ _ _ _ ?e1] => pcfix_cont1 e1; eapply paco1''b_acc ; pcpost1 CIH with r
  | [|- @paco1''c _ _ _ _ _ _ _ ?e1] => pcfix_cont1 e1; eapply paco1''c_acc ; pcpost1 CIH with r

  | [|- @paco2 _ _ _ _            ?e1 ?e2] => pcfix_cont2 e1 e2; eapply paco2_acc ; pcpost2 CIH with r   
  | [|- @paco2'a _ _ _ _ _ _      ?e1 ?e2] => pcfix_cont2 e1 e2; eapply paco2'a_acc ; pcpost2 CIH with r 
  | [|- @paco2'b _ _ _ _ _ _      ?e1 ?e2] => pcfix_cont2 e1 e2; eapply paco2'b_acc ; pcpost2 CIH with r 
  | [|- @paco2''a _ _ _ _ _ _ _ _ ?e1 ?e2] => pcfix_cont2 e1 e2; eapply paco2''a_acc ; pcpost2 CIH with r
  | [|- @paco2''b _ _ _ _ _ _ _ _ ?e1 ?e2] => pcfix_cont2 e1 e2; eapply paco2''b_acc ; pcpost2 CIH with r
  | [|- @paco2''c _ _ _ _ _ _ _ _ ?e1 ?e2] => pcfix_cont2 e1 e2; eapply paco2''c_acc ; pcpost2 CIH with r

  | [|- @paco3 _ _ _ _ _            ?e1 ?e2 ?e3] => pcfix_cont3 e1 e2 e3; eapply paco3_acc ; pcpost3 CIH with r   
  | [|- @paco3'a _ _ _ _ _ _ _      ?e1 ?e2 ?e3] => pcfix_cont3 e1 e2 e3; eapply paco3'a_acc ; pcpost3 CIH with r 
  | [|- @paco3'b _ _ _ _ _ _ _      ?e1 ?e2 ?e3] => pcfix_cont3 e1 e2 e3; eapply paco3'b_acc ; pcpost3 CIH with r 
  | [|- @paco3''a _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3] => pcfix_cont3 e1 e2 e3; eapply paco3''a_acc ; pcpost3 CIH with r
  | [|- @paco3''b _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3] => pcfix_cont3 e1 e2 e3; eapply paco3''b_acc ; pcpost3 CIH with r
  | [|- @paco3''c _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3] => pcfix_cont3 e1 e2 e3; eapply paco3''c_acc ; pcpost3 CIH with r

  | [|- @paco4 _ _ _ _ _ _            ?e1 ?e2 ?e3 ?e4] => pcfix_cont4 e1 e2 e3 e4; eapply paco4_acc ; pcpost4 CIH with r   
  | [|- @paco4'a _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4] => pcfix_cont4 e1 e2 e3 e4; eapply paco4'a_acc ; pcpost4 CIH with r 
  | [|- @paco4'b _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4] => pcfix_cont4 e1 e2 e3 e4; eapply paco4'b_acc ; pcpost4 CIH with r 
  | [|- @paco4''a _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4] => pcfix_cont4 e1 e2 e3 e4; eapply paco4''a_acc ; pcpost4 CIH with r
  | [|- @paco4''b _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4] => pcfix_cont4 e1 e2 e3 e4; eapply paco4''b_acc ; pcpost4 CIH with r
  | [|- @paco4''c _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4] => pcfix_cont4 e1 e2 e3 e4; eapply paco4''c_acc ; pcpost4 CIH with r

  | [|- @paco5 _ _ _ _ _ _ _            ?e1 ?e2 ?e3 ?e4 ?e5] => pcfix_cont5 e1 e2 e3 e4 e5; eapply paco5_acc ; pcpost5 CIH with r   
  | [|- @paco5'a _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5] => pcfix_cont5 e1 e2 e3 e4 e5; eapply paco5'a_acc ; pcpost5 CIH with r 
  | [|- @paco5'b _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5] => pcfix_cont5 e1 e2 e3 e4 e5; eapply paco5'b_acc ; pcpost5 CIH with r 
  | [|- @paco5''a _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5] => pcfix_cont5 e1 e2 e3 e4 e5; eapply paco5''a_acc ; pcpost5 CIH with r
  | [|- @paco5''b _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5] => pcfix_cont5 e1 e2 e3 e4 e5; eapply paco5''b_acc ; pcpost5 CIH with r
  | [|- @paco5''c _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5] => pcfix_cont5 e1 e2 e3 e4 e5; eapply paco5''c_acc ; pcpost5 CIH with r

  | [|- @paco6 _ _ _ _ _ _ _ _            ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => pcfix_cont6 e1 e2 e3 e4 e5 e6; eapply paco6_acc ; pcpost6 CIH with r   
  | [|- @paco6'a _ _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => pcfix_cont6 e1 e2 e3 e4 e5 e6; eapply paco6'a_acc ; pcpost6 CIH with r 
  | [|- @paco6'b _ _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => pcfix_cont6 e1 e2 e3 e4 e5 e6; eapply paco6'b_acc ; pcpost6 CIH with r 
  | [|- @paco6''a _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => pcfix_cont6 e1 e2 e3 e4 e5 e6; eapply paco6''a_acc ; pcpost6 CIH with r
  | [|- @paco6''b _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => pcfix_cont6 e1 e2 e3 e4 e5 e6; eapply paco6''b_acc ; pcpost6 CIH with r
  | [|- @paco6''c _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6] => pcfix_cont6 e1 e2 e3 e4 e5 e6; eapply paco6''c_acc ; pcpost6 CIH with r

  | [|- @paco7 _ _ _ _ _ _ _ _ _            ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => pcfix_cont7 e1 e2 e3 e4 e5 e6 e7; eapply paco7_acc ; pcpost7 CIH with r   
  | [|- @paco7'a _ _ _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => pcfix_cont7 e1 e2 e3 e4 e5 e6 e7; eapply paco7'a_acc ; pcpost7 CIH with r 
  | [|- @paco7'b _ _ _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => pcfix_cont7 e1 e2 e3 e4 e5 e6 e7; eapply paco7'b_acc ; pcpost7 CIH with r 
  | [|- @paco7''a _ _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => pcfix_cont7 e1 e2 e3 e4 e5 e6 e7; eapply paco7''a_acc ; pcpost7 CIH with r
  | [|- @paco7''b _ _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => pcfix_cont7 e1 e2 e3 e4 e5 e6 e7; eapply paco7''b_acc ; pcpost7 CIH with r
  | [|- @paco7''c _ _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7] => pcfix_cont7 e1 e2 e3 e4 e5 e6 e7; eapply paco7''c_acc ; pcpost7 CIH with r

  | [|- @paco8 _ _ _ _ _ _ _ _ _ _            ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8; eapply paco8_acc ; pcpost8 CIH with r   
  | [|- @paco8'a _ _ _ _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8; eapply paco8'a_acc ; pcpost8 CIH with r 
  | [|- @paco8'b _ _ _ _ _ _ _ _ _ _ _ _      ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8; eapply paco8'b_acc ; pcpost8 CIH with r 
  | [|- @paco8''a _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8; eapply paco8''a_acc ; pcpost8 CIH with r
  | [|- @paco8''b _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8; eapply paco8''b_acc ; pcpost8 CIH with r
  | [|- @paco8''c _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8] => pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8; eapply paco8''c_acc ; pcpost8 CIH with r

  | [|- @paco0 _ _]            => pcfix_cont0; eapply paco0_acc ; pcpost0 CIH with r
  | [|- @paco0'a _ _ _ _]      => pcfix_cont0; eapply paco0'a_acc ; pcpost0 CIH with r
  | [|- @paco0'b _ _ _ _]      => pcfix_cont0; eapply paco0'b_acc ; pcpost0 CIH with r
  | [|- @paco0''a _ _ _ _ _ _] => pcfix_cont0; eapply paco0''a_acc ; pcpost0 CIH with r
  | [|- @paco0''b _ _ _ _ _ _] => pcfix_cont0; eapply paco0''b_acc ; pcpost0 CIH with r
  | [|- @paco0''c _ _ _ _ _ _] => pcfix_cont0; eapply paco0''c_acc ; pcpost0 CIH with r
  end.

Tactic Notation "pcofix" ident(CIH) := pcofix CIH with r.

