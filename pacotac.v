Require Import JMeq.
Require Import hpattern.
Require Export paconotation.

(** * Tactic support for [paco] library 

    This file defines tactics for converting the conclusion to the right form so
    that the accumulation lemmas can be usefully applied. These tactics are used
    in both internal and external approaches.

    Our main tactic, [pcofix], is defined at the end of the file and
    works for predicates of arity up to 8.
*)

(** ** Internal tactics *)

Inductive _pcfix_mark := _pcfix_mark_cons.

Inductive _pcfix_mark' := _pcfix_mark'_cons.

Lemma eq_JMeq: forall A (a b: A), a = b -> JMeq a b.
Proof. intros; subst; apply JMeq_refl. Defined.

Ltac simplJM mark := 
  repeat match goal with [H: ?x |- _] =>
    match x with
    | mark => idtac
    | JMeq _ _  => apply JMeq_eq in H 
    | ?a = _ => subst a
    end
  end.

Ltac hrewrite_last e H := let x := fresh "_x" in
    first [try (set (x:=e) at 9; fail 1);
      first [try (set (x:=e) at 5; fail 1);
        first [try (set (x:=e) at 3; fail 1);
          first [try (set (x:=e) at 2; fail 1);
            try (hrewrite H at 1)
          | try (hrewrite H at 2) ]
        | first [try (set (x:=e) at 4; fail 1);
            try (hrewrite H at 3)
          | try (hrewrite H at 4) ] ]
      | first [try (set (x:=e) at 7; fail 1);
          first [try (set (x:=e) at 6; fail 1);
            try (hrewrite H at 5)
          | try (hrewrite H at 6)]
        | first [try (set (x:=e) at 8; fail 1);
            try (hrewrite H at 7)
          | try (hrewrite H at 8) ] ] ]
    | first [try (set (x:=e) at 13; fail 1);
        first [try (set (x:=e) at 11; fail 1);
          first [try (set (x:=e) at 10; fail 1);
            try (hrewrite H at 9)
          | try (hrewrite H at 10) ]
        | first [try (set (x:=e) at 12; fail 1);
            try (hrewrite H at 11)
          | try (hrewrite H at 12) ] ]
      | first [try (set (x:=e) at 15; fail 1);
          first [try (set (x:=e) at 14; fail 1);
            try (hrewrite H at 13)
          | try (hrewrite H at 14)]
        | first [try (set (x:=e) at 16; fail 1);
            try (hrewrite H at 15)
          | try (hrewrite H at 16) ] ] ] ]
.

Ltac pcfix_generalize_hyp mark :=
  let y := fresh "_rel" in
  match goal with
  | [x: ?A |- _] => 
    match A with 
    | mark => clear x
    | _ => intro y;
      match type of y with
        | context[x] => revert x y; 
          match goal with [|-forall x, @?f x -> _] => 
            intros x y; generalize (ex_intro f x y) 
          end
        | _ => generalize (conj y x)
      end; clear x y; pcfix_generalize_hyp mark
    end
  end.

Ltac pcfix_convert e x EQ :=
  generalize (eq_refl e); generalize e at 2; intros x EQ; 
  hrewrite_last e EQ; apply eq_sym, eq_JMeq in EQ; revert x EQ.

Ltac pcfix_destruct_hyp mark :=
  match goal with 
  | [x: ?A |- _] =>
    match A with
    | mark => idtac
    | exists n, ?p => let n' := fresh n in destruct x as (n', x); pcfix_destruct_hyp mark
    | ?p /\ ?q => let x' := fresh x in destruct x as (x,x'); pcfix_destruct_hyp mark
    end 
  end. 

Ltac pcfix_revert_hyp mark :=
  match goal with [x: ?A |- _] =>
  match A with
    | mark => clear x
    | _ => revert x; pcfix_revert_hyp mark
  end end.

Ltac pcfix_post_var INC pr cr := let TMP := fresh "_tmp" in
  repeat (
    match goal with [H: context f [pr] |-_] => 
      let cih := context f [cr] in rename H into TMP; 
      assert(H : cih) by (repeat intro; eapply INC, TMP; eassumption); clear TMP
    end);
  clear INC pr. 

Ltac pcfix_simp_hyp CIH :=
  let EP := fresh "__EP__" in
  let FP := fresh "__FF__" in
  let TP := fresh "__TP__" in
  let XP := fresh "__XP__" in
  let PP := type of CIH in 
  evar (EP: Prop); 
  assert (TP: False -> PP) by (
    intros FP; generalize _pcfix_mark_cons; repeat intro;
    pcfix_destruct_hyp _pcfix_mark; 
    pcfix_revert_hyp _pcfix_mark'; simplJM _pcfix_mark; pcfix_revert_hyp _pcfix_mark;
    let con := get_concl in set (TP:=con); revert EP; instantiate (1:= con); destruct FP);
  clear TP;
  assert (XP: EP) by (unfold EP; clear -CIH; repeat intro; apply CIH; 
    first [
      (repeat match goal with | [ |- @ex _ _ ] => eexists | [ |- _ /\ _ ] => split end; 
       first [apply eq_JMeq; reflexivity|eassumption|apply _pcfix_mark'_cons]); fail
    | repeat match goal with | [ |- @ex _ _ ] => eexists end; 
      eauto using eq_JMeq, _pcfix_mark'_cons]);
  unfold EP in *; clear EP CIH; rename XP into CIH.

Ltac pcfix_post_simp CIH :=
  let CIH := fresh CIH in let TMP := fresh "_TMP_" in
  intro CIH; pcfix_simp_hyp CIH;
  generalize _pcfix_mark_cons; intro TMP; 
  repeat intro; pcfix_destruct_hyp _pcfix_mark;
  pcfix_revert_hyp _pcfix_mark'; simplJM _pcfix_mark; pcfix_revert_hyp _pcfix_mark.

Ltac pcfix_ren_r nr cr := 
  first [rename cr into nr | let nr := fresh nr in rename cr into nr].

Ltac pcfix_ren_pr pr cr := rename cr into pr.

(** *** Arity 0 
*)

Ltac pcfix_cont0 := 
  generalize _pcfix_mark'_cons; pcfix_generalize_hyp _pcfix_mark.

Ltac pcpre0 :=
  generalize _pcfix_mark_cons; repeat intro; pcfix_cont0.

Ltac pcfix_post_match0 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | bot0 -> _ => clear H; tac1 cr
  | ?pr -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost0" ident(CIH) "with" ident(nr) := 
  pcfix_post_match0 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 1 
*)

Ltac pcfix_cont1 e1 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1;
  generalize (conj EQ1 _pcfix_mark'_cons); clear EQ1;
  move x1 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1.

Lemma _pcpre1: forall A (gf: rel1 A) a 
  (X: let gf' := gf in gf' a), gf a.
Proof. intros; apply X. Defined.

Ltac pcpre1 := let X := fresh "_X" in
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre1; intro X;
  match goal with
  | |- _ ?e1 => unfold X; clear X; pcfix_cont1 e1
  end.

Ltac pcfix_post_match1 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _, bot1 _ -> _ => clear H; tac1 cr
  | forall _, ?pr _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost1" ident(CIH) "with" ident(nr) := 
  pcfix_post_match1 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 2 
*)

Ltac pcfix_cont2 e1 e2 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2;
  generalize (conj (conj EQ1 EQ2) _pcfix_mark'_cons); clear EQ1 EQ2;
  move x1 at top; move x2 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2.

Lemma _pcpre2: forall A B (gf: rel2 A B) a b 
  (X: let gf' := gf in gf' a b), gf a b.
Proof. intros; apply X. Defined.

Ltac pcpre2 := let X := fresh "_X" in
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre2; intro X;
  match goal with
  | |- _ ?e1 ?e2 => unfold X; clear X; pcfix_cont2 e1 e2
  end.

Ltac pcfix_post_match2 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _, bot2 _ _ -> _ => clear H; tac1 cr
  | forall _ _, ?pr _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost2" ident(CIH) "with" ident(nr) := 
  pcfix_post_match2 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 3 
*)

Ltac pcfix_cont3 e1 e2 e3 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  let x3 := fresh "_v" in let EQ3 := fresh "_EQ" in
  pcfix_convert e3 x3 EQ3;
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2 x3 EQ3;
  generalize (conj (conj EQ1 (conj EQ2 EQ3)) _pcfix_mark'_cons); clear EQ1 EQ2 EQ3;
  move x1 at top; move x2 at top; move x3 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2 x3.

Lemma _pcpre3: forall A B C (gf: rel3 A B C) a b c
  (X: let gf' := gf in gf' a b c), gf a b c.
Proof. intros; apply X. Defined.

Ltac pcpre3 := let X := fresh "_X" in
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre3; intro X;
  match goal with
  | |- _ ?e1 ?e2 ?e3 => unfold X; clear X; pcfix_cont3 e1 e2 e3
  end.

Ltac pcfix_post_match3 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _ _, bot3 _ _ _ -> _ => clear H; tac1 cr
  | forall _ _ _, ?pr _ _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost3" ident(CIH) "with" ident(nr) := 
  pcfix_post_match3 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 4 
*)

Ltac pcfix_cont4 e1 e2 e3 e4 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  let x3 := fresh "_v" in let EQ3 := fresh "_EQ" in
  let x4 := fresh "_v" in let EQ4 := fresh "_EQ" in
  pcfix_convert e4 x4 EQ4;
  pcfix_convert e3 x3 EQ3;
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2 x3 EQ3 x4 EQ4;
  generalize (conj (conj EQ1 (conj EQ2 (conj EQ3 EQ4))) _pcfix_mark'_cons); clear EQ1 EQ2 EQ3 EQ4;
  move x1 at top; move x2 at top; move x3 at top; move x4 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2 x3 x4.

Lemma _pcpre4: forall A B C D (gf: rel4 A B C D) a b c d
  (X: let gf' := gf in gf' a b c d), gf a b c d.
Proof. intros; apply X. Defined.

Ltac pcpre4 := let X := fresh "_X" in
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre4; intro X;
  match goal with
  | |- _ ?e1 ?e2 ?e3 ?e4 => unfold X; clear X; pcfix_cont4 e1 e2 e3 e4
  end.

Ltac pcfix_post_match4 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _ _ _, bot4 _ _ _ _ -> _ => clear H; tac1 cr
  | forall _ _ _ _, ?pr _ _ _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost4" ident(CIH) "with" ident(nr) := 
  pcfix_post_match4 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 5 
*)

Ltac pcfix_cont5 e1 e2 e3 e4 e5 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  let x3 := fresh "_v" in let EQ3 := fresh "_EQ" in
  let x4 := fresh "_v" in let EQ4 := fresh "_EQ" in
  let x5 := fresh "_v" in let EQ5 := fresh "_EQ" in
  pcfix_convert e5 x5 EQ5;
  pcfix_convert e4 x4 EQ4;
  pcfix_convert e3 x3 EQ3;
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2 x3 EQ3 x4 EQ4 x5 EQ5;
  generalize (conj (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 EQ5)))) _pcfix_mark'_cons); clear EQ1 EQ2 EQ3 EQ4 EQ5;
  move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2 x3 x4 x5.

Lemma _pcpre5: forall A B C D E (gf: rel5 A B C D E) a b c d e
  (X: let gf' := gf in gf' a b c d e), gf a b c d e.
Proof. intros; apply X. Defined.

Ltac pcpre5 := let X := fresh "_X" in
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre5; intro X;
  match goal with
  | |- _ ?e1 ?e2 ?e3 ?e4 ?e5 => unfold X; clear X; pcfix_cont5 e1 e2 e3 e4 e5
  end.

Ltac pcfix_post_match5 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _ _ _ _, bot5 _ _ _ _ _ -> _ => clear H; tac1 cr
  | forall _ _ _ _ _, ?pr _ _ _ _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost5" ident(CIH) "with" ident(nr) := 
  pcfix_post_match5 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 6 
*)

Ltac pcfix_cont6 e1 e2 e3 e4 e5 e6 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  let x3 := fresh "_v" in let EQ3 := fresh "_EQ" in
  let x4 := fresh "_v" in let EQ4 := fresh "_EQ" in
  let x5 := fresh "_v" in let EQ5 := fresh "_EQ" in
  let x6 := fresh "_v" in let EQ6 := fresh "_EQ" in
  pcfix_convert e6 x6 EQ6;
  pcfix_convert e5 x5 EQ5;
  pcfix_convert e4 x4 EQ4;
  pcfix_convert e3 x3 EQ3;
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2 x3 EQ3 x4 EQ4 x5 EQ5 x6 EQ6;
  generalize (conj (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 EQ6))))) _pcfix_mark'_cons); clear EQ1 EQ2 EQ3 EQ4 EQ5 EQ6;
  move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2 x3 x4 x5 x6.

Lemma _pcpre6: forall A B C D E F (gf: rel6 A B C D E F) a b c d e f
  (X: let gf' := gf in gf' a b c d e f), gf a b c d e f.
Proof. intros; apply X. Defined.

Ltac pcpre6 :=
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre6; let X := fresh "X" in intro X;
  match goal with
  | |- _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 => unfold X; clear X; pcfix_cont6 e1 e2 e3 e4 e5 e6
  end.

Ltac pcfix_post_match6 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _ _ _ _ _, bot6 _ _ _ _ _ _ -> _ => clear H; tac1 cr
  | forall _ _ _ _ _ _, ?pr _ _ _ _ _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost6" ident(CIH) "with" ident(nr) := 
  pcfix_post_match6 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 7 
*)

Ltac pcfix_cont7 e1 e2 e3 e4 e5 e6 e7 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  let x3 := fresh "_v" in let EQ3 := fresh "_EQ" in
  let x4 := fresh "_v" in let EQ4 := fresh "_EQ" in
  let x5 := fresh "_v" in let EQ5 := fresh "_EQ" in
  let x6 := fresh "_v" in let EQ6 := fresh "_EQ" in
  let x7 := fresh "_v" in let EQ7 := fresh "_EQ" in
  pcfix_convert e7 x7 EQ7;
  pcfix_convert e6 x6 EQ6;
  pcfix_convert e5 x5 EQ5;
  pcfix_convert e4 x4 EQ4;
  pcfix_convert e3 x3 EQ3;
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2 x3 EQ3 x4 EQ4 x5 EQ5 x6 EQ6 x7 EQ7;
  generalize (conj (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 EQ7)))))) _pcfix_mark'_cons); clear EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7;
  move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2 x3 x4 x5 x6 x7.

Lemma _pcpre7: forall A B C D E F G (gf: rel7 A B C D E F G) a b c d e f g
  (X: let gf' := gf in gf' a b c d e f g), gf a b c d e f g.
Proof. intros; apply X. Defined.

Ltac pcpre7 :=
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre7; let X := fresh "X" in intro X;
  match goal with
  | |- _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 => unfold X; clear X; pcfix_cont7 e1 e2 e3 e4 e5 e6 e7
  end.

Ltac pcfix_post_match7 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _ _ _ _ _ _, bot7 _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
  | forall _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost7" ident(CIH) "with" ident(nr) := 
  pcfix_post_match7 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** *** Arity 8 
*)

Ltac pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8 := 
  let x1 := fresh "_v" in let EQ1 := fresh "_EQ" in
  let x2 := fresh "_v" in let EQ2 := fresh "_EQ" in
  let x3 := fresh "_v" in let EQ3 := fresh "_EQ" in
  let x4 := fresh "_v" in let EQ4 := fresh "_EQ" in
  let x5 := fresh "_v" in let EQ5 := fresh "_EQ" in
  let x6 := fresh "_v" in let EQ6 := fresh "_EQ" in
  let x7 := fresh "_v" in let EQ7 := fresh "_EQ" in
  let x8 := fresh "_v" in let EQ8 := fresh "_EQ" in
  pcfix_convert e8 x8 EQ8;
  pcfix_convert e7 x7 EQ7;
  pcfix_convert e6 x6 EQ6;
  pcfix_convert e5 x5 EQ5;
  pcfix_convert e4 x4 EQ4;
  pcfix_convert e3 x3 EQ3;
  pcfix_convert e2 x2 EQ2;
  pcfix_convert e1 x1 EQ1;
  intros x1 EQ1 x2 EQ2 x3 EQ3 x4 EQ4 x5 EQ5 x6 EQ6 x7 EQ7 x8 EQ8;
  generalize (conj (conj EQ1 (conj EQ2 (conj EQ3 (conj EQ4 (conj EQ5 (conj EQ6 (conj EQ7 EQ8))))))) _pcfix_mark'_cons); clear EQ1 EQ2 EQ3 EQ4 EQ5 EQ6 EQ7 EQ8;
  move x1 at top; move x2 at top; move x3 at top; move x4 at top; move x5 at top; move x6 at top; move x7 at top; move x8 at top;
  pcfix_generalize_hyp _pcfix_mark; revert x1 x2 x3 x4 x5 x6 x7 x8.

Lemma _pcpre8: forall A B C D E F G H (gf: rel8 A B C D E F G H) a b c d e f g h
  (X: let gf' := gf in gf' a b c d e f g h), gf a b c d e f g h.
Proof. intros; apply X. Defined.

Ltac pcpre8 :=
  generalize _pcfix_mark_cons; repeat intro;
  apply _pcpre8; let X := fresh "X" in intro X;
  match goal with
  | |- _ ?e1 ?e2 ?e3 ?e4 ?e5 ?e6 ?e7 ?e8 => unfold X; clear X; pcfix_cont8 e1 e2 e3 e4 e5 e6 e7 e8
  end.

Ltac pcfix_post_match8 tac1 tac2 := 
  let cr := fresh "_cr" in let INC := fresh "INC" in intros cr INC; repeat (red in INC);
  match goal with [H: ?x |- _] => match x with 
  | forall _ _ _ _ _ _ _ _, bot8 _ _ _ _ _ _ _ _ -> _ => clear H; tac1 cr
  | forall _ _ _ _ _ _ _ _, ?pr _ _ _ _ _ _ _ _ -> _ => pcfix_post_var INC pr cr; tac2 pr cr
  | _ => tac1 cr
  end end.

Tactic Notation "pcpost8" ident(CIH) "with" ident(nr) := 
  pcfix_post_match8 ltac:(pcfix_ren_r nr) pcfix_ren_pr; pcfix_post_simp CIH.

(** ** External interface *)

(** We provide our main tactics:

    - [pcofix{n} ident using lemma with ident']


    where [ident] is the identifier used to name the generated coinduction hypothesis,
    [lemma] is an expression denoting which accumulation lemma is to be used, and
    [ident'] is the identifier used to name the accumulation variable.
*)

Tactic Notation "pcofix0" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre0; eapply lem; pcpost0 CIH with r.

Tactic Notation "pcofix1" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre1; eapply lem; pcpost1 CIH with r.

Tactic Notation "pcofix2" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre2; eapply lem; pcpost2 CIH with r.

Tactic Notation "pcofix3" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre3; eapply lem; pcpost3 CIH with r.

Tactic Notation "pcofix4" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre4; eapply lem; pcpost4 CIH with r.

Tactic Notation "pcofix5" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre5; eapply lem; pcpost5 CIH with r.

Tactic Notation "pcofix6" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre6; eapply lem; pcpost6 CIH with r.

Tactic Notation "pcofix7" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre7; eapply lem; pcpost7 CIH with r.

Tactic Notation "pcofix8" ident(CIH) "using" constr(lem) "with" ident(r) := 
  pcpre8; eapply lem; pcpost8 CIH with r.

(** [pcofix] automatically figures out the appropriate index [n] from
    the type of the accumulation lemma [lem] and applies [pcofix{n}].
*)

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) "with" ident(nr) := 
  let N := fresh "_N" in let TMP := fresh "_TMP" in
  evar (N : nat);
  let P := type of lem in
  assert (TMP: False -> P) by
    (intro TMP; repeat intro; match goal with [H : _ |- _] => revert H end;
     match goal with 
     | [|- _ _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 8)
     | [|- _ _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 7)
     | [|- _ _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 6)
     | [|- _ _ _ _ _ _ -> _] => revert N; instantiate (1 := 5)
     | [|- _ _ _ _ _ -> _] => revert N; instantiate (1 := 4)
     | [|- _ _ _ _ -> _] => revert N; instantiate (1 := 3)
     | [|- _ _ _ -> _] => revert N; instantiate (1 := 2)
     | [|- _ _ -> _] => revert N; instantiate (1 := 1)
     | [|- _ -> _] => revert N; instantiate (1 := 0)
     end; destruct TMP);
  clear TMP;
  revert N;
  match goal with 
  | [|- let _ := 0 in _] => intros _; pcofix0 CIH using lem with nr
  | [|- let _ := 1 in _] => intros _; pcofix1 CIH using lem with nr
  | [|- let _ := 2 in _] => intros _; pcofix2 CIH using lem with nr
  | [|- let _ := 3 in _] => intros _; pcofix3 CIH using lem with nr
  | [|- let _ := 4 in _] => intros _; pcofix4 CIH using lem with nr
  | [|- let _ := 5 in _] => intros _; pcofix5 CIH using lem with nr
  | [|- let _ := 6 in _] => intros _; pcofix6 CIH using lem with nr
  | [|- let _ := 7 in _] => intros _; pcofix7 CIH using lem with nr
  | [|- let _ := 8 in _] => intros _; pcofix8 CIH using lem with nr
  end.

Tactic Notation "pcofix" ident(CIH) "using" constr(lem) := 
  pcofix CIH using lem with r.

