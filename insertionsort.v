Require Import Arith List Lia.

(** § DEFINITIONS FOR THE CORRECTNESS OF THE ALGORITHM *)

(* insert element in sorted list of naturals *)
Fixpoint insert (x:nat) (l:list nat) : (list nat) :=
match l with
| nil   => x::nil
| h::tl => if x <=? h then x::l else h::(insert x tl)
end.

(* sort a list of naturals *)
Fixpoint insertion_sort (l:list nat) : (list nat) :=
match l with
| nil   => nil
| h::tl => insert h (insertion_sort tl)
end.

(* predicate whether list of naturals is sorted *)
Inductive sorted : (list nat) -> Prop :=
| sorted_nil : sorted nil
| sorted_one : forall x, sorted (x::nil)
| sorted_all : forall x y l, x <= y -> sorted (y::l) -> sorted (x::y::l).

(* find number of occurrences of given natural on list *)
Fixpoint num_occ (x:nat) (l:list nat) : nat :=
match l with
| nil   => 0
| h::tl => if x =? h then S (num_occ x tl) else (num_occ x tl)
end.

(* whether l1 is a permutation of l2 *)
Definition perm (l1 l2:list nat) : Prop :=
forall n:nat, num_occ n l1 = num_occ n l2.


(** § DEFINITIONS FOR THE ASYMPTOTIC ANALYSIS *)

(* compute time cost of the `insert` algorithm *)
Fixpoint T_insert (x:nat) (l:list nat) : nat :=
match l with
| nil   => 0
| h::tl => if x <=? h then 1 else S (T_insert x tl)
end.

(* compute time cost of the `insertion_sort` algorithm *)
Fixpoint T_sort (l:list nat) : nat :=
match l with
| nil   => 0
| h::tl => (T_insert h (insertion_sort tl)) + (T_sort tl)
end.

(* compute worst case time cost of the `insert` algorithm *)
Fixpoint T_insert_w (n:nat) : nat :=
match n with
| 0   => 0
| S m => S (T_insert_w m)
end.

(* compute worst case time cost of the `insertion_sort` algorithm *)
Fixpoint T_sort_w (n:nat) : nat :=
match n with
| 0   => 0
| S m => (T_insert_w m) + (T_sort_w m)
end.

(* big-O notation *)
Definition big_o (g:nat->nat) (f:nat->nat) : Prop :=
exists (c n0:nat), c > 0
                /\ n0 > 0
                /\ forall (n:nat), n >= n0 -> 0 <= (f n) <= (c * (g n)).

(* special growths *)
Definition linear_growth    := big_o (fun (n:nat) => n).
Definition quadratic_growth := big_o (fun (n:nat) => n * n).


(** § LEMMAS FOR THE CORRECTNESS OF THE ALGORITHM *)

(* the inserting algorithm preserves sorting *)
Lemma insert_preserves_sorting: forall l x, sorted l -> sorted (insert x l).
Proof.
	intros l x H.
	induction H as [ | a | a b l Hhead Htail IHsorted]; simpl.
	- apply sorted_one.
	- case_eq (x <=? a); intros H; apply sorted_all.
		+ apply Nat.leb_le in H. assumption.
		+ apply sorted_one.
		+ apply Nat.leb_gt in H. apply Nat.lt_le_incl in H. assumption.
		+ apply sorted_one.
	- case_eq (x <=? a); intros H.
		+ apply Nat.leb_le in H.
		  apply sorted_all; try apply sorted_all; assumption.
		+ apply Nat.leb_gt in H.
		  apply Nat.lt_le_incl in H.
		  simpl insert in IHsorted.
		  case_eq (x <=? b); intros H2; rewrite H2 in IHsorted; apply sorted_all; assumption.
Qed.

(* insertion sort sorts a list *)
Lemma insertion_sort_sorts: forall l, sorted (insertion_sort l).
Proof.
	intros l.
	induction l; simpl.
	- apply sorted_nil.
	- apply insert_preserves_sorting.
	  assumption.
Qed.

(* inserting a different element does not change the count *)
Lemma num_occ_insert_diff: forall l n a, n =? a = false -> num_occ n (insert a l) = (num_occ n l).
Proof.
	intros l n a Hdiff.
	induction l as [ | h tl IHl]; simpl.
	- rewrite Hdiff. reflexivity.
	- case_eq (a <=? h); intros Hle; case_eq (n =? h); intros Heq; simpl.
		+ rewrite Hdiff. rewrite Heq. reflexivity.
		+ rewrite Hdiff. rewrite Heq. reflexivity.
		+ rewrite Heq. rewrite IHl. reflexivity.
		+ rewrite Heq. rewrite IHl. reflexivity.
Qed.

(* inserting an equal element changes the count *)
Lemma num_occ_insert_same: forall l n, num_occ n (insert n l) = S (num_occ n l).
Proof.
	intros l n.
	induction l as [ | h tl IHl]; simpl.
	- rewrite Nat.eqb_refl. reflexivity.
	- case_eq (n =? h); intros Heq.
		+ apply Nat.eqb_eq in Heq as Hle.
		  apply Nat.eq_le_incl in Hle.
		  apply leb_correct in Hle.
		  rewrite Hle.
		  simpl.
		  rewrite Heq.
		  rewrite Nat.eqb_refl.
		  reflexivity.
		+ case_eq (n <=? h); intros Hle; simpl.
			* rewrite Nat.eqb_refl.
			  rewrite Heq.
			  reflexivity.
			* rewrite Heq.
			  rewrite IHl.
			  reflexivity.
Qed.

(* insertion sort permutes a list *)
Lemma insertion_sort_perm: forall l, perm l (insertion_sort l).
Proof.
	intros l.
	induction l; simpl; unfold perm.
	- reflexivity.
	- intros n. simpl.
	  case_eq (n =? a); intros Heq; rewrite IHl.
		+ rewrite <- num_occ_insert_same.
		  rewrite Nat.eqb_eq in Heq.
		  rewrite Heq.
		  reflexivity.
		+ rewrite num_occ_insert_diff; auto.
Qed.


(** § LEMMAS FOR THE ASYMPTOTIC ANALYSIS *)

Lemma insert_increments_length: forall l x, length (insert x l) = S (length l).
Proof.
	intros l x.
	induction l as [ | h tl IHl]; simpl.
	- reflexivity.
	- case_eq (x <=? h); intros Hle; simpl.
		+ reflexivity.
		+ rewrite IHl. reflexivity.
Qed.

Lemma insert_sort_length: forall l, length (insertion_sort l) = length l.
Proof.
	intros l.
	induction l as [ | h tl IHl]; simpl.
	- reflexivity.
	- rewrite insert_increments_length.
	  rewrite IHl.
	  reflexivity.
Qed.

(* solve T_insert_w recurrence with a generating function *)
Lemma T_insert_w_generating: forall n, T_insert_w n = n.
Proof.
	induction n as [| n IHn]; simpl; auto.
Qed.

(* solve T_sort_w recurrence with a generating function *)
Lemma T_sort_w_generating: forall n, T_sort_w n = (n * n - n) / 2.
Proof.
	induction n as [| n IHn].
	- simpl. reflexivity.
	- simpl T_sort_w.
	  rewrite T_insert_w_generating.
	  rewrite IHn. clear IHn.
	  cut (forall m, S m * S m = S (m + m + m * m)); try lia.
	  intros Haux. rewrite Haux. clear Haux.
	  cut (forall m, S (m + m + m * m) - S m = m + m + m * m - m); try lia.
	  intros Haux. rewrite Haux. clear Haux.
	  rewrite <- Nat.div_add_l; try auto.
	  cut (forall m, m + m = m * 2); try lia.
	  intros Haux. rewrite Haux. clear Haux.
	  rewrite Nat.add_sub_assoc; try lia.
	  induction n; try lia.
Qed.


(** § THEOREMS FOR THE CORRECTNESS OF THE ALGORITHM *)

(* the insertion sort algorithm is correct *)
Theorem insertion_sort_correct: forall l, let l' := (insertion_sort l) in sorted l' /\ perm l l'.
Proof.
	intros l l'.
	split.
	- apply insertion_sort_sorts.
	- apply insertion_sort_perm.
Qed.


(** § THEOREMS FOR THE ASYMPTOTIC ANALYSIS *)

(* `T_insert_w` is indeed the worst case cost *)
Theorem T_insert_w_check: forall l x, (T_insert x l) <= (T_insert_w (length l)).
Proof.
	intros l x.
	induction l as [ | h tl IHl]; simpl.
	- trivial.
	- case_eq (x <=? h); intros Hle.
		+ lia.
		+ apply le_n_S.
		  assumption.
Qed.

(* `T_sort_w` is indeed the worst case cost *)
Theorem T_sort_w_check: forall l, (T_sort l) <= (T_sort_w (length l)).
Proof.
	intros l.
	induction l as [ | h tl IHl]; simpl.
	- trivial.
	- apply plus_le_compat.
		+ apply le_trans with (T_insert_w (length (insertion_sort tl))).
		  apply T_insert_w_check.
		  rewrite insert_sort_length.
		  reflexivity.
		+ assumption.
Qed.

(* asymptotic analysis of insert *)
Theorem T_insert_w_linear: linear_growth T_insert_w.
Proof.
	unfold linear_growth.
	unfold big_o.
	exists 1, 1.
	split; try split; try auto.
	intros n H.
	rewrite Nat.mul_1_l.
	rewrite T_insert_w_generating.
	split; try apply Nat.le_0_l; auto.
Qed.

(* asymptotic analysis of insertion sort *)
Theorem T_sort_w_quadratic: quadratic_growth T_sort_w.
Proof.
	unfold quadratic_growth.
	unfold big_o.
	exists 1, 1.
	split; try split; try auto.
	intros n H.
	rewrite Nat.mul_1_l.
	rewrite T_sort_w_generating.
	split; try lia.
	rewrite Nat.mul_le_mono_pos_l with (p := 2); try auto.
	rewrite Nat.mul_div_le; try auto.
	lia.
Qed.
