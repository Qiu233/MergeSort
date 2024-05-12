import Mathlib.Data.List.Perm
import Mathlib.Tactic.Linarith

variable {α : Type}

variable [LinearOrder α]

def Merge : List α → List α → List α
  | [], y => y
  | x, [] => x
  | a :: x, b :: y =>
    if a ≤ b
      then a :: Merge x (b :: y)
      else b :: Merge (a :: x) y
termination_by x y => x.length + y.length

def List.split (l : List α) : List α × List α :=
  letI idx := l.length / 2
  l.splitAt idx

lemma split_dec_l {l : List α} : l.length ≥ 2 → l.split.1.length < l.length := by
  intro h
  unfold List.split
  simp
  apply Nat.div_lt_of_lt_mul
  linarith
lemma split_dec_r {l : List α} : l.length ≥ 2 → l.split.2.length < l.length := by
  intro h
  unfold List.split
  simp
  apply Nat.sub_lt
  . linarith only [h]
  . apply Classical.not_not.mp
    intro hn
    simp at hn
    rw [Nat.div_eq_zero_iff (by decide)] at hn
    linarith only [h, hn]

lemma aux_1 {l : List α} : ¬ l.length ≤ 1 ↔ l.length ≥ 2 := by
  apply Iff.intro
  all_goals
    intro h
    linarith only [h]

def MergeSort (list : List α) : List α :=
  if _ : list.length ≤ 1
    then list
    else Merge (MergeSort list.split.1) (MergeSort list.split.2)
termination_by list.length
decreasing_by
  . simp_wf
    rename ¬List.length list ≤ 1 => h
    exact split_dec_l $ aux_1.mp h
  . simp_wf
    rename ¬List.length list ≤ 1 => h
    exact split_dec_r $ aux_1.mp h

inductive Ordered [LinearOrder α] : (List α) → Prop where
  | nil : Ordered []
  | sing (a : α) : Ordered [a]
  | cons
      (a b : α) (tail : List α)
      (h1 : a ≤ b) (h2 : Ordered (b :: tail)) : Ordered (a :: b :: tail)

lemma Ordered.cons' {a b : α} {tail : List α}
    (h1 : a ≤ b) (h2 : Ordered (b :: tail)) : Ordered (a :: b :: tail)
  := Ordered.cons a b tail h1 h2

attribute [simp] Ordered.nil Ordered.sing

lemma Ordered.tail {a : α} {x : List α} : Ordered (a :: x) → Ordered x := by
  intro h
  cases h with
  | sing a' =>
    simp
  | cons a' b' tail' h1 h2 =>
    simp [h2]

theorem Ordered.iff {a : α} {l : List α} : (Ordered (a :: l) ↔ (∀ x ∈ l, a ≤ x) ∧ Ordered l) := by
  apply Iff.intro
  . intro h
    simp [Ordered.tail h]
    intro x hx
    cases h with
    | sing a =>
      simp at hx
    | cons a b tail h1 h2 =>
      simp at hx
      rcases hx with hx | hx
      . simp [hx, h1, h2]
      . trans b
        . exact h1
        . have := (Ordered.iff (l := tail)).mp h2 |>.1
          exact this x hx
  . cases l with
    | nil => simp
    | cons b tail =>
      intro ⟨h, h'⟩
      refine cons' ?_ h'
      apply h
      simp

@[simp]
lemma Merge.nil_x {x : List α} : Merge [] x = x := by
  simp [Merge]
@[simp]
lemma Merge.x_nil {x : List α} : Merge x [] = x := by
  unfold Merge
  cases x <;> simp

lemma Merge.ordered_nil_x {x : List α} : Ordered x → Ordered (Merge [] x) := by
  intro h
  simp [h]

lemma Merge.ordered_x_nil {x : List α} : Ordered x → Ordered (Merge x []) := by
  intro h
  simp [h]

lemma Merge.ordered_sing_sing {a b : α} : Ordered (Merge [a] [b]) := by
  simp [Merge,]
  split
  . case inl h =>
      apply Ordered.cons' h
      simp
  . case inr h =>
      apply Ordered.cons' ?_ (by simp)
      simp at h
      apply le_of_lt h

theorem Merge.Perm {x y : List α} : List.Perm (x ++ y) (Merge x y) := by
  unfold Merge
  cases x with
  | nil => simp
  | cons a tail =>
    cases y with
    | nil => simp
    | cons a' tail' =>
      simp
      split
      . case inl h =>
        apply List.Perm.cons
        apply Merge.Perm
      . case inr h =>
        have : List.Perm (a :: (tail ++ a' :: tail')) (a' :: ((a :: tail) ++ tail')) := by
          simp
          trans a :: a' :: (tail ++ tail')
          . apply List.Perm.cons
            have aux_1 : tail ++ a' :: tail' = (tail ++ [a']) ++ tail' := by simp
            have aux_2 : a' :: (tail ++ tail') = (a' :: tail) ++ tail' := by simp
            rw [aux_1, aux_2]
            apply List.Perm.append
            simp
            simp
          . apply List.Perm.swap
        apply List.Perm.trans this
        apply List.Perm.cons
        apply Merge.Perm

theorem List.Perm.forall {x y : List α} {motive : α → Prop} (h : List.Perm x y) :
    (∀ t ∈ x, motive t) ↔ (∀ t ∈ y, motive t) := by
  apply Iff.intro
  . intro h' t ht
    rw [List.Perm.mem_iff (l₂ := x) h.symm] at ht
    apply h' t ht
  . intro h' t ht
    rw [List.Perm.mem_iff (l₂ := y) h] at ht
    apply h' t ht

theorem Merge.Perm_red {x y : List α} {motive : α → Prop} :
    (∀ t ∈ (x ++ y), motive t) → (∀ t ∈ (Merge x y), motive t) := by
  intro h'
  have perm := Merge.Perm (x := x) (y := y)
  rw [List.Perm.forall perm.symm]
  exact h'

open Ordered in
theorem Merge.ordered {l1 l2 : List α} :
    Ordered l1 → Ordered l2 → Ordered (Merge l1 l2) := by
  intro ha hb
  match ha, hb with
  | nil, hb =>
    apply Merge.ordered_nil_x hb
  | ha, nil =>
    apply Merge.ordered_x_nil ha
  | sing a, sing a' =>
    apply Merge.ordered_sing_sing
  | sing a, cons a' b' tail' h1' h2' =>
    simp [Merge]
    split
    . case inl h =>
        apply cons' h
        apply cons' h1' h2'
    . case inr h =>
      split
      . case inl h' =>
        simp at h
        apply cons' (le_of_lt h)
        apply cons' h' h2'
      . case inr h' =>
        simp at h h'
        apply cons' h1'
        have : Ordered tail' := Ordered.tail h2'
        have : Ordered (Merge [a] tail') := Merge.ordered (Ordered.sing a) this
        rw [Ordered.iff]
        rw [Ordered.iff] at h2'
        simp [this]
        apply Merge.Perm_red
        simp [le_of_lt h']
        exact h2'.1
  | cons a b tail h1 h2, sing a' =>
    simp [Merge]
    split
    . case inl h =>
      split
      . case inl h' =>
        apply cons' h1
        rw [Ordered.iff]
        apply And.intro
        . have perm : List.Perm ([a'] ++ tail) (tail ++ [a']) := by apply List.perm_append_comm
          apply Merge.Perm_red
          rw [List.Perm.forall perm.symm]
          simp [h']
          rw [Ordered.iff] at h2
          exact h2.1
        apply Merge.ordered (Ordered.tail h2)
        simp
      . case inr h' =>
        apply cons' h
        simp at h'
        apply cons' (le_of_lt h') h2
    . case inr h =>
      simp at h
      apply cons' (le_of_lt h)
      apply cons' h1 h2
  | cons a b tail h1 h2, cons a' b' tail' h1' h2' =>
    unfold Merge
    split
    . case inl h =>
        rw [Ordered.iff]
        apply And.intro ?_
        . apply Merge.ordered h2
          apply cons' h1' h2'
        . apply Merge.Perm_red
          intro t ht
          simp at ht
          rcases ht with ht | ht | ht | ht | ht
          . simp [ht, h1]
          . apply le_trans h1
            rw [Ordered.iff] at h2
            apply h2.1 t ht
          . simp [ht, h]
          . rw [ht]
            apply le_trans h h1'
          . apply le_trans h
            apply le_trans h1'
            rw [Ordered.iff] at h2'
            apply h2'.1 t ht
    . case inr h =>
        simp at h
        rw [Ordered.iff]
        apply And.intro ?_
        . apply Merge.ordered (cons' h1 h2) h2'
        . apply Merge.Perm_red
          . intro t ht
            have h' := le_of_lt h
            simp at ht
            rcases ht with ht | ht | ht | ht | ht
            . simp [ht, h']
            . simp [ht, le_trans h' h1]
            . apply le_trans h'
              apply le_trans h1
              rw [Ordered.iff] at h2
              apply h2.1 t ht
            . simp [ht, h1']
            . apply le_trans h1'
              rw [Ordered.iff] at h2'
              apply h2'.1 t ht

theorem MergeSort.ordered {l : List α} :
    Ordered (MergeSort l) := by
  unfold MergeSort
  split
  . case inl h =>
      cases l with
      | nil => simp
      | cons a tail =>
        have : tail = [] := by
          simp [Nat.succ_eq_add_one] at h
          exact List.length_eq_zero.mp h
        simp [this]
  . case inr h =>
      rw [aux_1] at h
      have ordered_l : Ordered (MergeSort (List.split l).1) := MergeSort.ordered
      have ordered_r : Ordered (MergeSort (List.split l).2) := MergeSort.ordered
      apply Merge.ordered ordered_l ordered_r
termination_by l.length
decreasing_by
  . simp_wf
    rename ¬List.length l ≤ 1 => h
    exact split_dec_l $ aux_1.mp h
  . simp_wf
    rename ¬List.length l ≤ 1 => h
    exact split_dec_r $ aux_1.mp h

theorem MergeSort.Perm {l : List α} : List.Perm l (MergeSort l) := by
  unfold MergeSort
  split
  . case inl h => simp
  . case inr h =>
    simp at h
    have perm_l : List.Perm ((List.split l).1) (MergeSort (List.split l).1) := MergeSort.Perm
    have perm_r : List.Perm ((List.split l).2) (MergeSort (List.split l).2) := MergeSort.Perm
    trans (MergeSort (List.split l).1) ++ (MergeSort (List.split l).2)
    . trans (List.split l).1 ++ (List.split l).2
      . unfold List.split
        simp
      . apply List.Perm.append perm_l perm_r
    . apply Merge.Perm
termination_by l.length
decreasing_by
  . simp_wf
    rename ¬List.length l ≤ 1 => h
    exact split_dec_l $ aux_1.mp h
  . simp_wf
    rename ¬List.length l ≤ 1 => h
    exact split_dec_r $ aux_1.mp h
