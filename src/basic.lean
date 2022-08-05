/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import data.set.function
import tactic

open set

def row (i : fin 9) : set (fin 9 × fin 9) := { p | p.1 = i }
def col (i : fin 9) : set (fin 9 × fin 9) := { p | p.2 = i }
def box (i j : fin 3) : set (fin 9 × fin 9) := { p | p.1.1 / 3 = i.1 ∧ p.2.1 / 3 = j.1 }

lemma mem_row (i j k : fin 9) : (j, k) ∈ row i ↔ j = i := iff.rfl
lemma mem_col (i j k : fin 9) : (j, k) ∈ col i ↔ k = i := iff.rfl
lemma mem_box (i j : fin 9) (k l : fin 3) : (i, j) ∈ box k l ↔ i.1 / 3 = k.1 ∧ j.1 / 3 = l.1 := iff.rfl

structure sudoku :=
(f : fin 9 × fin 9 → fin 9)
(h_row : ∀ i : fin 9, set.bij_on f (row i) set.univ)
(h_col : ∀ i : fin 9, set.bij_on f (col i) set.univ)
(h_box : ∀ i j : fin 3, set.bij_on f (box i j) set.univ)

namespace sudoku

lemma cell_cases (s : sudoku) (i j : fin 9) :
  s.f (i, j) = 9 ∨ s.f (i, j) = 1 ∨ s.f (i, j) = 2 ∨ s.f (i, j) = 3 ∨ s.f (i, j) = 4 ∨ s.f (i, j) = 5 ∨ s.f (i, j) = 6 ∨ s.f (i, j) = 7 ∨ s.f (i, j) = 8 :=
begin
  cases s.f (i, j) with v hv,
  interval_cases v; tauto
end

lemma row_cases (s : sudoku) (i j : fin 9) :
  s.f (i, 0) = j ∨ s.f (i, 1) = j ∨ s.f (i, 2) = j ∨ s.f (i, 3) = j ∨ s.f (i, 4) = j ∨ s.f (i, 5) = j ∨ s.f (i, 6) = j ∨ s.f (i, 7) = j ∨ s.f (i, 8) = j :=
begin
  obtain ⟨⟨x, ⟨y, hy⟩⟩, ⟨h, h'⟩⟩ : j ∈ s.f '' row i := (s.h_row i).surj_on trivial,
  rw mem_row at h,
  subst h,
  interval_cases y; tauto
end

lemma col_cases (s : sudoku) (i j : fin 9) :
  s.f (0, i) = j ∨ s.f (1, i) = j ∨ s.f (2, i) = j ∨ s.f (3, i) = j ∨ s.f (4, i) = j ∨ s.f (5, i) = j ∨ s.f (6, i) = j ∨ s.f (7, i) = j ∨ s.f (8, i) = j :=
begin
  obtain ⟨⟨⟨x, hx⟩, y⟩, ⟨h, h'⟩⟩ : j ∈ s.f '' col i := (s.h_col i).surj_on trivial,
  rw mem_col at h,
  subst h,
  interval_cases x; tauto
end

lemma box_cases (s : sudoku) (i j : fin 3) (k : fin 9) :
  s.f ((3 * i.1 : ℕ), (3 * j.1 : ℕ)) = k ∨
  s.f ((3 * i.1 : ℕ), (3 * j.1 + 1 : ℕ)) = k ∨
  s.f ((3 * i.1 : ℕ), (3 * j.1 + 2 : ℕ)) = k ∨
  s.f ((3 * i.1 + 1 : ℕ), (3 * j.1 : ℕ)) = k ∨
  s.f ((3 * i.1 + 1 : ℕ), (3 * j.1 + 1 : ℕ)) = k ∨
  s.f ((3 * i.1 + 1 : ℕ), (3 * j.1 + 2 : ℕ)) = k ∨
  s.f ((3 * i.1 + 2 : ℕ), (3 * j.1 : ℕ)) = k ∨
  s.f ((3 * i.1 + 2 : ℕ), (3 * j.1 + 1 : ℕ)) = k ∨
  s.f ((3 * i.1 + 2 : ℕ), (3 * j.1 + 2 : ℕ)) = k :=
begin
  obtain ⟨⟨x, y⟩, ⟨h, h'⟩⟩ : k ∈ s.f '' box i j := (s.h_box i j).surj_on trivial,
  rw mem_box at h,
  cases h with h₀ h₁,
  have hx : x.1 = 3 * i.val + (x.1 % 3),
  { rw [add_comm, ←h₀, nat.mod_add_div] },
  have hy : y.1 = 3 * j.val + (y.1 % 3),
  { rw [add_comm, ←h₁, nat.mod_add_div] },
  have := nat.mod_lt x.val (show 3 > 0, from dec_trivial),
  have := nat.mod_lt y.val (show 3 > 0, from dec_trivial),
  interval_cases (x.val % 3);
  rw h at hx;
  try { rw add_zero at hx };
  rw ←hx;
  interval_cases (y.val % 3);
  rw h_1 at hy;
  try { rw add_zero at hy };
  simp only [←hy, fin.coe_val_eq_self];
  tauto
end

lemma cell_conflict (s : sudoku) {i j k l : fin 9} (h₀ : s.f (i, j) = k) (h₁ : s.f (i, j) = l)
  (h₂ : k ≠ l) : false :=
begin
  apply h₂,
  rw [←h₀, ←h₁]
end

lemma row_conflict (s : sudoku) {i j k l : fin 9} (h₀ : s.f (i, j) = l) (h₁ : s.f (i, k) = l)
  (h₂ : j ≠ k) : false :=
begin
  apply h₂,
  suffices : (i, j) = (i, k),
  { cases this, refl },
  refine (s.h_row i).inj_on _ _ (h₀.trans h₁.symm);
  rw mem_row
end

lemma col_conflict (s : sudoku) {i j k l : fin 9} (h₀ : s.f (i, k) = l) (h₁ : s.f (j, k) = l)
  (h₂ : i ≠ j) : false :=
begin
  apply h₂,
  suffices : (i, k) = (j, k),
  { cases this, refl },
  refine (s.h_col k).inj_on _ _ (h₀.trans h₁.symm);
  rw mem_col
end

lemma bloop {i : ℕ} (hi : i < 9) : i / 3 < 3 :=
by interval_cases i; exact dec_trivial

lemma box_conflict (s : sudoku) {i j k l m : fin 9} (h₀ : s.f (i, j) = m) (h₁ : s.f (k, l) = m)
  (h₂ : i.1 / 3 = k.1 / 3) (h₃ : j.1 / 3 = l.1 / 3) (h₄ : i ≠ k ∨ j ≠ l) : false :=
begin
  contrapose h₄,
  push_neg,
  clear h₄,
  suffices : (i, j) = (k, l),
  { cases this, exact ⟨rfl, rfl⟩ },
  refine (s.h_box (i.1 / 3 : ℕ) (j.1 / 3 : ℕ)).inj_on _ _ (h₀.trans h₁.symm),
  { rw mem_box,
    split,
    { rw fin.coe_val_of_lt,
      exact bloop i.2 },
    { rw fin.coe_val_of_lt,
      exact bloop j.2 } },
  { rw mem_box,
    split,
    { rw fin.coe_val_of_lt,
      { exact h₂.symm },
      { exact bloop i.2 } },
    { rw fin.coe_val_of_lt,
      { exact h₃.symm },
      { exact bloop j.2 } } }
end

/-- Outer pencil marks capture the fact that a certain number appears in one of two places. -/
def snyder (s : sudoku) (i j k l m : fin 9) : Prop :=
s.f (i, j) = m ∨ s.f (k, l) = m

def snyder₃ (s : sudoku) (i j k l m n o : fin 9) : Prop :=
s.f (i, j) = o ∨ s.f (k, l) = o ∨ s.f (m, n) = o

/-- Inner pencil marks capture the fact that a certain cell contains one of two numbers. -/
def double (s : sudoku) (i j k l : fin 9) : Prop :=
s.f (i, j) = k ∨ s.f (i, j) = l

/-- Inner pencil marks capture the fact that a certain cell contains one of three numbers. -/
def triple (s : sudoku) (i j k l m : fin 9) : Prop :=
s.f (i, j) = k ∨ s.f (i, j) = l ∨ s.f (i, j) = m

lemma triple_perm₁ {s : sudoku} {i j k l m : fin 9} : s.triple i j k l m → s.triple i j l k m :=
by { unfold triple, tauto }

lemma triple_perm₂ {s : sudoku} {i j k l m : fin 9} : s.triple i j k l m → s.triple i j m l k :=
by { unfold triple, tauto }

/-- The first (trivial) piece of sudoku theory: If there are two outer pencil marks relating two
    cells, then we get an inner pencil mark for those two numbers in both cells. -/
lemma double_left_of_snyder {s : sudoku} {i j k l m n : fin 9} (h₀ : snyder s i j k l m)
  (h₁ : snyder s i j k l n) (h₂ : m ≠ n) : double s i j m n :=
by { unfold double, cases h₀; cases h₁; try { tauto }, exact absurd (h₀.symm.trans h₁) h₂ }

/-- The first (trivial) piece of sudoku theory: If there are two outer pencil marks relating two
    cells, then we get an inner pencil mark for those two numbers in both cells. -/
lemma double_right_of_snyder {s : sudoku} {i j k l m n : fin 9} (h₀ : snyder s i j k l m)
  (h₁ : snyder s i j k l n) (h₂ : m ≠ n) : double s k l m n :=
by { unfold double, cases h₀; cases h₁; try { tauto }, exact absurd (h₀.symm.trans h₁) h₂ }

lemma triple_of_double₁ {s : sudoku} {i j k l m : fin 9} : s.double i j k l → s.triple i j m k l :=
by { unfold triple, tidy, tauto }

lemma triple_of_double₂ {s : sudoku} {i j k l m : fin 9} : s.double i j k l → s.triple i j k m l :=
by { unfold triple, tidy, tauto }

lemma triple_of_double₃ {s : sudoku} {i j k l m : fin 9} : s.double i j k l → s.triple i j k l m :=
by { unfold triple, tidy, tauto }

/-- Two cells are in contention if they "see each other", i.e., cannot contain the same number. -/
def contention (s : sudoku) (i j k l : fin 9) : Prop :=
∀ (m : fin 9), s.f (i, j) = m → s.f (k, l) = m → false

lemma row_contention {s : sudoku} {i j k : fin 9} (h : j ≠ k) : s.contention i j i k :=
λ m h₀ h₁, s.row_conflict h₀ h₁ h

lemma col_contention {s : sudoku} {i j k : fin 9} (h : i ≠ j) : s.contention i k j k :=
λ m h₀ h₁, s.col_conflict h₀ h₁ h

lemma box_contention {s : sudoku} {i j k l : fin 9} (h : i.1 / 3 = k.1 / 3)
  (h' : j.1 / 3 = l.1 / 3) (h'' : i ≠ k ∨ j ≠ l) : s.contention i j k l :=
λ m h₀ h₁, s.box_conflict h₀ h₁ h h' h''

lemma snyder₃_of_triple₁ {s : sudoku} {i j k l m n o p q : fin 9}
  (h₀ : s.triple i j o p q) (h₁ : s.triple k l o p q) (h₂ : s.triple m n o p q)
  (h : s.contention i j k l) (h' : s.contention i j m n) (h'' : s.contention k l m n) :
  s.snyder₃ i j k l m n o :=
begin
  unfold snyder₃,
  rcases h₀ with _|_|_,
  { left, exact h₀ },
  { rcases h₁ with _|_|_,
    { right, left, exact h₁ },
    { exfalso, exact h _ h₀ h₁ },
    rcases h₂ with _|_|_,
    { right, right, exact h₂ },
    { exfalso, exact h' _ h₀ h₂ },
    { exfalso, exact h'' _ h₁ h₂ } },
  { rcases h₁ with _|_|_,
    { right, left, exact h₁ },
    swap, { exfalso, exact h _ h₀ h₁ },
    rcases h₂ with _|_|_,
    { right, right, exact h₂ },
    { exfalso, exact h'' _ h₁ h₂ },
    { exfalso, exact h' _ h₀ h₂ } }
end

lemma snyder₃_of_triple₂ {s : sudoku} {i j k l m n o p q : fin 9}
  (h₀ : s.triple i j o p q) (h₁ : s.triple k l o p q) (h₂ : s.triple m n o p q)
  (h : s.contention i j k l) (h' : s.contention i j m n) (h'' : s.contention k l m n) :
  s.snyder₃ i j k l m n p :=
snyder₃_of_triple₁ (triple_perm₁ h₀) (triple_perm₁ h₁) (triple_perm₁ h₂) h h' h''

lemma snyder₃_of_triple₃ {s : sudoku} {i j k l m n o p q : fin 9}
  (h₀ : s.triple i j o p q) (h₁ : s.triple k l o p q) (h₂ : s.triple m n o p q)
  (h : s.contention i j k l) (h' : s.contention i j m n) (h'' : s.contention k l m n) :
  s.snyder₃ i j k l m n q :=
snyder₃_of_triple₁ (triple_perm₂ h₀) (triple_perm₂ h₁) (triple_perm₂ h₂) h h' h''

lemma snyder₃_of_triple_row₁ {s : sudoku} {i j k l m n o : fin 9}
  (hj : s.triple i j m n o) (hk : s.triple i k m n o) (hl : s.triple i l m n o)
  (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) : s.snyder₃ i j i k i l m :=
snyder₃_of_triple₁ hj hk hl (row_contention hjk) (row_contention hjl) (row_contention hkl)

lemma snyder₃_of_triple_row₂ {s : sudoku} {i j k l m n o : fin 9}
  (hj : s.triple i j m n o) (hk : s.triple i k m n o) (hl : s.triple i l m n o)
  (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) : s.snyder₃ i j i k i l n :=
snyder₃_of_triple₂ hj hk hl (row_contention hjk) (row_contention hjl) (row_contention hkl)

lemma snyder₃_of_triple_row₃ {s : sudoku} {i j k l m n o : fin 9}
  (hj : s.triple i j m n o) (hk : s.triple i k m n o) (hl : s.triple i l m n o)
  (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l) : s.snyder₃ i j i k i l o :=
snyder₃_of_triple₃ hj hk hl (row_contention hjk) (row_contention hjl) (row_contention hkl)

lemma snyder₃_of_triple_col₁ {s : sudoku} {i j k l m n o : fin 9}
  (hi : s.triple i j m n o) (hk : s.triple k j m n o) (hl : s.triple l j m n o)
  (hik : i ≠ k) (hkl : k ≠ l) (hil : i ≠ l) : s.snyder₃ i j k j l j m :=
snyder₃_of_triple₁ hi hk hl (col_contention hik) (col_contention hil) (col_contention hkl)

lemma snyder₃_of_triple_col₂ {s : sudoku} {i j k l m n o : fin 9}
  (hi : s.triple i j m n o) (hk : s.triple k j m n o) (hl : s.triple l j m n o)
  (hik : i ≠ k) (hkl : k ≠ l) (hil : i ≠ l) : s.snyder₃ i j k j l j n :=
snyder₃_of_triple₂ hi hk hl (col_contention hik) (col_contention hil) (col_contention hkl)

lemma snyder₃_of_triple_col₃ {s : sudoku} {i j k l m n o : fin 9}
  (hi : s.triple i j m n o) (hk : s.triple k j m n o) (hl : s.triple l j m n o)
  (hik : i ≠ k) (hkl : k ≠ l) (hil : i ≠ l) : s.snyder₃ i j k j l j o :=
snyder₃_of_triple₃ hi hk hl (col_contention hik) (col_contention hil) (col_contention hkl)

/-- X wing -/
lemma X_wing_row {s : sudoku} {i j k l m o : fin 9}
  (hi : s.snyder i j i k o) (hl : s.snyder l j l k o)
  (hil: i ≠ l) (hmi : m ≠ i) (hml: m ≠ l) : s.f (m, j) ≠ o :=
begin
  intro ifz, cases hi,
  apply col_contention hmi, exact ifz, exact hi,
  cases hl, apply col_contention hml, exact ifz, exact hl,
  apply col_contention hil, exact hi, exact hl,
end

lemma X_wing_col {s : sudoku} {i j k l m o : fin 9}
  (hj : s.snyder i j k j o) (hl : s.snyder i l k l o)
  (hjl: j ≠ l) (hmj : m ≠ j) (hml: m ≠ l) : s.f (i, m) ≠ o :=
begin
  intro ifz, cases hj,
  apply row_contention hmj, exact ifz, exact hj,
  cases hl, apply row_contention hml, exact ifz, exact hl,
  apply row_contention hjl, exact hj, exact hl,
end

/-- XY wing -/
lemma XY_wing {s : sudoku} {i j k l m n o p x y z: fin 9}
  (h₀ : s.double i j x y) (h₁ : s.double k l x z) (h₂ : s.double m n y z)
  (h : s.contention i j k l) (h' : s.contention i j m n)
  (h'' : s.contention o p k l) (h''' : s.contention o p m n) : s.f (o, p) ≠ z :=
begin
  intro ifz, cases h₀,
  cases h₁, apply h x, exact h₀, exact h₁, apply h'' z, exact ifz, exact h₁,
  cases h₂, apply h' y, exact h₀, exact h₂, apply h''' z, exact ifz, exact h₂,
end

/-- XYZ wing -/
lemma XYZ_wing {s : sudoku} {i j k l m n o p x y z: fin 9}
  (h₀ : s.triple i j x y z) (h₁ : s.double k l x z) (h₂ : s.double m n y z)
  (h : s.contention i j k l) (h' : s.contention i j m n)
  (h'' : s.contention o p k l) (h''' : s.contention o p m n)
  (h'''' : s.contention o p i j) : s.f (o, p) ≠ z :=
begin
  intro ifz, cases h₀,
  cases h₁, apply h x, exact h₀, exact h₁, apply h'' z, exact ifz, exact h₁,
  cases h₂, apply h' y, cases h₀, exact h₀,
  exfalso, apply h'''' z, exact ifz, exact h₀, exact h₂,
  cases h₀, apply h''' z, exact ifz, exact h₂, apply h''' z, exact ifz, exact h₂,
end

/-- sws_chains means strong-weak-strong chains -/
lemma sws_chains {s : sudoku} {i j k l m n o p x: fin 9}
  (h₀ : s.snyder i j k l x) (h₁ : s.contention k l m n)
  (h₂ : s.snyder m n o p x): s.snyder i j o p x :=
begin
  cases h₀, cases h₂, left, exact h₀, right, exact h₂,
  right, cases h₂, exfalso, apply h₁ x, exact h₀, exact h₂, exact h₂,
end

/-- wsw_chains means weak-strong-weak chains -/
lemma wsw_chains {s : sudoku} {i j k l m n x: fin 9}
  (h₀ : s.contention i j k l) (h₁ : s.snyder k l m n x)
  (h₂ : s.contention m n i j): s.f(i, j) ≠ x :=
begin
  intro ifx, cases h₁, apply h₀ x, exact ifx, exact h₁,
  apply h₂ x, exact h₁, exact ifx,
end

/-- Turbot fish -/
lemma Turbot_fish {s : sudoku} {i j k l m n o p q r x: fin 9}
  (h₀ : s.contention i j k l) (h₁ : s.snyder k l m n x)
  (h₂ : s.contention m n o p) (h₃ : s.snyder o p q r x)
  (h₄ : s.contention q r i j): s.f (i, j) ≠ x :=
  by {apply wsw_chains h₀, exact sws_chains h₁ h₂ h₃, exact h₄,}

end sudoku
