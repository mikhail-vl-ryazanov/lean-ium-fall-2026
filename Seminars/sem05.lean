/-!
# Seminar 5
Propositional equality
-/

/- Mutual inductive types -/

mutual
  inductive Even : Nat → Prop where
  | zero : Even 0
  | succ : (n : Nat) → Odd n → Even (n + 1)

  inductive Odd : Nat → Prop where
  | succ : (n : Nat) → Even n → Odd (n + 1)
end

#check Even.rec
#check Odd.rec

example {n : Nat} (h : Even n) : Even (n + 2) :=
  Even.succ (n + 1) (Odd.succ n h)

/- Equality -/

inductive Eq' {α : Type} (a : α) : α → Prop where
  | refl : Eq' a a

#check Eq'.casesOn
#check Eq'.rec

theorem Eq'.symm {α : Type} {a b : α} (h : Eq' a b) : Eq' b a :=
  Eq'.rec Eq'.refl h

theorem Eq'.trans {α : Type} {a b c : α} (h₁ : Eq' a b) (h₂ : Eq' b c) : Eq' a c :=
  Eq'.rec h₁ h₂

theorem Eq'.congrArg {α β : Type} {a₁ a₂ : α}
    (f : α → β) (h : Eq' a₁ a₂) : Eq' (f a₁) (f a₂) :=
  Eq'.rec refl h

#print Eq
#check rfl
#check (0 = 0)
#check (0 = 1)

example : 2 + 2 = 4 := rfl
example (n : Nat) : n + 0 = n := rfl
theorem foo : (n : Nat) : 0 + n = n :=
  match n with
  | Nat.zero => rfl
  | Nat.succ =>
    have h: 0 + m = m := foo m
    congrArg Nat.succ h


/- rw -/

section rw
  variable (a b c : Nat) (f : Nat → Nat)

  example (h₁ : f 0 = 0) (h₂ : a = 0) : f a = 0 := by
    rw [h₂]
    rw [h₁]

  example (h₁ : f 0 = 0) (h₂ : a = 0) :
      f a = 0 := by
    rw [h₂, h₁]

  example (p : Nat → Prop) (q : Prop) (h : q → a = b)
          (h' : p b) (hq : q) : p a := by
    rw [h hq]; assumption --rwa [h hq]

  example (h₁ : a = b) (h₂ : f a = 0) : f b = 0 := by
    rw [←h₁, h₂]

  example : a + b + c = a + c + b := by
    rw [Nat.add_assoc, Nat.add_comm b, ← Nat.add_assoc]

  example : a + b + c = a + c + b := by
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm b]

  example : a + b + c = a + c + b := by
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm _ b]

  example : a + b + c = a + c + b := by
    rw?

  example (h : a + 0 = 0) : f a = f 0 := by
    rw [Nat.add_zero] at h
    rw [h] at ⊢

  example : (a + b)^2 = a^2 + 2 * a * b + b^2 := by
    sorry

end rw

/- simp -/
/- https://leanprover-community.github.io/extras/simp.html -/

section simp
  variable (a b c : Nat)

  -- try this
  -- set_option trace.Meta.Tactic.simp.rewrite true

  example : (a + 0) * (0 + b * 1 + c * 0) = a * b := by
    simp

  example (p : Nat → Prop) (h : p (a * b))
          : p ((a + 0) * (0 + b * 1 + c * 0)) := by
    simp; assumption -- simpa

  example (p : Nat → Prop) (h : p ((a + 0) * (0 + b * 1 + c * 0)))
          : p (a * b) := by
    simp at h; assumption

  example : (a + 0) * (0 + b * 1 + c * 0) = a * b := by
    simp?

  -- try commenting this
  attribute [local simp] Nat.add_comm
  example : a + b = b + a := by simp

  def f (m n : Nat) : Nat :=
    m + n + m

  example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
    simp [h, ← h', f]

  /- Simp hygiene -/

  -- Do not use simp in the middle of the proof, use simp only
  example (n m : Nat) (h : n + n = m) : n * 2 + 0 = m := by
    simp
    rw [Nat.mul_two]
    exact h

  -- Use args in "simp normal form" is possible
  example (m n : Nat) (h : m ≤ n) :
    n - m + m = n := by
    simp [h]

  end simp


/- calc mode -/
section calc'
  variable (a b c d e : Nat)

  example
      (h1 : a = b)
      (h2 : b = c + 1)
      (h3 : c = d)
      (h4 : e = 1 + d) :
      a = e :=
    calc
      a = b      := by rw [h1]
      _ = c + 1  := by rw [h2]
      _ = d + 1  := by rw [h3]
      _ = 1 + d  := by rw [Nat.add_comm]
      _ = e      := by rw [h4]

  example (h1 : a = b) (h2 : b ≤ c) (h3 : c + 1 < d) : a < d :=
    calc
      a = b     := h1
      _ < b + 1 := Nat.lt_succ_self b
      _ ≤ c + 1 := Nat.succ_le_succ h2
      _ < d     := h3

  example (x y : Int): (x - y) * (x + y) = x^2 - y^2 := by
    sorry

end calc'

/- tactics for inductive types -/

section induction

  -- cases
  example (a : Nat) (h : a ≠ 0) : a.succ.pred = a := by
    cases a
    case zero =>
      apply absurd rfl h
    case succ b =>
      rfl

  theorem Nat.zero_add' (a : Nat) : 0 + a = a := by
    cases a
    case zero => rfl
    case succ a => rw [Nat.add_succ, Nat.zero_add']

  --induction
  theorem Nat.zero_add'' (a : Nat) : 0 + a = a := by
    induction a
    case zero => rfl
    case succ a ih => rw [Nat.add_succ, ih]

  theorem Nat.add_assoc' (a b c : Nat) : a + b + c = a + (b + c) := by
    sorry

  #check Nat.mod.inductionOn
  example (a : Nat) {b : Nat} (h : b > 0) : a % b < b := by
    induction a, b using Nat.mod.inductionOn with
    | ind a b h₁ ih =>
      rw [Nat.mod_eq_sub_mod h₁.2]
      exact ih h
    | base a b h₁ =>
      have : ¬ 0 < b ∨ ¬ b ≤ a := Iff.mp (Decidable.not_and_iff_or_not ..) h₁
      match this with
      | Or.inl h₁ => exact absurd h h₁
      | Or.inr h₁ =>
        have hgt : b > a := Nat.gt_of_not_le h₁
        rwa [← Nat.mod_eq_of_lt hgt] at hgt

  -- injection
  example (a b c: Nat) (h : a.succ.succ = b.succ.succ)
          : a + c = b + c := by
    injection h with h'
    injection h' with h''
    rw [h'']

  example (a b : Nat) (h : a.succ = 0) : b = b + 7 := by
    injection h

  example (a b : Nat) (h : a.succ = 0) : b = b + 7 := by
    contradiction

end induction

/-!
# Exercises
-/
section hw
  -- Define sumTo n k := 1 + ... + n
  def sumTo (n : Nat) : Nat :=
  match n with
  | Nat.zero => 0
  | Nat.succ m => sumTo m + n

  theorem gauss :
      ∀ n : Nat, 2 * sumTo n = n * (n + 1) := by
    intro n
    induction n with
    | zero => rfl
    | succ m hm =>
        have h1 (m : Nat) : 2 * m + 2 * 1 = m + m + 1 + 1 := by rw [Nat.two_mul]
        have h2 (m : Nat) : (m + 1) * 1 = m + 1 := by rw [Nat.mul_one]
        have h3 (m : Nat) : m + m + 1 + 1 = (m + 1) + (m + 1) := by rw [Nat.add_add_add_comm]
        dsimp [sumTo]
        rw [Nat.left_distrib, Nat.left_distrib, ← Nat.add_assoc]
        rw [Nat.left_distrib, Nat.left_distrib, Nat.add_assoc]
        rw [hm]
        rw [Nat.mul_comm]
        rw [h1, h2, h3]
        rw [← Nat.add_assoc]

  theorem exp_growth :
      ∀ k : Nat, ∃ N : Nat, ∀ n : Nat, N ≤ n → n^k ≤ 2^n := by
    sorry





  -- Might be useful:
  #check Nat.mul_mod_right
  #check Nat.mul_mod
  #check Nat.dvd_of_mod_eq_zero
  #check Nat.mod_two_eq_zero_or_one
  #check Nat.strongRecOn

  theorem sqrtTwoStep :
      ∀ a b : Nat, a ^ 2 = 2 * b ^ 2 →
      ∃ c : Nat, a = 2 * c ∧ b ^ 2 = 2 * c ^ 2 := by
    sorry

  theorem sqrtTwoIrrational: ∀ a b : Nat, 0 < b → a^2 ≠ 2 * b^2 := by
    sorry

end hw
