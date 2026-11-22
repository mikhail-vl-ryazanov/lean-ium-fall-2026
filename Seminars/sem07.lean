/-!
# Seminar 7
Axioms and computation. Quotients.
-/


/- Propositional extensionality -/

#check_failure (rfl : True = (True ∧ True))

example : True ↔ (True ∧ True) :=
  ⟨λ _ ↦ ⟨trivial, trivial⟩, λ _ ↦ trivial⟩

#print propext

theorem thm₁ {P : Prop → Prop} (h : a ↔ b) : P a ↔ P b := by
  replace h := propext h
  rw [h]

#print axioms thm₁
#print thm₁

theorem thm₂ {P : Prop → Prop} (h : a ↔ b) : P a ↔ P b := by
  rw [h]

#print axioms thm₂
#print thm₂


/- Functional extensionality -/

def f  (n : Nat) := n
def g  (n : Nat) := 0 + n
def g' (n : Nat) := n + 0

#check_failure (rfl : f = g)
#check (rfl : f = g')

theorem f_eq_g_ext (n : Nat) : f n = g n := by
  induction n <;> simp [f, g]

#check funext

theorem f_eq_g : f = g :=
  funext f_eq_g_ext

#print axioms f_eq_g

theorem f_eq_g' : f = g := by
  funext
  apply f_eq_g_ext

-- The type of all subsets of a type A
def Set (α : Type) : Type := α → Prop
def mem (a : α) (x : Set α) : Prop := x a
infix:50 (priority := high) "∈" => mem

theorem set_ext (h : ∀ a : α, a ∈ x ↔ a ∈ y) : x = y :=
  funext (λ a ↦ propext (h a))


/- Quotients -/

#print Quot

def mod7Rel (x y : Nat) : Prop := x % 7 = y % 7

#check Quot mod7Rel
#check (Quot.mk mod7Rel 4)

#print Quot.ind
#print Quot.lift

def decide_mod7Rel (x : Nat) : Bool := x % 7 = 0

theorem decide_mod7Rel_respects (a b : Nat) (h : mod7Rel a b) : decide_mod7Rel a = decide_mod7Rel b := by
  simp only [mod7Rel, decide_mod7Rel] at *
  rw [h]

#check (Quot.lift decide_mod7Rel decide_mod7Rel_respects)

example (a : Nat) :
  Quot.lift decide_mod7Rel decide_mod7Rel_respects (Quot.mk mod7Rel a) =
  decide_mod7Rel a :=
  rfl

#check (rfl : mod7Rel 4 11)
#check_failure (rfl : Quot.mk mod7Rel 4 = Quot.mk mod7Rel 11)

#print Quot.sound

theorem eq_4_11_mod7 : Quot.mk mod7Rel 4 = Quot.mk mod7Rel 11 := by
  apply Quot.sound
  rfl

#print axioms eq_4_11_mod7
#print funext

#print Setoid

instance NatMod7 : Setoid Nat where
  r := mod7Rel
  iseqv := {
    refl := by intro; rfl
    symm := by simp only [mod7Rel]; intro x y h; symm; apply h
    trans := by simp only [mod7Rel]; intro x y z h₁ h₂; apply Eq.trans h₁ h₂
  }

#check (rfl : 4 ≈ 11)

#print Quotient
#check Quotient.mk NatMod7 4


/- Choice -/

#print Nonempty

example (α : Type) : Nonempty α ↔ ∃ _ : α, True :=
  ⟨λ ⟨x⟩ ↦ ⟨x, trivial⟩, λ ⟨x, _⟩ ↦ ⟨x⟩⟩

#print Classical.choice

noncomputable def indefiniteDescription
  {p : α → Prop} (h : ∃ x : α, p x) : {x : α // p x} :=
  Classical.choice (let ⟨x, px⟩ := h; ⟨⟨x, px⟩⟩)

#print axioms indefiniteDescription

noncomputable def choose {p : α → Prop} (h : ∃ x, p x) : α :=
  (indefiniteDescription h).val

theorem choose_spec {p : α → Prop} (h : ∃ x, p x) : p (choose h) :=
  (indefiniteDescription h).property


/- Diaconescu's theorem -/

theorem em (p : Prop) : p ∨ ¬ p :=
  let U (x : Prop) := (x =  True) ∨ p
  let V (x : Prop) := (x = False) ∨ p
  have exU : ∃ x : Prop, U x := ⟨True, Or.inl rfl⟩
  have exV : ∃ x : Prop, V x := ⟨False, Or.inl rfl⟩
  let u : Prop := choose exU
  let v : Prop := choose exV
  have u_spec : U u := choose_spec exU
  have v_spec : V v := choose_spec exV
  have not_uv_or_p : u ≠ v ∨ p :=
    sorry
  have p_to_uv : p → u = v := by
    sorry
  sorry

#print axioms em
#check Classical.em
#print Classical.em
#print axioms Classical.em

theorem propComplete (p : Prop) : p = True ∨ p = False :=
  match em p with
  | .inl hp =>
    Or.inl (propext (Iff.intro (λ _ ↦ True.intro) (λ _ ↦ hp)))
  | .inr hn =>
    Or.inr (propext (Iff.intro hn False.elim))


/- Decidable -/

#print Decidable
#print Decidable.em

example : 2 + 2 ≠ 5 := by decide

#print DecidableEq

example (n m : Nat) : n = m ∨ n ≠ m := by apply Decidable.em

#print ite

def foo (n m : Nat) : Nat :=
  if n = m then 0 else n + m


/- Native evaluation -/

-- set_option maxRecDepth 5000

theorem big_list_sum : (List.range 1_001).sum = 500_500 := by
  -- decide
  decide +native

#print axioms big_list_sum
#print big_list_sum._native.decide.ax_1_1


/- sorry -/

#check sorryAx

theorem bad : False := sorry

#print axioms bad


/- Summary

Kernel primitive type constructions:
- Universes: Sort u : Sort (u + 1)
- Dependent functions: (x : α) → β x
- Inductive types and families
- Quotient types: Quot r

Import kernel principles:
- Non-cumulativity of Sorts
- Definitional proof irrelevance
- Impredicativity of Prop
- Restricted elimination from Prop

Standrad library logical axioms are:
- propext {a b : Prop} : (a ↔ b) → a = b
- Quot.sound.{u} {α : Sort u} {r : α → α → Prop} {a b : α} :
    r a b → Quot.mk r a = Quot.mk r b
- Classical.choice.{u} {α : Sort u} : Nonempty α → α

Derived principles:
- funext.{u, v} {α : Sort u} {β : α → Sort v}
    {f g : (x : α) → β x} (h : ∀ (x : α), f x = g x) : f = g
  follows from Quot.sound
- Classical.em (p : Prop) : p ∨ ¬p
  follows from propext, Quot.sound and Classical.choice

Additional axioms:
- sorryAx.{u} (α : Sort u) (synthetic : Bool) : α
- Native evaluation axioms
-/


/-!
# Exercises
-/

section hw
  noncomputable example {f : α → β} (hf : Function.Surjective f) :
      {g : β → α // Function.RightInverse g f} := by
  -- Определение сюръективности: для каждого y есть х, такой что f x = y
  -- hf : ∀ y : β, ∃ x : α, f x = y

  -- Используем классическую аксиому выбора, чтобы задать функцию g
    let g := fun y => Classical.choose (hf y)

  -- Помещаем g в зависимую пару (Subtype) вместе с доказательством его свойства
    refine ⟨g, ?_⟩

  -- Теперь нужно доказать, что g является правым обратным для f, то есть: ∀ y, f (g y) = y
    intro y
    dsimp [g]
  -- Classical.choose_spec извлекает свойство выбранного элемента
    exact Classical.choose_spec (hf y)

  def choice_from_surjective_right_inverse {α : Type}
      (h : ∀ {α β : Type}  {f : α → β}, Function.Surjective f →
          {g : β → α // Function.RightInverse g f}) :
      Nonempty α → α := by
    intro h_nonempty
    -- Строим постоянную функцию из α в единичный тип PUnit
    let f : α → PUnit := fun _ => PUnit.unit

    -- Доказываем, что f суръективна, так как в PUnit всего один элемент
    have f_surj : Function.Surjective f := by
      intro x
      cases x
      -- Нам нужен хотя бы один элемент из α, берем его из h_nonempty
      exact h_nonempty.elim (fun a => ⟨a, rfl⟩)

    -- Применяем гипотезу h к нашей функции f
    let ⟨g, _⟩ := h f_surj

    -- g имеет тип PUnit → α. Вызываем её на единственном элементе PUnit.unit
    exact g PUnit.unit

  /--
  info: 'choice_from_surjective_right_inverse' does not depend on any axioms
  -/
  #guard_msgs in
  #print axioms choice_from_surjective_right_inverse

/--
Есть список: [true, false, true, true].
1. Мы можем представить его как u ++ false :: true :: v, где:
	• u = [true]
	• v = [true]
2. Правило cancel позволяет убрать false :: true из середины.
3. Результатом шага (u ++ v) будет список: [true, true].
Таким образом, утверждение step [true, false, true, true] [true, true] будет истинным.
-/
  inductive step : List Bool → List Bool → Prop where
  | cancel (u v : List Bool) : step (u ++ false :: true :: v) (u ++ v)

#check step ([true] ++ false :: true :: [true]) ([true] ++ [true])

  def B : Type := Quot step

  -- Equivalence class of empty list is 1
  instance : OfNat B 1 where
    ofNat := Quot.mk step []

  -- Lift list contactenation to B
-- Вспомогательные леммы: конкатенация уважает отношение step
theorem step_append_left (w : List Bool) {x y : List Bool} (h : step x y) :
    step (w ++ x) (w ++ y) := by
  cases h with
  | cancel u v =>
    simpa [List.append_assoc] using step.cancel (w ++ u) v

theorem step_append_right {x y : List Bool} (h : step x y) (w : List Bool) :
    step (x ++ w) (y ++ w) := by
  cases h with
  | cancel u v =>
    simpa [List.append_assoc] using step.cancel u (v ++ w)

-- Поднятие конкатенации списков на B
-- Объявляем экземпляр класса типов Mul (оператор умножения *) для типа B
instance : Mul B where
  -- Определяем функцию умножения mul : B → B → B.
  -- Внешний Quot.lift снимает фактор-множество с первого аргумента (превращая List Bool → (B → B) в B → (B → B))
  mul := Quot.lift
    -- 1-й аргумент внешнего Quot.lift: функция, которая по конкретному первому списку l₁ строит функцию умножения на него (типа B → B).
    -- Внутренний Quot.lift снимает фактор-множество уже со второго аргумента
    (fun l₁ => Quot.lift
      -- 1-й аргумент внутреннего Quot.lift: сама операция на обычных списках — склеиваем l₁ и l₂ и упаковываем обратно в класс эквивалентности B
      (fun l₂ => Quot.mk step (l₁ ++ l₂))
      -- 2-й аргумент внутреннего Quot.lift: доказательство корректности по второму аргументу.
      -- Если список b₁ переходит в b₂ за один шаг (h : step b₁ b₂), то классы для (l₁ ++ b₁) и (l₁ ++ b₂) должны быть равны.
      -- step_append_left доказывает шаг, а Quot.sound превращает этот шаг в равенство (=) в типе B
      (fun _ _ h => Quot.sound (step_append_left l₁ h)))
    -- 2-й аргумент внешнего Quot.lift: доказательство корректности по первому аргументу.
    -- Если список a₁ переходит в a₂ (h : step a₁ a₂), то функции «умножить на a₁ слева» и «умножить на a₂ слева» должны быть равны.
    -- Входим в режим тактик (by), чтобы Lean сам вывел сложные типы
    (fun _ _ h => by
      -- Тактика функциональной экстенсиональности: чтобы доказать равенство двух функций (f = g),
      -- достаточно взять произвольный входной элемент q : B и доказать равенство их результатов (f q = g q)
      funext q
      -- Тактика индукции по фактор-множеству: заменяем абстрактный элемент q : B на его конкретного представителя Quot.mk step l₂
      induction q using Quot.ind with
      -- Разбираем единственный случай представителя l₂ : List Bool.
      -- Теперь цель упростилась до: Quot.mk step (a₁ ++ l₂) = Quot.mk step (a₂ ++ l₂).
      -- Закрываем цель: step_append_right доказывает переход по step, а Quot.sound превращает его в равенство
      | _ l₂ => exact Quot.sound (step_append_right h l₂))


example (x y z : B) : x * y * z = x * (y * z) := by
  -- Применяем принцип индукции Quot.ind к первому элементу x.
  -- Тактика заменяет абстрактный элемент x : B на класс эквивалентности некоторого списка
  induction x using Quot.ind with
  -- Разбираем единственный случай (конструктор Quot.mk) и даём внутреннему списку имя `a` (a : List Bool).
  -- Теперь x заменился на `Quot.mk step a`.
  -- Цель: Quot.mk step a * y * z = Quot.mk step a * (y * z)
  | _ a =>
    -- Применяем индукцию Quot.ind ко второму элементу y
    induction y using Quot.ind with
    -- Даём списку-представителю для y имя `b` (b : List Bool).
    -- Цель: Quot.mk step a * Quot.mk step b * z = Quot.mk step a * (Quot.mk step b * z)
    | _ b =>
      -- Применяем индукцию Quot.ind к третьему элементу z
      induction z using Quot.ind with
      -- Даём списку-представителю для z имя `c` (c : List Bool).
      -- Цель: Quot.mk step a * Quot.mk step b * Quot.mk step c = Quot.mk step a * (Quot.mk step b * Quot.mk step c)
      | _ c =>
        -- Тактика `change` заменяет текущую цель на выражение, которое равно ей по определению (definitionally equal).
        -- Поскольку наше умножение (*) определено через Quot.lift как конкатенация списков (++),
        -- Lean сам раскрывает умножение классов в склейку обычных списков a, b и c
        change Quot.mk step ((a ++ b) ++ c) = Quot.mk step (a ++ (b ++ c))
        -- Тактика `rw` (rewrite) применяет стандартную теорему ассоциативности конкатенации списков `List.append_assoc`
        -- к левой части равенства, превращая `(a ++ b) ++ c` в `a ++ (b ++ c)`.
        -- После этого левая и правая части становятся идентичными, и Lean автоматически закрывает цель
        rw [List.append_assoc]


example (x : B) : x * 1 = x := by
  -- Применяем индукцию по фактор-множеству Quot.ind к элементу x
  induction x using Quot.ind with
  -- Распаковываем единственный случай: x = Quot.mk step a, где a : List Bool.
  -- Цель становится: Quot.mk step a * 1 = Quot.mk step a
  | _ a =>
    -- По определению 1 — это `Quot.mk step []`, а умножение (*) — это конкатенация (++).
    -- С помощью `change` раскрываем левую часть в склейку списка `a` и пустого списка `[]`
    change Quot.mk step (a ++ []) = Quot.mk step a
    -- Применяем стандартную лемму `List.append_nil : a ++ [] = a`.
    -- После переписывания обе части равенства становятся одинаковыми, и цель закрывается
    rw [List.append_nil]


example (x : B) : 1 * x = x := by
  -- Заменяем абстрактный элемент x : B на класс конкретного списка a
  induction x using Quot.ind with
  | _ a =>
    -- Раскрываем определение единицы (1 = Quot.mk step []) и умножения (*)
    change Quot.mk step ([] ++ a) = Quot.mk step a
    -- Применяем лемму `List.nil_append : [] ++ a = a`
    rw [List.nil_append]



  def L : B := Quot.mk step [false]
  def R : B := Quot.mk step [true]

  example : L * R = 1 := by
    -- По определению:
    -- L * R  — это Quot.mk step ([false] ++ [true]), то есть Quot.mk step [false, true]
    -- 1      — это Quot.mk step []
    -- Приводим цель к виду, точно совпадающему с шаблоном конструктора `step.cancel [] []`
    change Quot.mk step ([] ++ false :: true :: []) = Quot.mk step ([] ++ [])
    -- `step.cancel [] []` доказывает, что список [false, true] переходит в [] за один шаг.
    -- `Quot.sound` превращает этот шаг в равенство классов в типе B
    exact Quot.sound (step.cancel [] [])

  example : R * L ≠ 1 := by
    sorry

  instance : Pow B Nat where
    pow :=
      let rec pow' b
        | 0     => 1
        | n + 1 => (pow' b n) * b
      pow'

  example (x : B) : ∃ m n : Nat, x = R ^ m * L ^ n := by
    sorry

  example (m n m' n' : Nat) :
      R ^ m * L ^ n = R ^ m' * L ^ n' →
      m = m' ∧ n = n' := by
    sorry
end hw
