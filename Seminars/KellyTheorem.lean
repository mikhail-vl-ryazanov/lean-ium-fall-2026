-- Импорт евклидовых пространств со скалярным произведением (для работы с плоскостью ℝ²)
import Mathlib.Analysis.InnerProductSpace.PiL2
-- Импорт тактики linarith для автоматического решения линейных неравенств
import Mathlib.Tactic.Linarith
-- Импорт тактики ring для упрощения алгебраических выражений в кольцах и полях
import Mathlib.Tactic.Ring

-- Открываем пространства имён вещественных чисел и пространств со скалярным произведением
open Real InnerProductSpace

-- 1. Базовые геометрические определения на евклидовой плоскости
-- Определяем точку как элемент двумерного евклидова пространства над ℝ
abbrev Point := EuclideanSpace ℝ (Fin 2)

-- Определяем структуру прямой, заданной опорной точкой и ненулевым направляющим вектором
structure Line where
  -- Опорная точка прямой
  p : Point
  -- Направляющий вектор прямой
  v : Point
  -- Условие, что направляющий вектор не равен нулю
  hv : v ≠ 0

-- Определяем предикат принадлежности точки x прямой l (параметрическое уравнение)
def OnLine (x : Point) (l : Line) : Prop :=
  -- Существует параметр t ∈ ℝ такой, что x = p + t * v
  ∃ t : ℝ, x = l.p + t • l.v

-- Строим прямую, проходящую через две несовпадающие точки x и y
noncomputable def lineThrough (x y : Point) (hxy : x ≠ y) : Line where
  -- Берём точку x в качестве опорной
  p := x
  -- Направляющим вектором берём разность y - x
  v := y - x
  -- Доказываем, что y - x ≠ 0, используя условие x ≠ y
  hv := sub_ne_zero.mpr hxy.symm

-- Расстояние от точки до прямой через ортогональную проекцию
noncomputable def distToLine (p : Point) (l : Line) : ℝ :=
  -- Вычисляем параметр проекции точки p на прямую l
  let t := ⟪p - l.p, l.v⟫_ℝ / ‖l.v‖ ^ 2
  -- Возвращаем норму (длину) перпендикуляра от точки p до её проекции на прямую
  ‖(p - l.p) - t • l.v‖

-- 2. Вспомогательная лемма о несовпадении точки p₀ = h + u и x = h + α • v при u ⊥ v, u ≠ 0
lemma ne_of_orth_add {h u v : Point} {α : ℝ}
    -- Предположение: вектор u ненулевой
    (hu : u ≠ 0)
    -- Предположение: векторы u и v ортогональны
    (huv : ⟪u, v⟫_ℝ = 0) :
    -- Утверждение: точки h + u и h + α • v не совпадают
    h + u ≠ h + α • v := by
  -- Предполагаем от противного, что точки равны
  intro eq
  -- Сокращаем слева на вектор h, получая u = α • v
  have hu_eq : u = α • v := add_left_cancel eq
  -- Доказываем, что скалярный квадрат вектора u равен нулю
  have h_inner : ⟪u, u⟫_ℝ = 0 := by
    -- Цепочка равенств для вычисления ⟪u, u⟫
    calc ⟪u, u⟫_ℝ = ⟪u, α • v⟫_ℝ := by nth_rw 2 [hu_eq]
      -- Выносим скаляр α из второго аргумента скалярного произведения
      _ = α * ⟪u, v⟫_ℝ := inner_smul_right u v α
      -- Подставляем ортогональность ⟪u, v⟫ = 0 и получаем 0
      _ = 0 := by rw [huv, mul_zero]
  -- Из ⟪u, u⟫ = 0 следует u = 0, что противоречит гипотезе hu : u ≠ 0
  exact hu (inner_self_eq_zero.mp h_inner)

-- 3. Ключевое геометрическое неравенство (свойство высот прямоугольного треугольника)
lemma kelly_core_ineq {h u v : Point} {α β : ℝ}
    -- Предположение: высота u ненулевая
    (hu : u ≠ 0)
    -- Предположение: направляющий вектор v ненулевой
    (hv : v ≠ 0)
    -- Предположение: векторы u и v перпендикулярны
    (huv : ⟪u, v⟫_ℝ = 0)
    -- Предположение: точки x и y лежат по одну сторону от h (или совпадают с h)
    (h_same_side : 0 ≤ β * α)
    -- Предположение: точка y строго ближе к основанию перпендикуляра h, чем x
    (h_closer : β ^ 2 < α ^ 2) :
    -- Утверждение 1: точка y не лежит на гипотенузе (прямой через p₀ и x)
    ¬ OnLine (h + β • v) (lineThrough (h + u) (h + α • v) (ne_of_orth_add hu huv)) ∧
    -- Утверждение 2: расстояние от y до гипотенузы строго меньше длины катета ‖u‖
    distToLine (h + β • v) (lineThrough (h + u) (h + α • v) (ne_of_orth_add hu huv)) < ‖u‖ := by
  -- Доказываем, что α ≠ 0
  have h_alpha_ne : α ≠ 0 := by
    -- Если α = 0, то β² < 0, что невозможно
    intro h0; rw [h0] at h_closer; nlinarith [sq_nonneg β]
  -- Доказываем, что β ≠ α
  have h_ba_ne : β ≠ α := by
    -- Если β = α, то α² < α², противоречие
    intro h_eq; rw [h_eq] at h_closer; exact lt_irrefl _ h_closer

  -- Разбиваем доказательство конъюнкции на две части
  constructor
  · -- Часть 1: y ∉ lineThrough p₀ x
    -- Предполагаем, что y лежит на прямой с параметром t
    rintro ⟨t, ht⟩
    -- Раскрываем определение lineThrough в гипотезе ht
    simp only [lineThrough] at ht
    -- Переносим всё в одну сторону: (β - t*α) • v = (1 - t) • u
    have h_vec : (β - t * α) • v = (1 - t) • u := by
      -- Вычитаем (h + u) из обеих частей уравнения ht
      have h1 : (h + β • v) - (h + u) = t • ((h + α • v) - (h + u)) := by
        rw [ht]; abel_nf
      -- Упрощаем разности, сокращая вектор h
      have h2 : β • v - u = t • (α • v - u) := by
        convert h1 using 1 <;> abel_nf
      -- Раскрываем скобки в правой части h2
      rw [smul_sub, ← mul_smul] at h2
      -- Перегруппировываем слагаемые, добавляя u и вычитая (t * α) • v
      have h3 : (β • v - u) + u - (t * α) • v = ((t * α) • v - t • u) + u - (t * α) • v := by
        rw [h2]
      -- Собираем коэффициенты при векторах v и u в цепочке равенств
      calc (β - t * α) • v = (β • v - u) + u - (t * α) • v := by rw [sub_smul]; abel_nf
        _ = ((t * α) • v - t • u) + u - (t * α) • v := h3
        _ = (1 - t) • u := by rw [sub_smul, one_smul]; abel_nf
    -- Скалярно умножаем обе части равенства h_vec на u, используя u ⊥ v
    have h_inner_u : ⟪(β - t * α) • v, u⟫_ℝ = ⟪(1 - t) • u, u⟫_ℝ := congrArg (⟪·, u⟫_ℝ) h_vec
    -- Используем симметричность скалярного произведения, чтобы получить ⟪v, u⟫ = 0
    have hvu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm, huv]
    -- Упрощаем левую часть до 0, а из правой выносим (1 - t)
    simp only [inner_smul_left, starRingEnd_apply, star_trivial, hvu, mul_zero] at h_inner_u
    -- Показываем, что скалярный квадрат ⟪u, u⟫ не равен нулю
    have hu_sq_ne : ⟪u, u⟫_ℝ ≠ 0 := mt inner_self_eq_zero.mp hu
    -- Выводим, что t = 1
    have ht1 : t = 1 := by
      -- Из 0 = (1 - t) * ⟪u, u⟫ и ⟪u, u⟫ ≠ 0 следует 1 - t = 0
      have : 1 - t = 0 := (mul_eq_zero.mp h_inner_u.symm).resolve_right hu_sq_ne
      -- Решаем линейное уравнение 1 - t = 0
      linarith
    -- Подставляем t = 1 в векторное равенство и получаем (β - α) • v = 0
    rw [ht1, sub_self, zero_smul, one_mul] at h_vec
    -- Показываем, что ⟪v, v⟫ ≠ 0
    have hv_sq_ne : ⟪v, v⟫_ℝ ≠ 0 := mt inner_self_eq_zero.mp hv
    -- Скалярно умножаем (β - α) • v = 0 на v
    have h_inner_v : ⟪(β - α) • v, v⟫_ℝ = 0 := by rw [h_vec, inner_zero_left]
    -- Выносим скаляр (β - α) из скалярного произведения
    simp only [inner_smul_left, starRingEnd_apply, star_trivial] at h_inner_v
    -- Делим на ⟪v, v⟫ ≠ 0 и получаем β - α = 0
    have : β - α = 0 := (mul_eq_zero.mp h_inner_v).resolve_right hv_sq_ne
    -- Получаем β = α, что противоречит h_ba_ne : β ≠ α
    exact h_ba_ne (sub_eq_zero.mp this)

  · -- Часть 2: distToLine y (lineThrough p₀ x) < ‖u‖
    -- Норма ненулевого вектора u строго положительна
    have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu

    -- Вводим сокращённое обозначение U = ‖u‖²
    set U := ‖u‖ ^ 2
    -- Вводим сокращённое обозначение V = ‖v‖²
    set V := ‖v‖ ^ 2
    -- Показываем, что U > 0
    have hU : 0 < U := sq_pos_of_pos hu_norm_pos
    -- Показываем, что V > 0
    have hV : 0 < V := sq_pos_of_pos (norm_pos_iff.mpr hv)

    -- Обозначаем направляющий вектор гипотенузы w = x - p₀
    set w := (h + α • v) - (h + u)
    -- Обозначаем вектор от p₀ до y как z = y - p₀
    set z := (h + β • v) - (h + u)
    -- Упрощаем выражение для w до α • v - u
    have hw_eq : w = α • v - u := by dsimp [w]; abel_nf
    -- Упрощаем выражение для z до β • v - u
    have hz_eq : z = β • v - u := by dsimp [z]; abel_nf

    -- Фиксируем ортогональность u и v в локальных гипотезах для simp
    have h_inner_uv : ⟪u, v⟫_ℝ = 0 := huv
    have h_inner_vu : ⟪v, u⟫_ℝ = 0 := by rw [real_inner_comm, huv]
    -- Связываем скалярные квадраты с U и V
    have h_uu : ⟪u, u⟫_ℝ = U := real_inner_self_eq_norm_sq u
    have h_vv : ⟪v, v⟫_ℝ = V := real_inner_self_eq_norm_sq v

    -- Вычисляем квадрат длины гипотенузы ‖w‖² = α²V + U (теорема Пифагора)
    have hw_norm_sq : ‖w‖ ^ 2 = α ^ 2 * V + U := by
      rw [← real_inner_self_eq_norm_sq, hw_eq]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
                 starRingEnd_apply, star_trivial, h_uu, h_vv, h_inner_uv, h_inner_vu]
      ring

    -- Вычисляем квадрат длины отрезка ‖z‖² = β²V + U (теорема Пифагора)
    have hz_norm_sq : ‖z‖ ^ 2 = β ^ 2 * V + U := by
      rw [← real_inner_self_eq_norm_sq, hz_eq]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
                 starRingEnd_apply, star_trivial, h_uu, h_vv, h_inner_uv, h_inner_vu]
      ring

    -- Вычисляем скалярное произведение ⟪z, w⟫ = αβV + U
    have hzw_inner : ⟪z, w⟫_ℝ = α * β * V + U := by
      rw [hz_eq, hw_eq]
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
                 starRingEnd_apply, star_trivial, h_uu, h_vv, h_inner_uv, h_inner_vu]
      ring

    -- Раскрываем определения distToLine и lineThrough в цели
    dsimp only [distToLine, lineThrough]
    -- Переписываем цель через введенные обозначения z и w
    change ‖z - (⟪z, w⟫_ℝ / ‖w‖ ^ 2) • w‖ < ‖u‖
    -- Обозначаем искомое расстояние через d
    set d := ‖z - (⟪z, w⟫_ℝ / ‖w‖ ^ 2) • w‖
    -- Фиксируем неотрицательность расстояния d ≥ 0
    have hd_nonneg : 0 ≤ d := norm_nonneg _

    -- Доказываем строгое неравенство для квадратов: d ^ 2 < U
    have hd_sq_lt : d ^ 2 < U := by
      -- Раскрываем определение d
      dsimp only [d]
      -- Переходим от квадрата нормы к скалярному произведению вектора самого на себя
      rw [← real_inner_self_eq_norm_sq]
      -- Используем симметричность скалярного произведения ⟪w, z⟫ = ⟪z, w⟫
      have hwz : ⟪w, z⟫_ℝ = ⟪z, w⟫_ℝ := real_inner_comm z w
      -- Раскрываем билинейность скалярного произведения
      simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
                 starRingEnd_apply, star_trivial, hwz, real_inner_self_eq_norm_sq]
      -- Подставляем ранее вычисленные значения ‖z‖², ⟪z, w⟫ и ‖w‖²
      rw [hz_norm_sq, hzw_inner, hw_norm_sq]
      -- Показываем, что знаменатель α²V + U строго положителен
      have h_denom : 0 < α ^ 2 * V + U := by nlinarith
      -- Сокращаем дробь со знаменателем и упрощаем арифметику
      rw [div_mul_cancel₀ _ h_denom.ne', sub_self, mul_zero, sub_zero]
      -- Переносим члены неравенства и избавляемся от деления на положительный знаменатель
      rw [sub_lt_comm, add_sub_cancel_right, div_mul_eq_mul_div, lt_div_iff₀ h_denom]
      -- Алгебраическое тождество для разности квадратов после приведения к общему знаменателю
      have h_id : (α * β * V + U) * (α * β * V + U) - β ^ 2 * V * (α ^ 2 * V + U) =
          U ^ 2 + U * V * (2 * (β * α) - β ^ 2) := by ring
      -- Показываем, что β² ≤ βα (так как β и α одного знака и |β| < |α|)
      have h_ba_ge : β ^ 2 ≤ β * α := by
        -- Сначала доказываем неравенство для квадратов: (β²)² ≤ (βα)²
        have h_sq_le : (β ^ 2) ^ 2 ≤ (β * α) ^ 2 := by
          have : (β * α) ^ 2 - (β ^ 2) ^ 2 = β ^ 2 * (α ^ 2 - β ^ 2) := by ring
          linarith [mul_nonneg (sq_nonneg β) (sub_nonneg.mpr h_closer.le)]
        -- Из (β²)² ≤ (βα)², β² ≥ 0 и βα ≥ 0 выводим β² ≤ βα
        nlinarith [sq_nonneg β]
      -- Убеждаемся, что слагаемое U * V * (2 * (β * α) - β²) неотрицательно
      have h_term_nonneg : 0 ≤ U * V * (2 * (β * α) - β ^ 2) :=
        mul_nonneg (mul_pos hU hV).le (by linarith)
      -- Квадрат строго положительного числа U строго положителен
      have h_U_sq_pos : 0 < U ^ 2 := sq_pos_of_pos hU
      -- Комбинируем тождество и оценки для завершения доказательства d² < U
      linarith

    -- Раскрываем определение U = ‖u‖² в гипотезе hd_sq_lt
    dsimp only [U] at hd_sq_lt
    -- Из d ^ 2 < ‖u‖ ^ 2 и 0 ≤ d, 0 < ‖u‖ автоматически следует d < ‖u‖
    nlinarith


-- 4. Главная теорема: Геометрическая лемма Келли
theorem kelly_triangle_ineq {p₀ a b c : Point} {l₀ : Line}
    -- Предположение: точка p₀ не лежит на прямой l₀
    (hp₀ : ¬ OnLine p₀ l₀)
    -- Предположения: точки a, b, c лежат на прямой l₀
    (ha : OnLine a l₀) (hb : OnLine b l₀) (hc : OnLine c l₀)
    -- Предположения: точки a, b, c попарно различны
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    -- Утверждение: существуют две точки x, y из {a, b, c} такие, что
    ∃ (x y : Point) (hxy : p₀ ≠ x),
      -- x и y принадлежат множеству {a, b, c}
      (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧
      -- точка y не лежит на прямой p₀x
      ¬ OnLine y (lineThrough p₀ x hxy) ∧
      -- и расстояние от y до прямой p₀x строго меньше расстояния от p₀ до l₀
      distToLine y (lineThrough p₀ x hxy) < distToLine p₀ l₀ := by
  -- Выделяем направляющий вектор v прямой l₀
  let v := l₀.v
  -- Фиксируем, что v ≠ 0
  have hv : v ≠ 0 := l₀.hv
  -- Фиксируем, что квадрат нормы вектора v не равен нулю
  have hv_sq : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)

  -- Вычисляем параметр t₀ ортогональной проекции точки p₀ на прямую l₀
  let t₀ := ⟪p₀ - l₀.p, v⟫_ℝ / ‖v‖ ^ 2
  -- Определяем основание перпендикуляра h на прямой l₀
  let h := l₀.p + t₀ • v
  -- Определяем вектор перпендикуляра u от основания h к точке p₀
  let u := p₀ - h

  -- Доказываем, что вектор u ортогонален направляющему вектору v
  have huv : ⟪u, v⟫_ℝ = 0 := by
    -- Раскрываем определения u, h и t₀
    dsimp [u, h, t₀]
    -- Перегруппировываем разность векторов для выноса проекции
    have : p₀ - (l₀.p + (⟪p₀ - l₀.p, v⟫_ℝ / ‖v‖ ^ 2) • v) =
           (p₀ - l₀.p) - (⟪p₀ - l₀.p, v⟫_ℝ / ‖v‖ ^ 2) • v := by abel_nf
    -- Раскрываем линейность скалярного произведения по первому аргументу
    rw [this, inner_sub_left, inner_smul_left, real_inner_self_eq_norm_sq]
    -- Упрощаем тривиальное комплексное сопряжение в ℝ
    simp only [starRingEnd_apply, star_trivial]
    -- Сокращаем ‖v‖² в числителе и знаменателе и получаем ноль
    rw [div_mul_cancel₀ _ hv_sq, sub_self]

  -- Доказываем, что вектор u не равен нулю (иначе p₀ = h лежала бы на l₀)
  have hu : u ≠ 0 := by
    -- Предполагаем от противного, что u = 0
    intro hu0
    -- Применяем гипотезу hp₀ : ¬ OnLine p₀ l₀ для получения противоречия
    apply hp₀
    -- Предъявляем параметр t₀ в качестве свидетеля принадлежности p₀ прямой l₀
    refine ⟨t₀, ?_⟩
    -- Из p₀ - h = 0 выводим p₀ = l₀.p + t₀ • v
    exact sub_eq_zero.mp hu0

  -- Показываем, что расстояние от p₀ до l₀ равно длине вектора u
  have h_dist_p₀ : distToLine p₀ l₀ = ‖u‖ := by
    -- Раскрываем определения distToLine, u, h, t₀ и v
    dsimp [distToLine, u, h, t₀, v]
    -- Приводим выражения под знаком нормы к одинаковому виду
    congr 1; abel_nf

  -- Извлекаем параметры ta, tb, tc точек a, b, c на прямой l₀
  rcases ha with ⟨ta, hta⟩
  rcases hb with ⟨tb, htb⟩
  rcases hc with ⟨tc, htc⟩

  -- Вычисляем смещённые координаты α, β, γ точек a, b, c относительно основания h
  let α := ta - t₀
  let β := tb - t₀
  let γ := tc - t₀

  -- Выражаем точки a, b, c через основание h и смещённые координаты α, β, γ
  have ha_eq : a = h + α • v := by dsimp [h, α, v]; rw [hta, sub_smul]; abel_nf
  have hb_eq : b = h + β • v := by dsimp [h, β, v]; rw [htb, sub_smul]; abel_nf
  have hc_eq : c = h + γ • v := by dsimp [h, γ, v]; rw [htc, sub_smul]; abel_nf

  -- Из попарного различия точек a, b, c выводим попарное различие координат α, β, γ
  have hαβ : α ≠ β := fun e => hab (by rw [ha_eq, hb_eq, e])
  have hβγ : β ≠ γ := fun e => hbc (by rw [hb_eq, hc_eq, e])
  have hαγ : α ≠ γ := fun e => hac (by rw [ha_eq, hc_eq, e])

  -- Вспомогательная функция для применения леммы kelly_core_ineq к произвольной паре точек (px, py)
  have apply_core : ∀ (px py : Point) (cx cy : ℝ),
      -- Точки px и py выбраны из множества {a, b, c}
      (px = a ∨ px = b ∨ px = c) → (py = a ∨ py = b ∨ py = c) →
      -- Представления точек px и py относительно основания перпендикуляра h
      px = h + cx • v → py = h + cy • v →
      -- Условия того, что точки по одну сторону от h и py ближе к h, чем px
      0 ≤ cy * cx → cy ^ 2 < cx ^ 2 →
      -- Заключение главной теоремы для конкретной пары (px, py)
      ∃ (x y : Point) (hxy : p₀ ≠ x),
        (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧
        ¬ OnLine y (lineThrough p₀ x hxy) ∧
        distToLine y (lineThrough p₀ x hxy) < distToLine p₀ l₀ := by
    -- Вводим все параметры и гипотезы в контекст
    intro px py cx cy hx_in hy_in hpx_eq hpy_eq h_side h_close
    -- Представляем точку p₀ в виде h + u
    have hp₀_eq : p₀ = h + u := by dsimp [u]; abel_nf
    -- Доказываем, что p₀ ≠ px по вспомогательной лемме ne_of_orth_add
    have h_ne : p₀ ≠ px := by
      rw [hp₀_eq, hpx_eq]
      exact ne_of_orth_add hu huv
    -- Вызываем основное геометрическое неравенство kelly_core_ineq
    rcases kelly_core_ineq (h := h) hu hv huv h_side h_close with ⟨res1, res2⟩
    -- Собираем экзистенциальный свидетель из полученных результатов
    refine ⟨px, py, h_ne, hx_in, hy_in, ?_, ?_⟩
    -- Подставляем представления точек в первую часть (непринадлежность прямой)
    · simp only [hp₀_eq, hpx_eq, hpy_eq]
      exact res1
    -- Заменяем distToLine p₀ l₀ на ‖u‖ и подставляем представления во вторую часть (неравенство расстояний)
    · rw [h_dist_p₀]
      simp only [hp₀_eq, hpx_eq, hpy_eq]
      exact res2

  -- Вспомогательный блок для пары точек одного знака:
  -- из cx * cy ≥ 0 и cx ≠ cy сразу получаем строгое неравенство квадратов
  have same_sign_case : ∀ (px py : Point) (cx cy : ℝ),
      -- Точки px и py выбраны из множества {a, b, c}
      (px = a ∨ px = b ∨ px = c) → (py = a ∨ py = b ∨ py = c) →
      -- Представления точек px и py относительно основания h
      px = h + cx • v → py = h + cy • v →
      -- Координаты различны и имеют одинаковый знак (оба ≥ 0 или оба < 0)
      cx ≠ cy → (0 ≤ cx ∧ 0 ≤ cy ∨ cx < 0 ∧ cy < 0) →
      -- Заключение главной теоремы
      ∃ (x y : Point) (hxy : p₀ ≠ x),
        (x = a ∨ x = b ∨ x = c) ∧ (y = a ∨ y = b ∨ y = c) ∧
        ¬ OnLine y (lineThrough p₀ x hxy) ∧
        distToLine y (lineThrough p₀ x hxy) < distToLine p₀ l₀ := by
    -- Вводим параметры и гипотезы в контекст
    intro px py cx cy hx_in hy_in hpx_eq hpy_eq hne hsign
    -- Доказываем, что квадраты координат различны: cx² ≠ cy²
    have h_sq_ne : cx ^ 2 ≠ cy ^ 2 := by
      -- Предполагаем от противного, что cx² = cy²
      intro heq
      -- Раскладываем разность квадратов на множители: (cx - cy)(cx + cy) = 0
      have h_diff : (cx - cy) * (cx + cy) = 0 := by linear_combination heq
      -- Разбираем два случая: cx - cy = 0 или cx + cy = 0
      rcases mul_eq_zero.mp h_diff with hsub | hadd
      -- Если cx - cy = 0, получаем cx = cy, противоречие с hne
      · exact hne (sub_eq_zero.mp hsub)
      -- Если cx + cy = 0 и числа одного знака, то оба равны 0, что противоречит cx ≠ cy
      · rcases hsign with ⟨hcx, hcy⟩ | ⟨hcx, hcy⟩
        -- Случай 0 ≤ cx и 0 ≤ cy: из cx + cy = 0 следует cx = cy = 0
        · exact hne (by linarith)
        -- Случай cx < 0 и cy < 0: сумма двух отрицательных чисел не может быть равна 0
        · linarith

    -- Сравниваем cy² и cx² по трихотомии (<, =, >)
    rcases lt_trichotomy (cy ^ 2) (cx ^ 2) with hlt | heq | hgt
    -- Случай cy² < cx²: точка py ближе к h, применяем apply_core к (px, py)
    · exact apply_core px py cx cy hx_in hy_in hpx_eq hpy_eq
        (by rcases hsign with ⟨_, _⟩ | ⟨_, _⟩ <;> nlinarith) hlt
    -- Случай cy² = cx²: невозможен по доказанному выше h_sq_ne
    · exact False.elim (h_sq_ne heq.symm)
    -- Случай cx² < cy²: точка px ближе к h, меняем точки местами и применяем apply_core к (py, px)
    · exact apply_core py px cy cx hy_in hx_in hpy_eq hpx_eq
        (by rcases hsign with ⟨_, _⟩ | ⟨_, _⟩ <;> nlinarith) hgt

   -- Перебор всех пар по принципу Дирихле (из 3 чисел минимум 2 лежат в {≥ 0} или {< 0})
  by_cases hα : 0 ≤ α <;> by_cases hβ : 0 ≤ β <;> by_cases hγ : 0 ≤ γ
  -- Случай 1: α ≥ 0, β ≥ 0, γ ≥ 0 -> берём пару (a, b)
  · exact same_sign_case a b α β (Or.inl rfl) (Or.inr (Or.inl rfl)) ha_eq hb_eq hαβ (Or.inl ⟨hα, hβ⟩)
  -- Случай 2: α ≥ 0, β ≥ 0, γ < 0 -> берём пару (a, b)
  · exact same_sign_case a b α β (Or.inl rfl) (Or.inr (Or.inl rfl)) ha_eq hb_eq hαβ (Or.inl ⟨hα, hβ⟩)
  -- Случай 3: α ≥ 0, β < 0, γ ≥ 0 -> берём пару (a, c)
  · exact same_sign_case a c α γ (Or.inl rfl) (Or.inr (Or.inr rfl)) ha_eq hc_eq hαγ (Or.inl ⟨hα, hγ⟩)
  -- Случай 4: α ≥ 0, β < 0, γ < 0 -> преобразуем ¬(0 ≤ β) в β < 0 и берём пару (b, c)
  · push Not at hβ hγ
    exact same_sign_case b c β γ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hb_eq hc_eq hβγ (Or.inr ⟨hβ, hγ⟩)
  -- Случай 5: α < 0, β ≥ 0, γ ≥ 0 -> берём пару (b, c)
  · exact same_sign_case b c β γ (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl)) hb_eq hc_eq hβγ (Or.inl ⟨hβ, hγ⟩)
  -- Случай 6: α < 0, β ≥ 0, γ < 0 -> преобразуем отрицания и берём пару (a, c)
  · push Not at hα hγ
    exact same_sign_case a c α γ (Or.inl rfl) (Or.inr (Or.inr rfl)) ha_eq hc_eq hαγ (Or.inr ⟨hα, hγ⟩)
  -- Случай 7: α < 0, β < 0, γ ≥ 0 -> преобразуем отрицания и берём пару (a, b)
  · push Not at hα hβ
    exact same_sign_case a b α β (Or.inl rfl) (Or.inr (Or.inl rfl)) ha_eq hb_eq hαβ (Or.inr ⟨hα, hβ⟩)
  -- Случай 8: α < 0, β < 0, γ < 0 -> преобразуем отрицания и берём пару (a, b)
  · push Not at hα hβ hγ
    exact same_sign_case a b α β (Or.inl rfl) (Or.inr (Or.inl rfl)) ha_eq hb_eq hαβ (Or.inr ⟨hα, hβ⟩)
