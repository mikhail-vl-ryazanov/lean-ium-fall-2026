-- Подключаем базовые определения и свойства конечных множеств (Finset)
import Mathlib.Data.Finset.Basic
-- Подключаем декартово произведение конечных множеств (×ˢ)
import Mathlib.Data.Finset.Prod
-- Подключаем вещественные числа (в стандартном Mathlib путь обычно Mathlib.Data.Real.Basic)
import Mathlib.Basic.Real.Basic
-- Подключаем стандартный набор тактик доказательств (simp, omega, linarith и др.)
import Mathlib.Tactic
-- Подключаем локальный модуль с определениями Point, Line, OnLine, distToLine и леммой kelly_triangle_ineq
import Seminars.KellyTheorem

-- Открываем секцию для локальной изоляции настроек и атрибутов
section KellyProof

-- Локально включаем классическую разрешимость всех высказываний (закон исключённого третьего)
attribute [local instance] Classical.propDecidable

/-- Вспомогательные свойства для lineThrough из Seminars.KellyTheorem -/
-- Формулируем лемму: первая точка p₁ лежит на прямой, проведённой через p₁ и p₂
lemma onLine_left (p₁ p₂ : Point) (h : p₁ ≠ p₂) : OnLine p₁ (lineThrough p₁ p₂ h) :=
  -- Свидетелем принадлежности является параметр t = 0: p₁ + 0 • (p₂ - p₁) = p₁
  ⟨0, by simp [lineThrough]⟩

-- Формулируем лемму: вторая точка p₂ лежит на прямой, проведённой через p₁ и p₂
lemma onLine_right (p₁ p₂ : Point) (h : p₁ ≠ p₂) : OnLine p₂ (lineThrough p₁ p₂ h) :=
  -- Свидетелем принадлежности является параметр t = 1: p₁ + 1 • (p₂ - p₁) = p₂
  ⟨1, by simp [lineThrough]⟩

/-- Множество всех соединяющих прямых W(M) -/
-- Определяем невычислимое конечное множество всех прямых, проходящих через пары точек из M
noncomputable def W (M : Finset Point) : Finset Line := by
  -- Включаем классическую логику внутри тела определения для работы с фильтрацией и образом Finset
  classical
  -- Берём все пары различных точек из M × M, прикрепляем доказательство различия (.attach) и строим образ
  exact ((M ×ˢ M).filter (fun p => p.1 ≠ p.2)).attach.image
    -- Задаём функцию отображения: строим прямую через пару точек p.val.1 и p.val.2
    (fun p => lineThrough p.val.1 p.val.2 (by
      -- Извлекаем из свойства прикреплённого элемента условие фильтрации
      have h := Finset.mem_filter.mp p.property
      -- Передаём доказательство того, что p.val.1 ≠ p.val.2, в конструктор прямой lineThrough
      exact h.2))

-- Формулируем лемму-критерий принадлежности прямой l множеству соединяющих прямых W M
lemma mem_W_iff (M : Finset Point) (l : Line) :
    -- Прямая l лежит в W M тогда и только тогда, когда существуют две различные точки p₁, p₂ ∈ M,
    l ∈ W M ↔ ∃ (p₁ : Point) (_ : p₁ ∈ M) (p₂ : Point) (_ : p₂ ∈ M) (hneq : p₁ ≠ p₂),
      -- такие, что l совпадает с прямой, проведённой через p₁ и p₂
      l = lineThrough p₁ p₂ hneq := by
  -- Используем классическую разрешимость для операций над Finset
  classical
  -- Раскрываем определение множества W
  unfold W
  -- Переписываем принадлежность образу множества через существование прообраза
  rw [Finset.mem_image]
  -- Разбиваем доказательство эквивалентности «↔» на два направления (→ и ←)
  constructor
  -- Направление (→): пусть прямая l принадлежит образу W M
  · intro h
    -- Извлекаем прообраз pair (элемент с доказательством) и равенство lineThrough ... = l
    rcases h with ⟨pair, _, h_eq⟩
    -- Раскрываем условие принадлежности пары отфильтрованному множеству
    have hp := Finset.mem_filter.mp pair.property
    -- Раскрываем принадлежность декартову произведению M ×ˢ M
    have hprod := Finset.mem_product.mp hp.1
    -- Предъявляем обе точки, их принадлежность M, неравенство и симметричное равенство l = ...
    exact ⟨pair.val.1, hprod.1, pair.val.2, hprod.2, hp.2, h_eq.symm⟩
  -- Направление (←): пусть существуют две различные точки p₁, p₂ ∈ M, задающие прямую l
  · intro h
    -- Извлекаем все компоненты из гипотезы существования
    rcases h with ⟨p₁, hp1, p₂, hp2, hneq, h_eq⟩
    -- Подставляем выражение lineThrough p₁ p₂ hneq вместо l в цель
    rw [h_eq]
    -- Объявляем гипотезу hp о том, что пара (p₁, p₂) лежит в отфильтрованном произведении
    have hp : (p₁, p₂) ∈ (M ×ˢ M).filter (fun p => p.1 ≠ p.2) :=
      -- Собираем принадлежность произведению и условие p₁ ≠ p₂
      Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp1, hp2⟩, hneq⟩
    -- Предъявляем прикреплённую пару ⟨(p₁, p₂), hp⟩ как искомый прообраз
    exact ⟨⟨(p₁, p₂), hp⟩, Finset.mem_attach _ _, rfl⟩

-- Определяем свойство коллинеарности конечного множества точек M
def AreCollinear (M : Finset Point) : Prop :=
  -- Множество M коллинеарно, если существует прямая l, на которой лежат все точки из M
  ∃ l : Line, ∀ p ∈ M, OnLine p l

-- Определяем свойство ординарной (обыкновенной) прямой для множества M
def IsOrdinary (l : Line) (M : Finset Point) : Prop :=
  -- Прямая l называется ординарной, если количество точек из M, лежащих на ней, равно ровно 2
  (M.filter (fun p => OnLine p l)).card = 2

/-- Стандартная ненулевая прямая (ось X) на случай пустого множества -/
-- Определяем конкретный экземпляр прямой (ось абсцисс)
noncomputable def defaultLine : Line where
  -- Задаём начальную точку прямой — начало координат (нулевой вектор)
  p := 0
  -- Задаём направляющий вектор — первый стандартный базисный орт (1, 0, ...)
  v := EuclideanSpace.single 0 1
  -- Начинаем доказательство того, что направляющий вектор не является нулевым
  hv := by
    -- Предположим от противного, что направляющий вектор равен 0
    intro h
    -- Извлекаем равенство нулевых координат (индекс 0) из равенства векторов
    have h0 := congrFun (congrArg WithLp.ofLp h) 0
    -- Упрощаем выражение и получаем противоречие 1 = 0
    simp at h0

/-- Вспомогательная лемма: если M не коллинеарно, то в M есть хотя бы 3 неколлинеарные точки,
    и множество пар (p, l) с p ∈ M, l ∈ W M, ¬ OnLine p l непусто. -/
-- Формулируем лемму о существовании пары «точка вне соединяющей прямой»
lemma exists_point_line_pair (M : Finset Point) (h_noncol : ¬ AreCollinear M) :
    -- Утверждаем, что найдутся точка p ∈ M и прямая l ∈ W M такие, что p не лежит на l
    ∃ p ∈ M, ∃ l ∈ W M, ¬ OnLine p l := by
  -- Включаем классическую логику для работы с мощностью Finset и разбором случаев
  classical
  -- Разбираем два случая: в множестве M не более одной точки (M.card ≤ 1) или больше одной
  by_cases h_card : M.card ≤ 1
  -- Случай M.card ≤ 1: приводим к противоречию, доказывая, что такое M всегда коллинеарно
  · exfalso; apply h_noncol
    -- Разбираем подслучаи: множество M пусто или содержит хотя бы один элемент p
    rcases M.eq_empty_or_nonempty with h_empty | ⟨p, hp⟩
    -- Подслучай 1: M пусто (M = ∅), подставляем пустое множество
    · rw [h_empty]
      -- Берём defaultLine; условие ∀ p ∈ ∅, OnLine p l выполняется тривиально
      exact ⟨defaultLine, by simp⟩
    -- Подслучай 2: в M есть точка p; проводим через p прямую с направляющим вектором от defaultLine
    · refine ⟨{ p := p, v := defaultLine.v, hv := defaultLine.hv }, fun x hx => ?_⟩
      -- Так как мощность M ≤ 1, любая точка x ∈ M совпадает с p
      have h_eq : x = p := Finset.card_le_one.mp h_card x hx p hp
      -- Заменяем x на p в цели
      rw [h_eq]
      -- Точка p лежит на проведённой через неё прямой при параметре t = 0
      exact ⟨0, by simp⟩
  -- Случай ¬(M.card ≤ 1): преобразуем отрицание в строгое неравенство 1 < M.card
  · push Not at h_card
    -- Из 1 < M.card арифметически следует 0 < M.card
    have h_pos1 : 0 < M.card := by omega
    -- Извлекаем первую точку p₁ ∈ M, так как мощность M положительна
    obtain ⟨p₁, hp₁⟩ := Finset.card_pos.mp h_pos1
    -- Показываем, что после удаления p₁ в M ещё остаются точки
    have h_pos2 : 0 < (M.erase p₁).card := by
      -- Мощность M \ {p₁} равна M.card - 1
      rw [Finset.card_erase_of_mem hp₁]
      -- Из 1 < M.card следует 0 < M.card - 1
      omega
    -- Извлекаем вторую точку p₂ из множества M \ {p₁}
    obtain ⟨p₂, hp₂_erase⟩ := Finset.card_pos.mp h_pos2
    -- Так как p₂ ∈ M.erase p₁, точки p₁ и p₂ различны
    have hneq : p₁ ≠ p₂ := (Finset.ne_of_mem_erase hp₂_erase).symm
    -- Точка p₂ также принадлежит исходному множеству M
    have hp₂ : p₂ ∈ M := Finset.mem_of_mem_erase hp₂_erase
    -- Проводим соединяющую прямую l через p₁ и p₂
    let l := lineThrough p₁ p₂ hneq
    -- По лемме mem_W_iff прямая l принадлежит W M
    have hlW : l ∈ W M := (mem_W_iff M l).mpr ⟨p₁, hp₁, p₂, hp₂, hneq, rfl⟩
    -- Доказываем, что в M найдётся третья точка p₃, не лежащая на прямой l
    have hex : ∃ p₃ ∈ M, ¬ OnLine p₃ l := by
      -- Предположим от противного, что такой точки нет
      by_contra h_all
      -- Преобразуем отрицание: все точки множества M лежат на прямой l
      push Not at h_all
      -- Это означает, что M коллинеарно, что противоречит гипотезе h_noncol
      exact h_noncol ⟨l, h_all⟩
    -- Извлекаем точку p₃ ∈ M и доказательство того, что ¬ OnLine p₃ l
    obtain ⟨p₃, hp₃, hnot⟩ := hex
    -- Возвращаем искомую тройку: точка p₃, прямая l ∈ W M и условие ¬ OnLine p₃ l
    exact ⟨p₃, hp₃, l, hlW, hnot⟩

/-- Основная теорема Сильвестра — Галлаи (доказательство Келли) -/
-- Формулируем теорему Сильвестра — Галлаи
theorem sylvester_gallai (M : Finset Point) (h_noncol : ¬ AreCollinear M) :
    -- Для любого неколлинеарного конечного множества M существует ординарная прямая l ∈ W M
    ∃ l ∈ W M, IsOrdinary l M := by
  -- Включаем классическую логику для работы с конечными множествами
  classical
  -- 1. Формируем конечное множество допустимых пар (p, l)
  -- Определяем множество пар (точка p ∈ M, прямая l ∈ W M), где точка не лежит на прямой
  let validPairs := (M ×ˢ W M).filter (fun pair => ¬ OnLine pair.1 pair.2)
  -- Доказываем, что множество допустимых пар непусто
  have h_nonempty : validPairs.Nonempty := by
    -- Вызываем доказанную выше вспомогательную лемму
    obtain ⟨p, hp, l, hl, hnot⟩ := exists_point_line_pair M h_noncol
    -- Показываем, что найденная пара (p, l) принадлежит validPairs
    exact ⟨(p, l), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hl⟩, hnot⟩⟩

  -- 2. Выбираем пару (p₀, l₀) с минимальным расстоянием distToLine p₀ l₀
  -- По принципу наименьшего элемента на конечном непустом множестве извлекаем пару (p₀, l₀), доказательство её принадлежности h_mem и свойство минимальности h_min
  obtain ⟨⟨p₀, l₀⟩, h_mem, h_min⟩ :=
    -- Применяем лемму Finset.exists_min_image к множеству validPairs и функции расстояния distToLine
    Finset.exists_min_image validPairs (fun pair => distToLine pair.1 pair.2) h_nonempty
  -- Раскрываем определение validPairs (фильтр и декартово произведение) в гипотезе h_mem
  simp only [validPairs, Finset.mem_filter, Finset.mem_product] at h_mem
  -- Разбираем составную гипотезу h_mem на три отдельных факта: p₀ ∈ M, l₀ ∈ W M и ¬ OnLine p₀ l₀
  rcases h_mem with ⟨⟨hp₀M, hl₀W⟩, hp₀_not_l₀⟩

  -- Утверждаем, что выбранная прямая l₀ ∈ W M и есть искомая ординарная прямая; осталось доказать IsOrdinary l₀ M
  refine ⟨l₀, hl₀W, ?_⟩

  -- 3. Покажем, что на l₀ лежит ровно 2 точки из M
  -- Вводим локальное имя ptsOnL₀ для подмножества точек из M, лежащих на прямой l₀
  let ptsOnL₀ := M.filter (fun p => OnLine p l₀)
  -- Начинаем доказательство оценки снизу: на прямой l₀ лежит как минимум 2 точки из M
  have h_ge_2 : 2 ≤ ptsOnL₀.card := by
    -- Раскрываем условие hl₀W : l₀ ∈ W M через определение образа множества пар точек
    have hl₀_img : l₀ ∈ ((M ×ˢ M).filter (fun p => p.1 ≠ p.2)).attach.image
        -- Указываем функцию отображения, строящую прямую по паре различных точек
        (fun p => lineThrough p.val.1 p.val.2 (by
          -- Извлекаем условие фильтрации из свойства прикреплённого элемента
          have h := Finset.mem_filter.mp p.property
          -- Передаём доказательство неравенства точек в конструктор прямой
          exact h.2)) := hl₀W
    -- Переписываем принадлежность образу через существование прообраза в Finset
    rw [Finset.mem_image] at hl₀_img
    -- Извлекаем прообраз pair и равенство прямой l₀ выражению lineThrough ...
    obtain ⟨pair, _, hl₀_eq⟩ := hl₀_img
    -- Извлекаем из pair.property принадлежность произведению и условие различия точек
    have hp := Finset.mem_filter.mp pair.property
    -- Извлекаем из hp.1 принадлежность первой и второй точки множеству M
    have hprod := Finset.mem_product.mp hp.1
    -- Утверждаем, что двухэлементное множество из этих двух точек является подмножеством ptsOnL₀
    have hsub : ({pair.val.1, pair.val.2} : Finset Point) ⊆ ptsOnL₀ := by
      -- Берём произвольную точку x из двухэлементного множества
      intro x hx
      -- Раскрываем принадлежность множеству {p₁, p₂} как дизъюнкцию равенств x = p₁ ∨ x = p₂
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      -- Разбираем оба случая подстановкой равенства в цель
      rcases hx with rfl | rfl
      -- Случай x = pair.val.1: точка лежит в M и на прямой l₀ (по лемме onLine_left)
      · exact Finset.mem_filter.mpr ⟨hprod.1, hl₀_eq ▸ onLine_left pair.val.1 pair.val.2 hp.2⟩
      -- Случай x = pair.val.2: точка лежит в M и на прямой l₀ (по лемме onLine_right)
      · exact Finset.mem_filter.mpr ⟨hprod.2, hl₀_eq ▸ onLine_right pair.val.1 pair.val.2 hp.2⟩
    -- Записываем цепочку неравенств: мощность пары различных точек равна 2
    calc 2 = ({pair.val.1, pair.val.2} : Finset Point).card := (Finset.card_pair hp.2).symm
         -- Мощность подмножества не превосходит мощности всего множества ptsOnL₀
         _ ≤ ptsOnL₀.card := Finset.card_le_card hsub

  -- Предположим от противного, что точек на l₀ больше двух (≥ 3)
  -- Вводим гипотезу от противного h_not_two : ¬ (ptsOnL₀.card = 2)
  by_contra h_not_two
  -- Переписываем отрицание равенства в виде неравенства ≠ для работы тактики omega
  have h_ne_two : ptsOnL₀.card ≠ 2 := h_not_two
  -- Из 2 ≤ ptsOnL₀.card и ptsOnL₀.card ≠ 2 арифметически выводим строгое неравенство 2 < ptsOnL₀.card
  have h_gt_2 : 2 < ptsOnL₀.card := by omega
  -- Выводим отсюда положительность мощности ptsOnL₀
  have h_pos_a : 0 < ptsOnL₀.card := by omega
  -- Из положительности мощности извлекаем первую точку a ∈ ptsOnL₀
  obtain ⟨a, ha⟩ := Finset.card_pos.mp h_pos_a
  -- Выражаем мощность множества после удаления элемента a
  have h_erase_a : (ptsOnL₀.erase a).card = ptsOnL₀.card - 1 :=
    -- Используем стандартную лемму о мощности при удалении элемента из Finset
    Finset.card_erase_of_mem ha
  -- Так как исходная мощность > 2, после удаления a остаётся больше нуля элементов
  have h_pos_b : 0 < (ptsOnL₀.erase a).card := by omega
  -- Извлекаем вторую точку b из остатка ptsOnL₀.erase a
  obtain ⟨b, hb_er⟩ := Finset.card_pos.mp h_pos_b
  -- Фиксируем, что точки a и b различны
  have hab : a ≠ b := (Finset.ne_of_mem_erase hb_er).symm
  -- Фиксируем, что точка b принадлежит исходному множеству ptsOnL₀
  have hb : b ∈ ptsOnL₀ := Finset.mem_of_mem_erase hb_er
  -- Выражаем мощность множества после удаления второго элемента b
  have h_erase_b : ((ptsOnL₀.erase a).erase b).card = (ptsOnL₀.erase a).card - 1 :=
    -- Применяем ту же лемму о мощности после удаления элемента
    Finset.card_erase_of_mem hb_er
  -- Так как исходная мощность ≥ 3, после двух удалений остаётся хотя бы один элемент
  have h_pos_c : 0 < ((ptsOnL₀.erase a).erase b).card := by omega
  -- Извлекаем третью точку c из остатка (ptsOnL₀.erase a).erase b
  obtain ⟨c, hc_er⟩ := Finset.card_pos.mp h_pos_c
  -- Фиксируем, что точки b и c различны
  have hbc : b ≠ c := (Finset.ne_of_mem_erase hc_er).symm
  -- Фиксируем, что точка c принадлежит ptsOnL₀.erase a
  have hc_er1 : c ∈ ptsOnL₀.erase a := Finset.mem_of_mem_erase hc_er
  -- Фиксируем, что точки a и c также различны
  have hac : a ≠ c := (Finset.ne_of_mem_erase hc_er1).symm
  -- Фиксируем, что точка c принадлежит исходному множеству ptsOnL₀
  have hc : c ∈ ptsOnL₀ := Finset.mem_of_mem_erase hc_er1
  -- Раскрываем определение ptsOnL₀ в гипотезах ha, hb, hc (каждая точка лежит в M и на прямой l₀)
  simp only [ptsOnL₀, Finset.mem_filter] at ha hb hc


  -- 4. Применяем геометрическую лемму Келли из Seminars.KellyTheorem
  -- Извлекаем из геометрической леммы Келли две точки x, y и набор свойств (p₀ ≠ x, x,y ∈ {a,b,c}, y ∉ p₀x, строгое уменьшение расстояния)
  obtain ⟨x, y, hp₀_neq_x, hx_abc, hy_abc, hy_not_l', h_dist_lt⟩ :=
    -- Вызываем лемму kelly_triangle_ineq, передавая факт p₀ ∉ l₀, принадлежность a, b, c прямой l₀ и их попарную различность
    kelly_triangle_ineq hp₀_not_l₀ ha.2 hb.2 hc.2 hab hbc hac

  -- Доказываем, что точка y принадлежит множеству M, разбирая три возможных случая (y = a, y = b или y = c)
  have hyM : y ∈ M := by rcases hy_abc with rfl | rfl | rfl <;> simp [ha.1, hb.1, hc.1]

  -- Новая прямая l' = lineThrough p₀ x hp₀_neq_x принадлежит W M
  -- Проводим новую соединяющую прямую l' через вершину p₀ и выбранную точку x
  let l' := lineThrough p₀ x hp₀_neq_x
  -- Начинаем доказательство того, что новая прямая l' входит в множество всех соединяющих прямых W M
  have hl'W : l' ∈ W M := by
    -- Доказываем, что точка x принадлежит множеству M, разбирая случаи x = a, x = b или x = c
    have hxM : x ∈ M := by rcases hx_abc with rfl | rfl | rfl <;> simp [ha.1, hb.1, hc.1]
    -- Применяем критерий mem_W_iff: так как p₀ ∈ M, x ∈ M и p₀ ≠ x, прямая l' принадлежит W M
    exact (mem_W_iff M l').mpr ⟨p₀, hp₀M, x, hxM, hp₀_neq_x, rfl⟩

  -- Пара (y, l') принадлежит validPairs, но distToLine y l' < distToLine p₀ l₀ — противоречие!
  -- Формируем доказательство того, что новая пара (y, l') является допустимой парой из validPairs
  have hy_pair_mem : (y, l') ∈ validPairs :=
    -- Объединяем принадлежность декартову произведению (y ∈ M и l' ∈ W M) с условием ¬ OnLine y l'
    Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hyM, hl'W⟩, hy_not_l'⟩
  -- Применяем свойство минимальности пары (p₀, l₀) к новой паре (y, l'), получая distToLine p₀ l₀ ≤ distToLine y l'
  have h_le := h_min (y, l') hy_pair_mem
  -- Тактика линейной арифметики сопоставляет distToLine p₀ l₀ ≤ distToLine y l' и distToLine y l' < distToLine p₀ l₀ и завершает доказательство противоречием
  linarith


end KellyProof
