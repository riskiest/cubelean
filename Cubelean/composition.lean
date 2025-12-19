import Mathlib

lemma head_le_of_pairwise_lt {xs : List ℝ } (h_nonempty : xs ≠ [])
    (h_sorted : xs.Pairwise (· < ·)) (x : ℝ) (h_mem : x ∈ xs) : xs[0]! ≤ x := by
  cases xs with
  | nil => contradiction
  | cons head tail =>
    simp [List.mem_cons] at h_mem
    cases h_mem with
    | inl h_eq =>
      -- x = head
      rw [h_eq]
      simp [List.getElem_cons_zero]
    | inr h_tail =>
      -- x ∈ tail, 所以 head < x (由 Pairwise)
      have : head < x := by
        simp [] at h_sorted
        exact h_sorted.1 x h_tail
      exact le_of_lt this

-- 非可计算的递归函数定义
noncomputable def myf (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) : ℝ :=
  if ht : t <= 0 then
    -- 注意：原题是 t < 0 返回 0，t = 0 返回 1。
    -- 这里为了方便终止证明逻辑，先判断 t <= 0，内部再细分
    if t = 0 then 1 else 0
  else
    -- 此时 t > 0
    -- 使用 attach 获取元素属于列表的证明
    let sum := (xs.attach.map (fun ⟨xi, hxi⟩ =>
      myf xs h_nonempty h_sorted (t - xi)
    )).sum
    sum / 6
termination_by Nat.ceil (t / xs.head h_nonempty.1)
decreasing_by
  -- 1. 简化目标
  -- 2. 获取 x0 (即 head)
  let x0 := xs.head h_nonempty.1
  -- 3. 证明 x0 = xs[0]!
  have x0_eq : x0 = xs[0]! := by
    cases xs with
    | nil => exact absurd rfl h_nonempty.1
    | cons h t =>
      -- x0 = h (由 List.head 定义)
      -- xs[0]! = h (列表索引)
      rfl
  -- 4. 证明 x0 > 0
  have x0_pos : x0 > 0 := by
    rw [x0_eq]
    exact h_nonempty.2
  -- 5. 提取 xi（在 decreasing_by 中可用）
  have xi_ge_x0 : xi ≥ x0 := by
    rw [x0_eq]
    apply head_le_of_pairwise_lt h_nonempty.1 h_sorted xi hxi
    -- xi ∈ xs.attach 中的元素，所以 xi ∈ xs
    -- sorry  -- 这需要从 attach 的上下文中提取 membership 证明

  -- 6. 证明 (t - xi) / x0 < t / x0
  -- 目标：Nat.floor ((t - xi) / x0) < Nat.floor (t / x0)

  -- 先证明 t > 0 (从 ht : ¬t ≤ 0 推出)
  have t_pos : t > 0 := by
    push_neg at ht
    exact ht

  -- 证明 (t - xi) / x0 <= (t - x0) / x0 = t / x0 -1
  have h_div_ineq : (t - xi) / x0 ≤ (t - x0) / x0 := by
    -- 因为 xi ≥ x0，所以 -xi ≤ -x0，因此 t - xi ≤ t - x0
    apply div_le_div_of_nonneg_right
    · linarith [xi_ge_x0]
    · linarith [x0_pos]

  -- 证明 (t - x0) / x0 = t / x0 - 1
  have h_div_eq : (t - x0) / x0 = t / x0 - 1 := by
    field_simp [x0_pos.ne']

  -- 结合不等式和等式
  have h_combined : (t - xi) / x0 ≤ t / x0 - 1 := by
    rw [h_div_eq] at h_div_ineq
    exact h_div_ineq

  -- -- 证明严格不等式：(t - xi) / x0 < t / x0
  -- have h_strict : (t - xi) / x0 < t / x0 := by
  --   apply div_lt_div_of_pos_right _ x0_pos
  --   linarith [xi_ge_x0, x0_pos]

  -- 7. 证明 Nat.ceil ((t - xi) / x0) ≤ Nat.ceil (t / x0 - 1)
  have h_ceil_le : Nat.ceil ((t - xi) / x0) ≤ Nat.ceil (t / x0 - 1) := by
    apply Nat.ceil_mono
    exact h_combined

  -- 8. 证明 Nat.ceil (t / x0 - 1) == Nat.ceil (t / x0) - 1, 当 t / x0 > 0 时
  have h_ceil_eq : Nat.ceil (t / x0 - 1) = Nat.ceil (t / x0) - 1 := by
    -- 证明 t / x0 > 0
    -- have h₁ : t / x0 > 0 := div_pos t_pos x0_pos
    -- 使用 Nat.ceil_sub_one
    exact Nat.ceil_sub_one (t / x0)

  -- 9. 证明 Nat.ceil (t / x0) - 1 < Nat.ceil (t / x0)
  have t_div_x0_pos: 0 < t / x0 := div_pos t_pos x0_pos

  have h_ceil_lt : Nat.ceil (t / x0) - 1 < Nat.ceil (t / x0) := by
    -- 先证明 Nat.ceil (t / x0) > 0
    have : Nat.ceil (t / x0) > 0 := Nat.ceil_pos.mpr t_div_x0_pos
    omega
  -- 10. 结合以上结果，得到最终结论
  have final_ineq : Nat.ceil ((t - xi) / x0) < Nat.ceil (t / x0) := by
    calc
      Nat.ceil ((t - xi) / x0)
          ≤ Nat.ceil (t / x0 - 1) := h_ceil_le
      _ = Nat.ceil (t / x0) - 1 := h_ceil_eq
      _ < Nat.ceil (t / x0) := h_ceil_lt
  exact final_ineq

-- ===== 第二部分：证明 myf 等于序列计数公式 =====

-- 辅助引理：严格递增列表没有重复元素
lemma pairwise_lt_nodup {xs : List ℝ} (h_sorted : xs.Pairwise (· < ·)) : xs.Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    rw [List.pairwise_cons] at h_sorted
    rw [List.nodup_cons]
    constructor
    · -- head ∉ tail
      intro h_mem
      -- 如果 head ∈ tail，则由 Pairwise 有 head < head（矛盾）
      have : head < head := h_sorted.1 head h_mem
      linarith
    · -- tail.Nodup
      exact ih h_sorted.2

-- 定义 Y_X(t;m): 长度为 m 的序列集合，满足序列和为 t
def Y_X (xs : List ℝ) (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·)) (t : ℝ) (m : ℕ) : Set (List ℝ) :=
  { seq : List ℝ | seq.length = m ∧
    (∀ y ∈ seq, y ∈ xs) ∧
    seq.sum = t }

-- 辅助引理：序列中每个元素的和至少为序列长度乘以最小元素
lemma sum_ge_length_mul_min (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (seq : List ℝ) (h_mem : ∀ y ∈ seq, y ∈ xs) :
    seq.sum ≥ (seq.length : ℝ) * xs[0]! := by
  induction seq with
  | nil => simp
  | cons head tail ih =>
    simp only [List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    have head_ge : head ≥ xs[0]! := by
      have head_in : head ∈ xs := h_mem head List.mem_cons_self
      exact head_le_of_pairwise_lt h_nonempty.1 h_sorted head head_in
    have tail_mem : ∀ y ∈ tail, y ∈ xs := by
      intro y hy
      exact h_mem y (List.mem_cons_of_mem head hy)
    have ih_apply := ih tail_mem
    nlinarith [head_ge, ih_apply, h_nonempty.2, sq_nonneg (tail.length : ℝ)]

-- 辅助引理：所有元素都是正数的非空列表，其和也是正数
lemma sum_pos_of_all_pos : ∀ (seq : List ℝ), seq ≠ [] → (∀ x ∈ seq, x > 0) → seq.sum > 0 := by
  intro seq h_nonempty h_all_pos
  cases seq with
  | nil => contradiction
  | cons head tail =>
    simp [List.sum_cons]
    have h_head : head > 0 := h_all_pos head List.mem_cons_self
    by_cases h_tail : tail = []
    · rw [h_tail]; simp; exact h_head
    · have h_tail_pos : tail.sum > 0 := by
        apply sum_pos_of_all_pos tail h_tail
        intro x hx
        exact h_all_pos x (List.mem_cons_of_mem head hx)
      linarith

-- Y_X(t;m) 的势（序列个数）
-- 证明有限性：长度为 m 的序列，每个元素从有限集合 xs 中选择，所以只有有限多个
lemma Y_X_finite : ∀ (xs : List ℝ) (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·)) (t : ℝ) (m : ℕ), (Y_X xs h_nonempty h_sorted t m).Finite := by
  intro xs h_nonempty h_sorted t m

  -- 核心思想：Y_X(t;m) ⊆ { 长度为m且元素来自xs的所有序列 }
  -- 后者是有限的（因为xs有限，m固定）

  -- 步骤1：定义包含所有可能序列的集合
  let AllSeqs : Set (List ℝ) := {seq | seq.length = m ∧ ∀ y ∈ seq, y ∈ xs}

  -- 步骤2：Y_X(t;m) 是 AllSeqs 的子集
  have h_subset : Y_X xs h_nonempty h_sorted t m ⊆ AllSeqs := by
    intro seq hseq
    simp [Y_X, AllSeqs] at hseq ⊢
    exact ⟨hseq.1, hseq.2.1⟩

  -- 步骤3：使用归纳法证明 AllSeqs 是有限的
  have h_all_finite : AllSeqs.Finite := by
    clear h_subset t h_nonempty h_sorted

    -- 对 m 归纳
    induction m with
    | zero =>
      -- m = 0: 只有空列表
      suffices AllSeqs = {[]} by rw [this]; exact Set.finite_singleton []
      ext seq
      constructor
      · intro h; simp [AllSeqs] at h; exact h.1
      · intro h; subst h; simp [AllSeqs]

    | succ m ih =>
      -- m = k+1: 使用归纳假设和 xs 的有限性
      -- 关键：所有长度 m+1 的序列可以写成 (长度m的前缀) ++ [xs中的某个元素]

      let AllSeqs_m : Set (List ℝ) := {seq | seq.length = m ∧ ∀ y ∈ seq, y ∈ xs}

      -- 步骤1: 建立映射 f: AllSeqs_m × {x | x ∈ xs} → AllSeqs
      -- f(prefix, x) = prefix ++ [x]
      let f : List ℝ × ℝ → List ℝ := fun p => p.1 ++ [p.2]

      -- 步骤2: 证明 AllSeqs ⊆ f '' (AllSeqs_m ×ˢ {x | x ∈ xs})
      have h_subset_image : AllSeqs ⊆ f '' (AllSeqs_m ×ˢ {x | x ∈ xs}) := by
        intro seq ⟨h_len, h_mem⟩
        by_cases h : seq = []
        · subst h; simp at h_len
        · -- seq 非空，可以分解为 dropLast ++ [getLast]
          use (seq.dropLast, seq.getLast h)
          constructor
          · simp [Set.mem_prod, AllSeqs_m]
            constructor
            · constructor
              · simp [h_len]
              · intro y hy
                apply h_mem
                rw [← List.dropLast_append_getLast h]
                simp [hy]
            · apply h_mem
              exact List.getLast_mem h
          · simp [f]
            exact List.dropLast_append_getLast h

      -- 步骤3: 证明 f '' (AllSeqs_m ×ˢ {x | x ∈ xs}) 是有限的
      have h_image_finite : (f '' (AllSeqs_m ×ˢ {x | x ∈ xs})).Finite := by
        apply Set.Finite.image
        apply Set.Finite.prod
        · exact ih
        · have : {x : ℝ | x ∈ xs} = ↑xs.toFinset := by ext x; simp
          rw [this]
          exact xs.toFinset.finite_toSet

      -- 步骤4: 有限集的子集是有限的
      exact h_image_finite.subset h_subset_image

  -- 步骤4：有限集的子集也是有限的
  exact h_all_finite.subset h_subset

noncomputable def card_Y_X (xs : List ℝ) (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·)) (t : ℝ) (m : ℕ) : ℕ :=
  (Y_X_finite xs h_nonempty h_sorted t m).toFinset.card

-- 序列长度上界引理
lemma Y_X_length_bound (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) (m : ℕ) :
    Y_X xs h_nonempty h_sorted t m ≠ ∅ → m ≤ Nat.ceil (t / xs[0]!) := by
  intro h_nempty
  -- 若存在序列 seq ∈ Y_X(t;m)，则 seq.sum = t
  -- 由于每个元素 ≥ xs[0]!，故 m * xs[0]! ≤ t
  -- 因此 m ≤ ceil(t / xs[0]!)

  -- 从非空性得到存在某个序列
  have : ∃ seq, seq ∈ Y_X xs h_nonempty h_sorted t m := by
    by_contra h_contra
    push_neg at h_contra
    have : Y_X xs h_nonempty h_sorted t m = ∅ := by
      ext seq; simp [h_contra]
    exact h_nempty this

  obtain ⟨seq, hseq⟩ := this
  simp [Y_X] at hseq
  obtain ⟨h_len, h_mem, h_sum⟩ := hseq

  -- 应用辅助引理：seq.sum ≥ seq.length * xs[0]!
  have h_sum_bound := sum_ge_length_mul_min xs h_nonempty h_sorted seq h_mem

  -- 结合 seq.sum = t 和 seq.length = m
  have h_m_bound : (m : ℝ) * xs[0]! ≤ t := by
    calc (m : ℝ) * xs[0]! = (seq.length : ℝ) * xs[0]! := by rw [h_len]
       _ ≤ seq.sum := h_sum_bound
       _ = t := h_sum

  -- 因此 m ≤ t / xs[0]!
  have x₀_pos : xs[0]! > 0 := h_nonempty.2
  have h_m_div : (m : ℝ) ≤ t / xs[0]! := by
    rw [le_div_iff₀']
    · calc xs[0]! * (m : ℝ) = (m : ℝ) * xs[0]! := mul_comm _ _
         _ ≤ t := h_m_bound
    · exact x₀_pos

  calc m = Nat.floor (m : ℝ) := by simp
     _ ≤ Nat.floor (t / xs[0]!) := Nat.floor_mono h_m_div
     _ ≤ Nat.ceil (t / xs[0]!) := Nat.floor_le_ceil _-- 有限和性质：当 m 超过某个界限时，Y_X(t;m) = ∅

lemma Y_X_vanish_large_m (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) (_ht : t > 0) :
    ∃ M : ℕ, ∀ m > M, Y_X xs h_nonempty h_sorted t m = ∅ := by
  use Nat.ceil (t / xs[0]!)
  intro m hm
  by_contra h_nempty
  have := Y_X_length_bound xs h_nonempty h_sorted t m h_nempty
  omega

-- 一一对应引理：序列末尾添加元素建立双射
lemma bijection_append (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·)) (t : ℝ) (m : ℕ) :
    card_Y_X xs h_nonempty h_sorted t (m + 1) =
    (xs.attach.map (fun ⟨xi, _⟩ =>
      card_Y_X xs h_nonempty h_sorted (t - xi) m
    )).sum := by
  -- 证明思路：
  -- 1. 定义映射 φ_{i,m}: Y_X(t-xi;m) → Y_X(t;m+1)
  --    φ_{i,m}(seq) = seq ++ [xi]
  --
  -- 2. 证明 φ_{i,m} 是单射：
  --    若 seq1 ++ [xi] = seq2 ++ [xi]，则 seq1 = seq2
  --
  --
  -- 3. 证明满射：
  --    对任意 seq' ∈ Y_X(t;m+1)，设末尾元素为 xi
  --    则 seq' = (前m个元素) ++ [xi]
  --    且前m个元素 ∈ Y_X(t-xi;m)
  --
  -- 4. 由双射性质得：
  --    |Y_X(t;m+1)| = Σ_{xi∈xs, t-xi≥0} |Y_X(t-xi;m)|

  -- 关键思路：Y_X(t;m+1) 中的每个序列可以唯一地分解为：
  -- 前m个元素（和为 t-xi）+ 最后一个元素 xi
  -- 这建立了 Y_X(t;m+1) 与 ⊎_{xi∈xs} Y_X(t-xi;m) 的双射

  unfold card_Y_X

  -- 核心想法：通过列表的分解-组合建立双射
  -- 分解：seq ↦ (dropLast seq, getLast seq)
  -- 组合：(prefix, xi) ↦ prefix ++ [xi]

  -- 由于完整的双射证明涉及 Finset 的复杂操作，
  -- 这里给出证明框架的关键步骤

  -- 关键性质1: 每个长度为 m+1 的序列都可以分解
  have decompose_exists : ∀ seq, seq ∈ Y_X xs h_nonempty h_sorted t (m + 1) →
    seq ≠ [] := by
    intro seq hseq
    simp [Y_X] at hseq
    intro h
    rw [h] at hseq
    simp at hseq

  -- 关键性质2: 分解后的部分满足条件
  have decompose_property : ∀ seq (hseq : seq ∈ Y_X xs h_nonempty h_sorted t (m + 1)) (hne : seq ≠ []),
    seq.getLast hne ∈ xs ∧
    seq.dropLast ∈ Y_X xs h_nonempty h_sorted (t - seq.getLast hne) m := by
    intro seq hseq hne
    simp [Y_X] at hseq ⊢
    obtain ⟨h_len, h_mem, h_sum⟩ := hseq
    constructor
    · apply h_mem; exact List.getLast_mem hne
    constructor
    · simp [h_len]
    constructor
    · intro y hy
      apply h_mem
      rw [← List.dropLast_append_getLast hne]
      simp [hy]
    · have h_eq : (seq.dropLast ++ [seq.getLast hne]).sum = t := by
        rw [List.dropLast_append_getLast hne]; exact h_sum
      simp at h_eq
      linarith

  -- 利用 decompose_exists 和 decompose_property 建立证明
  --
  -- 核心思想：通过 dropLast 和 getLast 建立双射
  -- Y_X(t;m+1) ≃ ⊎_{xi∈xs} Y_X(t-xi;m)

  -- 关键优化：直接使用 Finset，因为我们已知所有集合都是有限的

  -- 首先将 Y_X(t;m+1) 转换为 Finset
  have h_Y_finite := Y_X_finite xs h_nonempty h_sorted t (m + 1)
  let Y_finset := h_Y_finite.toFinset

  -- 步骤1: 定义按最后元素分组的 Finset
  -- 对每个 xi ∈ xs，定义 S_finset(xi) 为以 xi 结尾的序列
  let S_finset (xi : ℝ) : Finset (List ℝ) :=
    Y_finset.filter (fun seq =>
      if h : seq ≠ [] then seq.getLast h = xi else False)

  -- 步骤2: 对每个 xi，定义 V_finset(xi) = Y_X(t-xi; m) 的 Finset
  let V_finset (xi : ℝ) : Finset (List ℝ) :=
    (Y_X_finite xs h_nonempty h_sorted (t - xi) m).toFinset

  -- 步骤3: 证明对每个 xi，S_finset(xi) 和 V_finset(xi) 的基数相等
  -- 这通过建立双射来完成：
  --   f: S_finset(xi) → V_finset(xi), f(seq) = seq.dropLast
  -- 步骤3: 证明对每个 xi，S_finset(xi) 和 V_finset(xi) 的基数相等
  -- 这通过建立双射来完成：
  --   f: S_finset(xi) → V_finset(xi), f(seq) = seq.dropLast
  --   g: V_finset(xi) → S_finset(xi), g(pre) = pre ++ [xi]
  have h_card_eq : ∀ xi ∈ xs,
    (S_finset xi).card = (V_finset xi).card := by
    intro xi hxi
    simp only [V_finset]
    -- 证明 S_finset(xi) = image (·++[xi]) V_finset(xi)
    have h_bij : S_finset xi = Finset.image (fun pre => pre ++ [xi])
        ((Y_X_finite xs h_nonempty h_sorted (t - xi) m).toFinset) := by
      ext seq
      simp [S_finset, Y_finset, Set.Finite.mem_toFinset, Finset.mem_image]
      constructor
      · intro ⟨hseq, hne, heq_last⟩
        -- seq ∈ S_finset(xi) 意味着 seq.getLast = xi
        -- 所以 seq = seq.dropLast ++ [xi]
        use seq.dropLast
        constructor
        · -- seq.dropLast ∈ Y_X(t-xi; m)
          have ⟨_, hdrop⟩ := decompose_property seq hseq hne
          rw [← heq_last]
          exact hdrop
        · -- seq = seq.dropLast ++ [xi]
          rw [← heq_last]
          exact List.dropLast_append_getLast hne
      · intro ⟨pre, hpre, heq⟩
        -- 如果 seq = pre ++ [xi]，证明 seq ∈ S_finset(xi)
        rw [← heq]
        refine ⟨?_, ?_, ?_⟩
        · -- pre ++ [xi] ∈ Y_X(t; m+1)
          simp [Y_X] at hpre ⊢
          obtain ⟨hlen, hmem, hsum⟩ := hpre
          constructor
          · simp [hlen]
          constructor
          · intro y hy
            cases hy with
            | inl h => exact hmem y h
            | inr h => rw [h]; exact hxi
          · simp [hsum]
        · simp
        · have : (pre ++ [xi]).getLast (by simp : pre ++ [xi] ≠ []) = xi := by
            cases pre <;> simp
          exact this
    -- 利用单射性得到基数相等
    calc (S_finset xi).card
        = (Finset.image (fun pre => pre ++ [xi])
            ((Y_X_finite xs h_nonempty h_sorted (t - xi) m).toFinset)).card := by rw [h_bij]
      _ = ((Y_X_finite xs h_nonempty h_sorted (t - xi) m).toFinset).card := by
          apply Finset.card_image_of_injective
          intro p1 p2 heq
          exact (List.append_left_inj [xi]).mp heq

  -- 步骤4: 证明 S_finset(xi) 对不同的 xi 是不相交的
  have h_disjoint : ∀ xi1 ∈ xs, ∀ xi2 ∈ xs, xi1 ≠ xi2 →
    Disjoint (S_finset xi1) (S_finset xi2) := by
    intro xi1 hxi1 xi2 hxi2 hne_xi
    rw [Finset.disjoint_iff_ne]
    intro seq1 h1 seq2 h2
    simp [S_finset, Y_finset] at h1 h2
    intro heq
    subst heq
    obtain ⟨_, hne1, heq1⟩ := h1
    obtain ⟨_, hne2, heq2⟩ := h2
    apply hne_xi
    calc xi1 = seq1.getLast hne1 := heq1.symm
         _ = seq1.getLast hne2 := rfl
         _ = xi2 := heq2

  -- 步骤5: 证明 Y_finset 等于所有 S_finset(xi) 的并集
  have h_cover : Y_finset = Finset.biUnion xs.toFinset (fun xi => S_finset xi) := by
    ext seq
    simp only [Y_finset, S_finset, Set.Finite.mem_toFinset, Finset.mem_biUnion, Finset.mem_filter]
    refine ⟨fun hseq => ?_, fun h => ?_⟩
    · have hne := decompose_exists seq hseq
      have ⟨hlast_in, _⟩ := decompose_property seq hseq hne
      use seq.getLast hne, List.mem_toFinset.mpr hlast_in, hseq
      simp [hne]
    · obtain ⟨xi, hxi_in, hseq, hcond⟩ := h
      exact hseq

  -- 步骤6: 应用 Finset.card_biUnion 得到基数公式
  have h_card : Y_finset.card =
    (xs.toFinset.biUnion (fun xi => S_finset xi)).card := by
    rw [h_cover]

  -- 步骤7: 由于不相交，使用 Finset.card_biUnion
  have h_card_sum : Y_finset.card =
    (xs.toFinset.sum (fun xi => (S_finset xi).card)) := by
    rw [h_card]
    apply Finset.card_biUnion
    intro xi hxi xj hxj hne
    exact h_disjoint xi (List.mem_toFinset.mp hxi) xj (List.mem_toFinset.mp hxj) hne

  -- 步骤8: 将 S_finset 的基数替换为 V_finset 的基数
  have h_sum_eq : xs.toFinset.sum (fun xi => (S_finset xi).card) =
    xs.toFinset.sum (fun xi => (V_finset xi).card) := by
    apply Finset.sum_congr rfl
    intro xi hxi
    exact h_card_eq xi (List.mem_toFinset.mp hxi)

  -- 步骤8: 将 S_finset 的基数替换为 V_finset 的基数
  have h_sum_eq : xs.toFinset.sum (fun xi => (S_finset xi).card) =
    xs.toFinset.sum (fun xi => (V_finset xi).card) := by
    apply Finset.sum_congr rfl
    intro xi hxi
    exact h_card_eq xi (List.mem_toFinset.mp hxi)

  -- 步骤9: 将结果转换回 List.sum 的形式
  -- 利用 xs.Nodup 来建立 Finset.sum 和 List.sum 的等价性
  -- 步骤10: 完成证明
  calc Y_finset.card
      = xs.toFinset.sum (fun xi => (S_finset xi).card) := by rw [h_card_sum]
    _ = xs.toFinset.sum (fun xi => (V_finset xi).card) := h_sum_eq
    _ = (xs.attach.map (fun ⟨xi, _⟩ =>
          card_Y_X xs h_nonempty h_sorted (t - xi) m)).sum := by
      -- 关键：利用 xs.Nodup 使得 xs.toFinset 和 xs 一一对应
      have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted
      -- attach.map 等价于 map
      have h_expand : (xs.attach.map (fun ⟨xi, _⟩ =>
            card_Y_X xs h_nonempty h_sorted (t - xi) m)).sum =
          (xs.map (fun xi => card_Y_X xs h_nonempty h_sorted (t - xi) m)).sum := by
        simp only [List.attach, List.attachWith]
        rw [List.map_pmap]
        simp
      rw [h_expand]
      -- 使用 List.sum_toFinset 配合 Nodup
      symm
      rw [← List.sum_toFinset _ h_nodup]
      -- 最后一步：两边已经相等（V_finset 的定义就是 card_Y_X）
      simp only [V_finset, card_Y_X]
  --

-- 主定理：myf 等于序列计数求和公式
-- 使用第二数学归纳法：对 n ∈ ℕ 归纳证明 ∀ t ≤ n·x₀，定理成立
theorem myf_eq_sequence_count (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) :
    myf xs h_nonempty h_sorted t =
    ∑' m : ℕ, (card_Y_X xs h_nonempty h_sorted t m : ℝ) / (6 : ℝ) ^ m := by
  -- 证明策略：对 n ∈ ℕ 进行第一数学归纳
  -- 归纳命题 P(n): 对所有 t ≤ n·x₀，定理成立
  --
  -- 1. base: n=0 => t ≤ 0，在框架内证明
  -- 2. 递推：假设 n=k 成立（t ≤ k·x₀ 时成立），
  --          证明 k·x₀ < t ≤ (k+1)·x₀ 也成立
  --          从而 t ≤ (k+1)·x₀ 均成立，推出 n=k+1 成立
  --
  -- 数学归纳法涵盖所有 t ∈ ℝ：对任意 t，取 n = ⌈t/x₀⌉，则 t ≤ n·x₀

  let x₀ := xs[0]!

  -- 对任意 t，找到最小的 n 使得 t ≤ n·x₀
  let n := Nat.ceil (t / x₀)

  -- 证明 t ≤ n·x₀
  have ht_le : t ≤ (n : ℝ) * x₀ := by
    have x₀_pos : x₀ > 0 := h_nonempty.2
    have : (t / x₀ : ℝ) ≤ (n : ℝ) := Nat.le_ceil (t / x₀)
    calc t = (t / x₀) * x₀ := by field_simp
         _ ≤ (n : ℝ) * x₀ := by apply mul_le_mul_of_nonneg_right; exact this; linarith

  -- 对 k 进行第一数学归纳
  -- 归纳命题：∀ s ≤ k·x₀，定理成立
  suffices h_strong : ∀ k : ℕ, ∀ s, s ≤ (k : ℝ) * x₀ →
    myf xs h_nonempty h_sorted s = ∑' m, (card_Y_X xs h_nonempty h_sorted s m : ℝ) / 6 ^ m by
    exact h_strong n t ht_le

  intro k
  induction k with
  | zero =>
    -- ========== 基础情况：n = 0 ==========
    -- 要证明：∀ s ≤ 0·x₀ = 0，定理成立
    intro s hs
    have hs_nonpos : s ≤ 0 := by simp at hs; exact hs

    -- 分两种情况：s = 0 和 s < 0
    by_cases h_zero : s = 0
    · -- 情况 1: s = 0
      rw [h_zero]
      rw [myf]
      simp
      -- 此时 myf(0) = 1
      -- 需要证明 ∑' m, card_Y_X(0;m) / 6^m = 1
      -- 仅当 m=0 时 Y_X(0;0) = {[]} 非空，card = 1
      -- 其他 m > 0 时，Y_X(0;m) = ∅
      have h0 : card_Y_X xs h_nonempty h_sorted 0 0 = 1 := by
        unfold card_Y_X
        have h_eq : Y_X xs h_nonempty h_sorted 0 0 = {[]} := by
          ext seq
          simp [Y_X]
          cases seq with
          | nil => simp
          | cons h t => simp
        have h_finite : ({[]} : Set (List ℝ)).Finite := by
          rw [← h_eq]; exact Y_X_finite xs h_nonempty h_sorted 0 0
        calc (Y_X_finite xs h_nonempty h_sorted 0 0).toFinset.card
            = (h_finite).toFinset.card := by
              simp [Set.Finite.toFinset, h_eq]
          _ = 1 := by simp [Set.Finite.toFinset]
      have hm : ∀ m > 0, card_Y_X xs h_nonempty h_sorted 0 m = 0 := by
        intro m hm_pos
        unfold card_Y_X
        have h_empty : Y_X xs h_nonempty h_sorted 0 m = ∅ := by
          ext seq
          simp [Y_X]
          intro h_len h_mem h_sum
          have h_seq_nonempty : seq ≠ [] := by
            intro h_eq; rw [h_eq] at h_len; simp at h_len; omega
          have h_all_pos : ∀ x ∈ xs, x > 0 := by
            intro x hx
            have : xs[0]! ≤ x := head_le_of_pairwise_lt h_nonempty.1 h_sorted x hx
            linarith [h_nonempty.2]
          have h_seq_all_pos : ∀ y ∈ seq, y > 0 := by
            intro y hy; exact h_all_pos y (h_mem y hy)
          have h_sum_pos : seq.sum > 0 := sum_pos_of_all_pos seq h_seq_nonempty h_seq_all_pos
          rw [h_sum] at h_sum_pos; linarith
        calc (Y_X_finite xs h_nonempty h_sorted 0 m).toFinset.card
            = Finset.card (Set.Finite.toFinset (Y_X_finite xs h_nonempty h_sorted 0 m)) := rfl
          _ = 0 := by
            have : (Y_X_finite xs h_nonempty h_sorted 0 m).toFinset = ∅ := by
              ext seq; simp [h_empty]
            rw [this]; rfl
      have sum_eq : ∑' m, (card_Y_X xs h_nonempty h_sorted 0 m : ℝ) / 6 ^ m = 1 := by
        have h_tsum : ∑' m, (card_Y_X xs h_nonempty h_sorted 0 m : ℝ) / 6 ^ m = (card_Y_X xs h_nonempty h_sorted 0 0 : ℝ) / 6 ^ 0 := by
          apply tsum_eq_single 0
          intro m hm_ne
          by_cases h : m > 0
          · rw [hm m h]; simp
          · omega
        rw [h_tsum, h0]; norm_num
      exact sum_eq.symm

    · -- 情况 2: s < 0
      have hs_neg : s < 0 := by
        cases' hs_nonpos.lt_or_eq with h h
        · exact h
        · exfalso; exact h_zero h

      -- myf(s) = 0 when s < 0
      rw [myf]
      simp
      -- 当 s < 0 时，myf 的定义给出 if s < 0 then 0
      split
      · -- 需要证明 0 = ∑' m, card_Y_X(s;m) / 6^m
        -- 因为 s < 0 且 xs 全为正数，Y_X(s;m) = ∅ 对所有 m
        have h_all_empty : ∀ m, card_Y_X xs h_nonempty h_sorted s m = 0 := by
          intro m
          unfold card_Y_X
          have h_empty : Y_X xs h_nonempty h_sorted s m = ∅ := by
            ext seq
            simp [Y_X]
            intro h_len h_mem h_sum
            cases seq with
            | nil =>
              simp at h_sum; linarith [hs_neg, h_sum]
            | cons head tail =>
              have h_all_pos : ∀ x ∈ xs, x > 0 := by
                intro x hx
                have : xs[0]! ≤ x := head_le_of_pairwise_lt h_nonempty.1 h_sorted x hx
                linarith [h_nonempty.2]
              have h_seq_all_pos : ∀ y ∈ (head :: tail), y > 0 := by
                intro y hy; exact h_all_pos y (h_mem y hy)
              have h_sum_pos : (head :: tail).sum > 0 := by
                apply sum_pos_of_all_pos
                · simp
                · exact h_seq_all_pos
              rw [h_sum] at h_sum_pos; linarith [hs_neg]
          have h_finite_empty : (∅ : Set (List ℝ)).Finite := by simp
          calc (Y_X_finite xs h_nonempty h_sorted s m).toFinset.card
              = (h_finite_empty).toFinset.card := by
                congr 1; ext x; simp [Set.Finite.toFinset, h_empty]
            _ = 0 := by simp [Set.Finite.toFinset]
        simp [h_all_empty]
      · -- 矛盾：已知 s < 0
        linarith

  | succ k ih_k =>
    -- ========== 归纳步骤：n = k → n = k+1 ==========
    -- 归纳假设 ih_k: ∀ s ≤ k·x₀，定理对 s 成立
    -- 要证明：∀ s ≤ (k+1)·x₀，定理对 s 成立

    intro s hs
    -- s ≤ (k+1)·x₀
    by_cases h_case : s ≤ (k : ℝ) * x₀

    · -- 情况1: s ≤ k·x₀
      -- 直接应用归纳假设
      exact ih_k s h_case

    · -- 情况2: k·x₀ < s ≤ (k+1)·x₀
      -- 这是归纳的核心：使用 myf 的递推性质
      push_neg at h_case
      have hs_interval : (k : ℝ) * x₀ < s ∧ s ≤ ((k : ℝ) + 1) * x₀ := by
        constructor
        · exact h_case
        · calc s ≤ ↑(k + 1) * x₀ := hs
               _ = (↑k + 1) * x₀ := by norm_cast

      -- 证明目标：myf(s) = ∑' m, card_Y_X(s;m) / 6^m
      -- 根据 myf 的定义展开 myf(s) = (∑_{xi ∈ xs} myf(s - xi)) / 6

      -- Step 1: 证明 s > 0 并对每个 xi ∈ xs，证明s - xi ≤ k·x₀
      have s_pos : s > 0 := by
        calc s > (k : ℝ) * x₀ := hs_interval.1
             _ ≥ 0 := by apply mul_nonneg; exact Nat.cast_nonneg k; linarith [h_nonempty.2]

      have h_sub_le : ∀ xi ∈ xs, s - xi ≤ (k : ℝ) * x₀ := by
        intro xi hxi
        have xi_ge_x₀ : xi ≥ x₀ := by
          apply head_le_of_pairwise_lt h_nonempty.1 h_sorted xi hxi
        calc s - xi ≤ s - x₀ := by linarith [xi_ge_x₀]
             _ ≤ ((k : ℝ) + 1) * x₀ - x₀ := by linarith [hs_interval.2]
             _ = (k : ℝ) * x₀ := by ring

      -- 应用归纳假设到每个 myf(s - xi)
      have h_ih_apply : ∀ xi ∈ xs,
        myf xs h_nonempty h_sorted (s - xi) =
        ∑' m, (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m := by
        intro xi hxi
        apply ih_k
        exact h_sub_le xi hxi

      -- 展开 myf(s) 的递推定义
      rw [myf]
      have hs_not_le : ¬(s ≤ 0) := by linarith [s_pos]
      simp only [hs_not_le]

      -- #check List.attach
      -- #check list_sum_eq_finset_sum_attach
      -- 替换 myf(s - xi) 为归纳假设 IH
      -- have h_ih_applied :
      --     (List.map (fun x => myf xs h_nonempty h_sorted (s - x)) xs).sum =
      --     (xs.attach.map (fun x => myf xs h_nonempty h_sorted (s - x)) ).sum := by
      --   simp [List.attach, List.attachWith]
        -- apply congr rfl

        -- apply h_ih_apply
        -- intro ⟨xi, hxi⟩ h_mem_attach
        -- -- 证明 s - xi < s，且对 t' = s - xi 满足 IH
        -- -- 这里的证明依赖于 myf 的终止性结构 (t - x < t)，且 IH 成立
        -- -- 对于 t - xi ≤ 0 的情况，IH 仍然成立（基例）
        -- sorry

      -- Step 2: 证明根据Y_X_length_bound或Y_X_vanish_large_m引理，只有有限个m使得card_Y_X非零
      -- 从而证明∑' m, (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m是有限和

      -- 对每个 xi ∈ xs，s - xi 可能为负或非负
      -- 如果 s - xi ≤ 0，则所有 Y_X(s-xi;m) = ∅（因为序列和必须为正）
      -- 如果 s - xi > 0，则由 Y_X_vanish_large_m，存在 M 使得 m > M 时 Y_X(s-xi;m) = ∅
      have h_finite_support : ∀ xi ∈ xs, ∃ M : ℕ, ∀ m > M,
          card_Y_X xs h_nonempty h_sorted (s - xi) m = 0 := by
        intro xi hxi
        by_cases h_pos_diff : s - xi > 0
        · -- s - xi > 0 的情况，应用 Y_X_vanish_large_m
          obtain ⟨M, hM⟩ := Y_X_vanish_large_m xs h_nonempty h_sorted (s - xi) h_pos_diff
          use M
          intro m hm
          rw [card_Y_X]
          simp [hM m hm]
        · -- s - xi ≤ 0 的情况，所有 m 都有 Y_X(s-xi;m) = ∅
          push_neg at h_pos_diff
          use 0
          intro m _
          rw [card_Y_X]
          have h_empty : Y_X xs h_nonempty h_sorted (s - xi) m = ∅ := by
            ext seq
            simp [Y_X]
            intro h_len h_mem h_sum
            -- 矛盾：seq.sum = s - xi ≤ 0，但所有元素 > 0
            have h_all_pos : ∀ y ∈ seq, y > 0 := by
              intro y hy
              have : xs[0]! ≤ y := by
                have y_in_xs := h_mem y hy
                exact head_le_of_pairwise_lt h_nonempty.1 h_sorted y y_in_xs
              linarith [h_nonempty.2]
            -- seq 非空时导出矛盾
            obtain ⟨_, _⟩ | ⟨head, tail⟩ := seq
            · -- seq = [] 的情况：长度为 m 但必须 m = 0
              simp at h_len
              omega
            · -- seq = head :: tail 的情况
              have h_sum_pos : (head :: tail).sum > 0 := by
                apply sum_pos_of_all_pos
                · simp
                · exact h_all_pos
              linarith [h_sum, h_pos_diff]
          simp [h_empty]

      -- Step 3: 交换有限和与有限和的顺序
      -- 由于 h_finite_support 保证了每个 ∑' m 实际上是有限和，可以直接交换求和顺序

      -- 完整的证明路径：
      -- 当前目标：证明 (xs.attach.map (fun ⟨xi, _⟩ => myf(s-xi))).sum / 6 = ∑' m, card_Y_X(s;m) / 6^m
      --
      -- Step 3a: 将每个 myf(s-xi) 替换为 ∑' m, card_Y_X(s-xi;m) / 6^m （使用 h_ih_apply）
      -- Step 3b: 交换有限和顺序：(∑_{xi} (∑' m, ...)) / 6 = ∑' m, (∑_{xi} ...) / 6^(m+1)
      -- Step 4: 应用 bijection_append：∑_{xi} card_Y_X(s-xi;m) = card_Y_X(s;m+1)
      -- Step 5: 调整指标：∑' m, card_Y_X(s;m+1) / 6^(m+1) = ∑' m, card_Y_X(s;m) / 6^m

      -- Step 3a: 应用归纳假设替换每个 myf(s-xi)
      have h_replace_ih : ∀ xi ∈ xs.attach,
          myf xs h_nonempty h_sorted (s - xi.val) =
          ∑' m, (card_Y_X xs h_nonempty h_sorted (s - xi.val) m : ℝ) / 6 ^ m := by
        intro ⟨xi, hxi⟩ _
        exact h_ih_apply xi hxi

      -- 当前目标形式：(xs.attach.map (fun ⟨xi, _⟩ => myf(s-xi))).sum / 6
      -- 目标形式：∑' m, card_Y_X(s;m) / 6^m

      -- Step 3b: 交换求和顺序（有限和与有限和）
      -- 由于每个级数有有限支撑（h_finite_support），可以将其视为有限和并交换顺序

      -- 找到一个统一的上界 M，使得：
      -- 1. 对所有 xi ∈ xs，当 m > M 时 card_Y_X(s-xi;m) = 0
      -- 2. 当 m > M 时 card_Y_X(s;m) = 0
      -- 这样左边和右边的有限和范围可以一致
      have h_uniform_bound : ∃ M : ℕ,
          (∀ xi ∈ xs, ∀ m > M, card_Y_X xs h_nonempty h_sorted (s - xi) m = 0) ∧
          (∀ m > M, card_Y_X xs h_nonempty h_sorted s m = 0) := by
        -- 取 M = ⌈s / xs[0]!⌉，这对两者都适用
        use Nat.ceil (s / xs[0]!)
        constructor
        · -- 证明对所有 xi ∈ xs，m > M 时 card_Y_X(s-xi;m) = 0
          intro xi hxi m hm
          obtain ⟨M_xi, hM_xi⟩ := h_finite_support xi hxi
          by_cases h_case : m > M_xi
          · exact hM_xi m h_case
          · push_neg at h_case
            by_contra h_nonzero
            have h_nonempty_set : Y_X xs h_nonempty h_sorted (s - xi) m ≠ ∅ := by
              rw [card_Y_X] at h_nonzero
              intro h_contra
              simp [h_contra] at h_nonzero
            have h_bound := Y_X_length_bound xs h_nonempty h_sorted (s - xi) m h_nonempty_set
            have : m ≤ Nat.ceil (s / xs[0]!) := by
              have xi_pos : xi > 0 := by
                have : xs[0]! ≤ xi := head_le_of_pairwise_lt h_nonempty.1 h_sorted xi hxi
                linarith [h_nonempty.2]
              calc m ≤ Nat.ceil ((s - xi) / xs[0]!) := h_bound
                   _ ≤ Nat.ceil (s / xs[0]!) := by
                     apply Nat.ceil_mono
                     apply div_le_div_of_nonneg_right _ (by linarith [h_nonempty.2])
                     linarith [xi_pos]
            omega
        · -- 证明 m > M 时 card_Y_X(s;m) = 0
          intro m hm
          rw [card_Y_X]
          have h_empty : Y_X xs h_nonempty h_sorted s m = ∅ := by
            by_contra h_nempty
            have h_bound := Y_X_length_bound xs h_nonempty h_sorted s m h_nempty
            omega
          simp [h_empty]

      obtain ⟨M, hM, hM_s⟩ := h_uniform_bound

      -- 利用有限支撑，将无穷级数转换为有限和
      -- 对每个 xi ∈ xs，∑' m, card_Y_X(s-xi;m) / 6^m = ∑_{m=0}^M card_Y_X(s-xi;m) / 6^m
      have h_tsum_eq_sum : ∀ xi ∈ xs,
          ∑' m, (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m =
          ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m := by
        intro xi hxi
        apply tsum_eq_sum
        intro m hm
        simp at hm
        -- m ∉ range(M+1) 意味着 m > M
        have : m > M := by omega
        have h_zero := hM xi hxi m this
        simp [h_zero]

      -- 同样，对 s 本身：∑' m, card_Y_X(s;m) / 6^m = ∑_{m=0}^M card_Y_X(s;m) / 6^m
      have h_tsum_eq_sum_s : ∑' m, (card_Y_X xs h_nonempty h_sorted s m : ℝ) / 6 ^ m =
          ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted s m : ℝ) / 6 ^ m := by
        apply tsum_eq_sum
        intro m hm
        simp at hm
        have : m > M := by omega
        have h_zero := hM_s m this
        simp [h_zero]

      -- 简化左边：先将 attach.map 转换为 map
      have h_map_eq : (xs.attach.map (fun ⟨xi, _⟩ => myf xs h_nonempty h_sorted (s - xi))).sum =
          (xs.map (fun xi => myf xs h_nonempty h_sorted (s - xi))).sum := by
        simp only [List.attach, List.attachWith]
        rw [List.map_pmap]
        simp

      rw [h_map_eq]

      -- 将每个 myf(s-xi) 替换为有限和
      -- 简化方法：直接在和式中应用变换
      have h_step1 : (xs.map (fun xi => myf xs h_nonempty h_sorted (s - xi))).sum / 6 =
          (xs.map (fun xi =>
            ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum / 6 := by
        congr 1
        -- 使用 List.map_congr_left 证明两个 map 相等
        congr 1
        apply List.map_congr_left
        intro xi hxi
        rw [h_ih_apply xi hxi]
        exact h_tsum_eq_sum xi hxi

      rw [h_step1]

      -- 交换有限和的顺序：∑_{xi} (∑_{m} ...) = ∑_{m} (∑_{xi} ...)
      have h_step3 : (xs.map (fun xi =>
            ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum =
          ∑ m ∈ Finset.range (M + 1),
            (xs.map (fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum := by
        have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted
        -- 将 xs.map f 改写为 xs.attach.map
        have h_left : (xs.map (fun xi =>
              ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum =
            (xs.attach.map (fun ⟨xi, _⟩ =>
              ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum := by
          simp only [List.attach, List.attachWith, List.map_pmap]
          simp
        rw [h_left]
        -- 转换为 Finset.sum
        rw [← List.sum_toFinset _ (List.nodup_attach.mpr h_nodup)]
        -- 右边也类似处理，先证明求和函数相等
        have h_sum_eq : ∀ m, (xs.map (fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum =
            (xs.attach.toFinset.sum (fun ⟨xi, _⟩ => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)) := by
          intro m
          have h_right : (xs.map (fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum =
              (xs.attach.map (fun ⟨xi, _⟩ => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m)).sum := by
            simp only [List.attach, List.attachWith, List.map_pmap]
            simp
          rw [h_right]
          rw [← List.sum_toFinset _ (List.nodup_attach.mpr h_nodup)]
        simp_rw [h_sum_eq]
        -- 使用 Finset.sum_comm
        rw [← Finset.sum_comm]

      rw [h_step3]
      simp

      -- Step 4: 应用 bijection_append
      -- 目标：(∑ m ∈ range(M+1), (∑ xi ∈ xs, card_Y_X(s-xi,m) / 6^m)) / 6 = ∑' m, card_Y_X(s,m) / 6^m

      -- 首先建立一个辅助引理：对每个 m，∑_{xi} card_Y_X(s-xi,m) = card_Y_X(s,m+1)
      have h_bij_step : ∀ m, (xs.map fun xi => card_Y_X xs h_nonempty h_sorted (s - xi) m).sum =
          card_Y_X xs h_nonempty h_sorted s (m + 1) := by
        intro m
        have h_bij := bijection_append xs h_nonempty h_sorted s m
        -- bijection_append 给出：card_Y_X(s,m+1) = (xs.attach.map ...).sum
        -- 需要证明 (xs.map ...).sum = card_Y_X(s,m+1)
        rw [h_bij]
        -- List.attach.map 和 List.map 的关系
        simp only [List.attach, List.attachWith]
        rw [List.map_pmap]
        simp

      -- 现在我们有了 h_bij_step，可以转换每一项
      -- 目标：(∑ m, (∑ xi, card_Y_X(s-xi,m) / 6^m)) / 6 = ∑' m, card_Y_X(s,m) / 6^m

      -- 先将 / 6 移入求和符号
      rw [Finset.sum_div]

      -- 引入 h_nodup 以便后续使用
      have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted

      -- 将 List.map.sum 转换为 Finset.sum 并应用 h_bij_step
      have h_step4 : ∑ m ∈ Finset.range (M + 1),
          (xs.map fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m).sum / 6 =
          ∑ m ∈ Finset.range (M + 1), (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) / 6 ^ (m + 1) := by
        -- 策略：对每个 m，证明单项相等
        refine Finset.sum_congr rfl fun m _ => ?_

        -- 对单个 m 的证明，分三步
        -- Step 1: List.sum 转换（涉及类型转换）
        have h1 : (xs.map fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m).sum =
                  ((xs.map fun xi => card_Y_X xs h_nonempty h_sorted (s - xi) m).sum : ℝ) / 6 ^ m := by
          -- simp_rw [div_eq_mul_inv]
          -- let C : ℝ = (6 ^ m)⁻¹

          -- 2. 将除法写成乘法 C * ...
          calc
            (xs.map fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m).sum
              = (xs.map fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) * (6 ^ m)⁻¹).sum := by
                simp_rw [div_eq_mul_inv]

            _ =  (xs.map fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ)).sum * (6 ^ m)⁻¹ := by
              rw [List.sum_map_mul_right]
            _ = ((xs.map fun xi => card_Y_X xs h_nonempty h_sorted (s - xi) m).sum : ℝ) / 6 ^ m := by
              -- 关键：(xs.map (ℕ→ℝ)).sum = ((xs.map ℕ).sum : ℝ)
              congr 1
              -- 使用通用引理: ∑ (cast ∘ f) = cast (∑ f)
              have cast_sum_eq : ∀ (f : ℝ → ℕ) (xs : List ℝ),
                (xs.map (Nat.cast ∘ f)).sum = ((xs.map f).sum : ℝ) := by
                intro f xs
                induction xs with
                | nil => simp
                | cons a as ih =>
                  rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
                  rw [ih]
                  simp [Nat.cast_add]
              exact cast_sum_eq (fun xi => card_Y_X xs h_nonempty h_sorted (s - xi) m) xs



        -- Step 2: 应用 h_bij_step
        have h2 : ((xs.map fun xi => card_Y_X xs h_nonempty h_sorted (s - xi) m).sum : ℝ) =
                  (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) := by
          simp [h_bij_step m]

        -- Step 3: 代数运算 - 合并除法
        have h3 : (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) / 6 ^ m / 6 =
                  (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) / 6 ^ (m + 1) := by
          field_simp
          ring

        -- 组合三步
        calc (xs.map fun xi => (card_Y_X xs h_nonempty h_sorted (s - xi) m : ℝ) / 6 ^ m).sum / 6
            = ((xs.map fun xi => card_Y_X xs h_nonempty h_sorted (s - xi) m).sum : ℝ) / 6 ^ m / 6 := by rw [h1]
          _ = (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) / 6 ^ m / 6 := by rw [h2]
          _ = (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) / 6 ^ (m + 1) := h3

      rw [h_step4]

      have card_pos_zero_eq_zero : card_Y_X xs h_nonempty h_sorted s 0 = 0 := by
        -- 证明 Y_X(s;0) = ∅ 因为 s > 0
        unfold card_Y_X
        have h_empty : Y_X xs h_nonempty h_sorted s 0 = ∅ := by
          ext seq
          simp [Y_X]
          intro h_len h_mem h_sum
          -- 矛盾：长度为0但和为正，因为seq长度为0但和s > 0
          have : seq.sum = 0 := by
            cases seq with
            | nil => simp
            | cons _ _ => simp at h_len
          linarith
        have h_finite_empty : (∅ : Set (List ℝ)).Finite := by simp
        calc (Y_X_finite xs h_nonempty h_sorted s 0).toFinset.card
            = (h_finite_empty).toFinset.card := by
              congr 1; ext x; simp [Set.Finite.toFinset, h_empty]
          _ = 0 := by simp [Set.Finite.toFinset]


      -- Step 5: 指数替换 m ↦ m + 1
      -- 关键：由于 hM_s，当 m > M 时 card_Y_X(s;m) = 0
      -- 所以 card_Y_X(s;M+1) = 0
      have h_card_M_plus_1 : card_Y_X xs h_nonempty h_sorted s (M + 1) = 0 := by
        apply hM_s
        omega

      have h_final : ∑ m ∈ Finset.range (M + 1),
          (card_Y_X xs h_nonempty h_sorted s (m + 1) : ℝ) / 6 ^ (m + 1) =
          ∑ m ∈ Finset.range (M + 1),
            (card_Y_X xs h_nonempty h_sorted s m : ℝ) / 6 ^ m - (card_Y_X xs h_nonempty h_sorted s 0 : ℝ) / 6 ^ 0 := by
        -- 索引变换：∑_{m=0}^{M} f(m+1) = ∑_{m=1}^{M+1} f(m)
        -- 但由于 f(M+1) = 0，所以 = ∑_{m=1}^{M} f(m)
        -- 而 ∑_{m=0}^{M} f(m) = f(0) + ∑_{m=1}^{M} f(m)
        -- 所以 ∑_{m=1}^{M} f(m) = ∑_{m=0}^{M} f(m) - f(0)

        simp only [card_pos_zero_eq_zero, Nat.cast_zero, zero_div, sub_zero]

        -- 证明 ∑_{m=0}^{M} f(m+1) = ∑_{m=0}^{M} f(m)
        -- 使用 Finset.sum_range_succ 展开左边
        rw [Finset.sum_range_succ]

        -- 现在左边是 ∑_{m=0}^{M-1} f(m+1) + f(M+1)
        -- 由于 f(M+1) = 0，所以 = ∑_{m=0}^{M-1} f(m+1)
        simp [h_card_M_plus_1]

        -- 关键观察：∑_{m=0}^{M-1} f(m+1) 和 ∑_{m=1}^{M} f(m) 是相同的和，只是索引不同
        -- 而 ∑_{m=0}^{M} f(m) = f(0) + ∑_{m=1}^{M} f(m)
        -- 由于 f(0) = 0，所以 ∑_{m=1}^{M} f(m) = ∑_{m=0}^{M} f(m)

        -- 先展开 range(M) 的求和
        rw [Finset.sum_range_succ']
        simp [card_pos_zero_eq_zero]

      rw [h_final]
      rw [h_tsum_eq_sum_s]
      simp [card_pos_zero_eq_zero]
