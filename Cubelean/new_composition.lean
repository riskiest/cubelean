import Mathlib
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.List
import Mathlib.Data.Fintype.Basic
import Cubelean.multinomial

-- 开启求和符号 ∑ 的支持
open BigOperators

noncomputable def c : ℝ := 1 / 6

-- 我们定义一个辅助函数，专门计算 measure (度量值)
-- 这样就把 "分类讨论" 的逻辑写在了最显眼的地方
noncomputable def my_measure (xs : Finset ℝ) (t : ℝ) : Nat :=
  if h_ne : xs.Nonempty then
    -- 如果非空，就用 (t / 最小值) 向上取整
    Nat.ceil (t / xs.min' h_ne)
  else
    -- 如果为空，反正不递归，随便给个 0
    0

-- 2. 定义核心递归函数
noncomputable def reachProb (xs : Finset ℝ) (h_pos : ∀ x ∈ xs, 0 < x) (t : ℝ) : ℝ :=
  if h : t ≤ 0 then
    if t = 0 then 1 else 0
  else
    if h_ne : xs.Nonempty then
      let sum_val := ∑ x ∈  xs.attach, reachProb xs h_pos (t - x.val)
      sum_val * c
    else
      0

-- 3. 终止性证明
-- 这里直接定义度量函数： t 除以 (s中的最小值)，然后向上取整转为自然数
termination_by my_measure xs t
  -- Nat.ceil (t / (if h : s.Nonempty then s.min' h else 1))

decreasing_by
-- 1. 展开度量
  simp [my_measure, h_ne]
  -- dsimp [my_measure]
  -- 2. 这里的 h_s 是来自函数体的 if h_s : s.Nonempty
  -- 因为只有 true 分支递归，所以上下文里肯定有 h_s
  -- simp [h_ne]
  -- 3. 定义 step (此时不需要 if 了，直接取值)
  let step := xs.min' h_ne

-- [优化3] 集中准备“弹药”：把 step > 0, t > 0, x ≥ step 全准备好
  -- have h_step_pos : 0 < step := h_pos _ (s.min'_mem _)
  -- have h_t_pos : 0 < t := by linarith [h] -- h 是 ¬(t≤0)
  -- have h_val_ge_step :  x.val ≥ step := Finset.min'_le _ _ x.2

  -- 4. 证明 step > 0
  have h_step_pos : step > 0 := by
    apply h_pos
    exact xs.min'_mem h_ne

  -- 5. 证明 t > 0
  have h_t_pos : t > 0 := by
    push_neg at h
    exact h

  have h_t_div_step_pos : t / step > 0 := by
    apply div_pos h_t_pos h_step_pos

  have h_ceil_pos : Nat.ceil (t / step) > 0 := by
    apply Nat.ceil_pos.mpr
    exact h_t_div_step_pos

  have h_val_ge_step : x.val ≥ step := by
      apply Finset.min'_le; exact x.2

  have h_real_ineq : (t - x.val) / step ≤ t / step - 1 := by
      rw [sub_div]
      gcongr
      -- 证明 x.val / step ≥ 1
      rw [le_div_iff₀ h_step_pos]
      simp
      exact h_val_ge_step

-- 5. 【核心步骤 C】 按照你的逻辑链条进行 calc
  calc
    Nat.ceil ((t - x.val) / step)
    _ ≤ Nat.ceil (t / step - 1) := by
      -- 利用 Nat.ceil 的单调性 (Nat.ceil_mono)
      apply Nat.ceil_mono
      exact h_real_ineq
    _ = Nat.ceil (t / step) - 1 := by
      -- 利用 Nat.ceil (x - 1) = Nat.ceil x - 1
      -- 这需要 x ≥ 0，这里 t/step > 0 显然满足
      rw [Nat.ceil_sub_one]
    _ < Nat.ceil (t / step) := by
      -- 利用 Nat 的性质：如果 n > 0，则 n - 1 < n
      apply Nat.pred_lt
      exact h_ceil_pos.ne' -- 这里需要证明 n ≠ 0

section ReachProb
variable {xs : Finset ℝ} (h_pos : ∀ x ∈ xs, 0 < x)
local notation "X" => { x // x ∈ xs }

-- 2. 证明 seq_fintype
-- { seq : List X // seq.length = m } 就是 List.Vector X m 的定义
-- Vector.fintype 直接提供了这个类型的 Fintype 实例
noncomputable instance seq_fintype (m : ℕ) :
    Fintype { seq : List X // seq.length = m} := Vector.fintype

-- 证明 Y_X_fintype
-- 这是 seq_fintype 的子类型（添加了 sum 条件）
noncomputable instance Y_X_fintype (t : ℝ) (m : ℕ) :
    Fintype { seq : List X // seq.length = m ∧ (seq.map (·.val)).sum = t } := by
  classical
  -- 先建立一个Fintype实例用于嵌套的Subtype
  letI : Fintype { s : { seq : List X // seq.length = m } // (s.val.map (·.val)).sum = t } :=
    Subtype.fintype (p := fun seq : { seq : List X // seq.length = m } => (seq.val.map (·.val)).sum = t)
  -- 使用 Equiv.subtypeSubtypeEquivSubtypeInter 重新组织条件
  exact Fintype.ofEquiv _
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun seq : List X => seq.length = m)
      (fun seq : List X => (seq.map (·.val)).sum = t))

/-- abbrev 会让这个定义在类型类搜索中是“透明”的 -/
abbrev Y_X (xs : Finset ℝ) (t : ℝ) (m : ℕ) : Type :=
  { seq : List { x // x ∈ xs } // seq.length = m ∧ (seq.map (·.val)).sum = t }

-- /-- 将 Y_X 定义为一个具体的子类型 -/
-- def Y_X (xs : Finset ℝ) (t : ℝ) (m : ℕ) : Type :=
--   { seq : List { x // x ∈ xs } // seq.length = m ∧ (seq.map (·.val)).sum = t }
/-- 基础情况：当长度 m = 0 时 -/
theorem card_Y_X_zero (t : ℝ) :
    Fintype.card (Y_X xs t 0) = if t = 0 then 1 else 0 := by
  -- 逻辑：长度为 0 的列表只有 [], 它的和是 0
  -- 1. 处理 if t = 0 then ... else ...
  split_ifs with h
  · -- 情况 A：t = 0
    subst h
    -- 我们证明 Y_X xs 0 0 只有唯一一个元素 (Unique)，即空列表
    -- 拥有 Unique 实例的类型，其基数必然为 1
    have : Unique (Y_X xs 0 0) := {
      default := ⟨[], by simp, by simp⟩,  -- 默认值是空列表
      uniq := fun ⟨l, hl, hs⟩ => by      -- 证明任何元素都等于空列表
        have l_nil : l = [] := List.length_eq_zero_iff.mp hl
        subst l_nil
        simp
    }
    exact Fintype.card_unique
  · -- 情况 B：t ≠ 0
    -- 证明该类型没有任何元素 (IsEmpty)
    rw [Fintype.card_eq_zero_iff]
    constructor
    intro ⟨l, hl, hs⟩
    -- 如果长度为 0，则 l 必定是 []
    have l_nil : l = [] := List.length_eq_zero_iff.mp hl
    -- 将 l = [] 代入总和公式
    rw [l_nil] at hs
    simp at hs
    -- 得到 0 = t，与假设 t ≠ 0 矛盾
    exact h hs.symm

-- /-- 核心定理：长度为 m+1 的序列个数等于前缀分解的和 -/
/-- 递归情况：当长度为 m + 1 时 -/
theorem card_Y_X_recursive (t : ℝ) (m : ℕ) :
    Fintype.card (Y_X xs t (m + 1)) = ∑ x : X, Fintype.card (Y_X xs (t - x.val) m) := by
  -- 逻辑：第一个元素 x 有 |xs| 种选择，每种选择后，剩余序列属于 Y_X (t - x) m
  -- 步骤 1: 将左侧转化为 Sigma 类型的基数
  -- 我们建立双射：Y_X(t, m+1) ≃ Σ (xi : X xs), Y_X(t - xi.val, m)
  let σ := Σ (x : X), Y_X xs (t - x.val) m

  -- 2. 关键：建立双射
  have h_equiv : Y_X xs t (m + 1) ≃ σ := {
    toFun := fun ⟨l, hl, hs⟩ =>
      -- 使用 match 拆分列表，这比 head/tail 更容易让 Lean 自动处理证明
      match l, hl with
      | x :: tail, h_len =>
        ⟨x, ⟨tail, by
          simp at h_len; exact h_len,
          by
          simp [List.sum_cons] at hs
          -- 这里的目标是证明 tail 的和等于 t - x.val
          rw [← hs]
          simp ⟩⟩

    invFun := fun ⟨x, ⟨tail, h_tlen, h_tsum⟩⟩ =>
      ⟨x :: tail, by simp [h_tlen], by
      -- 1. 展开求和公式：sum (x :: tail) = x + sum tail
        simp at *
        -- simp at h_tsum
        -- 2. 此时目标应该是 ↑x + (tail.map (·.val)).sum = t
        -- 我们直接把前提 h_tsum 里的 sum 替换掉
        rw [h_tsum]
        -- 3. 现在的目标是：↑x + (t - ↑x) = t
        -- 这是实数运算的常识，用 add_sub_cancel'_right 或 simp
        simp ⟩


    left_inv := fun ⟨l, hl, hs⟩ => by
      -- 列表的 ext 证明
      cases l <;> simp at hl
      simp

    right_inv := fun ⟨x, ⟨tail, h_tlen, h_tsum⟩⟩ => by
      simp
  }
  -- 3. 最终组合结论
  rw [Fintype.card_congr h_equiv]
  exact Fintype.card_sigma

/-- 引理：如果 xs 是空的且要求的长度 m > 0，那么 Y_X 集合必为空 -/
theorem Y_X_empty_of_empty_xs (h_empty : xs = ∅) (m : ℕ) (hm : m > 0) (t : ℝ) :
    IsEmpty (Y_X xs t m) := by
  constructor
  intro ⟨l, hl, hs⟩
  -- 1. 证明元素类型是空的
  haveI : IsEmpty X := by rw [h_empty]; infer_instance
  -- 2. 任何元素类型为空的列表都必须是 []
  have : l = [] := Unique.eq_default l
  -- 3. 长度矛盾
  rw [this] at hl
  simp at hl -- 得到 0 = m
  exact hm.ne hl

/-- 当 xs 为空时，概率级数关系成立 -/
theorem reachProb_eq_series_empty (h_empty : xs = ∅) (t : ℝ) :
    reachProb xs h_pos t = ∑' m : ℕ, (Fintype.card (Y_X xs t m) : ℝ) * c ^ m := by
  -- 1. 展开 reachProb 的定义
  rw [reachProb]
  -- 2. 分情况讨论 t ≤ 0 和 t > 0
  by_cases ht : t ≤ 0
  · -- t ≤ 0 分支
    simp [ht]
    by_cases h0 : t = 0
    ·
      subst h0
      simp
      -- 证明此时只有 m=0 项为 1，其余为 0 (因为 xs 是空的)
      -- 1. 告诉 Lean：这个无穷级数只有 m = 0 这一项非零
      rw [tsum_eq_single 0]
      . -- 证明当 m = 0 时的那一项正好等于 1
        -- 因为 Y_X xs 0 0 只有一个元素 []，且 c^0 = 1
        simp [card_Y_X_zero]
      . -- 证明当 m ≠ 0 时，所有项均为 0
        intro m hm
        have : c ^ m ≠ 0 := by simp [c]
        simp [this]
        simp [Fintype.card_eq_zero_iff.mpr (Y_X_empty_of_empty_xs h_empty m (Nat.pos_of_ne_zero hm) 0)]
        -- rw [Fintype.card_eq_zero_iff]
        -- constructor
        -- intro ⟨l, hl, hs⟩
        -- -- 如果长度为 m > 0，则 l 不可能是 []
        -- haveI : IsEmpty X := by rw [h_empty]; infer_instance
        -- -- 因为是 Unique，所以 l 必然等于 default (即 [])
        -- have : l = [] := Unique.eq_default l
        -- -- 3. 导出矛盾
        -- rw [this] at hl
        -- simp at hl -- 得到 0 = m
        -- exact hm hl.symm
    ·
      simp [h0]
      rw [tsum_eq_single 0]
      . -- 证明当 m = 0 时的那一项等于 0
        simp [card_Y_X_zero]
        exact h0
      .
        -- 证明当 m ≠ 0 时，所有项均为 0
        intro m hm
        have : c ^ m ≠ 0 := by simp [c]
        simp [this]
        simp [Fintype.card_eq_zero_iff.mpr (Y_X_empty_of_empty_xs h_empty m (Nat.pos_of_ne_zero hm) t)]
      -- 证明此时所有项均为 0
  · -- t > 0 分支
    -- 根据定义，xs 为空且 t > 0 时 reachProb = 0
    simp [ht, h_empty]
    rw [tsum_eq_single 0]
    . -- 证明当 m = 0 时的那一项等于 0
      simp [card_Y_X_zero]
      linarith
    .
      -- 证明当 m ≠ 0 时，所有项均为 0
      intro m hm
      have : c ^ m ≠ 0 := by simp [c]
      simp [this]
      simp [Fintype.card_eq_zero_iff.mpr (Y_X_empty_of_empty_xs _ m (Nat.pos_of_ne_zero hm) t)]

/-- 只需要传入 h_ne，Lean 会自动推导出它属于哪个 xs -/
noncomputable def x₀ (h_ne : xs.Nonempty) : ℝ :=
  xs.min' h_ne

lemma x₀_pos (h_ne : xs.Nonempty) (h_pos : ∀ x ∈ xs, 0 < x) : x₀ h_ne > 0 :=
  h_pos _ (Finset.min'_mem _ _)

lemma x₀_le_all (h_ne : xs.Nonempty) (x : X) : x₀ h_ne ≤ x :=
  Finset.min'_le _ _ x.property

/-- 使用 List.sum_le_sum 证明：和 ≥ 长度 * 最小值 -/
lemma list_sum_ge_length_mul_min (l : List X) (h_ne : xs.Nonempty) :
    (l.map (·.val)).sum ≥ (l.length : ℝ) * x₀ h_ne := by
  -- 1. 将右边的乘法写成一个常数列表的和
  -- (l.length * x₀) = (List.replicate l.length (x₀ h_ne)).sum
  rw [← nsmul_eq_mul]
  rw [← List.sum_replicate (l.length) (x₀ h_ne)]
  rw [← List.map_const]
  -- 2. 准备使用 List.sum_le_sum
  -- 注意：List.sum_le_sum 要求的是 l1.sum ≤ l2.sum
  -- 我们这里是 (replicate ...).sum ≤ (l.map ...).sum
  apply List.sum_le_sum
  simp [x₀_le_all h_ne]

/-- 关键引理：如果步数 m 超过了 (t / x₀)，那么和为 t 的序列不存在 -/
lemma Y_X_isEmpty_of_large_m (h_ne : xs.Nonempty) (t : ℝ) (m : ℕ)
    (hm : (m : ℝ) * x₀ h_ne > t) : IsEmpty (Y_X xs t m) := by
  constructor
  intro ⟨l, hl, hs⟩
  -- 1. 证明列表中的每一个元素 val 满足 val ≥ x₀
  have h_each_ge : ∀ x ∈ l, x ≥ x₀ h_ne := by
    intro x hx
    apply x₀_le_all h_ne

  -- 2. 证明列表的总和 ≥ m * x₀
  have h_sum_ge := list_sum_ge_length_mul_min l h_ne
  rw [hs, hl] at h_sum_ge
  -- 3. 结合 hs : sum = t 和前提 m * x₀ > t 导出矛盾
  linarith

/-- 边界情况引理：当 t ≤ 0 且 m > 0 时，Y_X 为空 -/
lemma Y_X_empty_of_t_le_zero (h_ne : xs.Nonempty) (h_pos : ∀ x ∈ xs, 0 < x) (t : ℝ) (m : ℕ)
    (ht : t ≤ 0) (hm : m > 0) : IsEmpty (Y_X xs t m) := by
  -- 直接调用那个“大数引理”
  apply Y_X_isEmpty_of_large_m h_ne

  -- 现在只需要证明前提条件：m * x₀ > t
  -- 逻辑：m * x₀ > 0 ≥ t
  have h_mul_pos : (m : ℝ) * x₀ h_ne > 0 := by
    apply mul_pos
    · simp; exact Nat.pos_of_ne_zero (Nat.ne_of_gt hm) -- m > 0
    · exact x₀_pos h_ne h_pos -- x₀ > 0 (注意这里需要上下文里的 h_pos)

  linarith [ht, h_mul_pos]

theorem reachProb_eq_series_nonempty (h_ne : xs.Nonempty) (t : ℝ) :
    reachProb xs h_pos t = ∑' m : ℕ, (Fintype.card (Y_X xs t m) : ℝ) * c ^ m := by
  -- 设定归纳步长
  let x_min := x₀ h_ne
  have hx_pos : x_min > 0 := x₀_pos h_ne h_pos

  -- 核心：将实数 t 映射到离散步数 k
  let n := Nat.ceil (t / x_min)
  -- 证明 t ≤ n·x₀
  have ht_le : t ≤ (n : ℝ) * x_min := (div_le_iff₀ hx_pos).mp (Nat.le_ceil _)

  suffices h_strong : ∀ k : ℕ, ∀ s, s ≤ (k : ℝ) * x_min →
      reachProb xs h_pos s = ∑' m, (Fintype.card (Y_X xs s m) : ℝ) * c ^ m from
    h_strong n t ht_le

  intro k
  induction k with
  | zero =>
      -- 基例：s ≤ 0。逻辑与空集情况类似，利用 card_Y_X_zero
      intro s hs; simp at hs
      rw [reachProb]
      simp [hs]
      by_cases h0 : s = 0
      ·
        -- s = 0 时
        simp [h0]
        rw [tsum_eq_single 0]
        . -- m = 0 时的项
          simp [card_Y_X_zero]
        . -- m ≠ 0 时的项
          intro m hm
          have : c ^ m ≠ 0 := by simp [c]
          simp [this]
          simp [Fintype.card_eq_zero_iff.mpr (Y_X_empty_of_t_le_zero h_ne h_pos _ m _ (Nat.pos_of_ne_zero hm))]
      ·
        -- s < 0 时
        simp [h0]
        rw [tsum_eq_single 0]
        . -- m = 0 时的项
          simp [card_Y_X_zero]
          exact h0
        . -- m ≠ 0 时的项
          intro m hm
          have : c ^ m ≠ 0 := by simp [c]
          simp [this]
          simp [Fintype.card_eq_zero_iff.mpr (Y_X_empty_of_t_le_zero h_ne h_pos s m hs (Nat.pos_of_ne_zero hm))]
  | succ k ih =>
      -- 归纳步：假设对 s ≤ k * x_min 成立，证明对 s ≤ (k+1) * x_min 成立
      intro s hs
      by_cases hb : s ≤ (k : ℝ) * x_min
      · exact ih s hb -- 落在旧范围内，直接用归纳假设
      · -- 落在新范围内：k * x_min < s ≤ (k+1) * x_min
        push_neg at hb
        -- 1. 展开定义
        rw [reachProb]
        have s_pos : s > 0 := by
          have hk_nonneg : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
          nlinarith [hb, hk_nonneg, hx_pos]
        simp [s_pos.not_ge, h_ne]

        -- 2. 对递归项应用归纳假设
        -- 关键：因为 x ≥ x_min，所以 s - x ≤ k * x_min
        have h_step : ∀ x : X,
            reachProb xs h_pos (s - x.val) = ∑' m, (Fintype.card (Y_X xs (s - x.val) m) : ℝ) * c ^ m := by
          intro x
          apply ih
          have hx_le : x_min ≤ x := x₀_le_all h_ne x
          have hsx_le: s - x ≤ ↑k * x_min := by
            calc s - x ≤ s - x_min := by linarith [hx_le]
            _ ≤ ↑(k + 1) * x_min - x_min := by linarith [hs]
            _ = ↑k * x_min := by simp [add_mul]

          linarith -- 这里 linarith 展示了它的“神力”：s - x ≤ (k+1)x_min - x_min = k*x_min

        -- 3. 级数变换（证明的灵魂）
        simp_rw [h_step]
        -- 交换求和：∑ x, ∑' m => ∑' m, ∑ x
        -- 关键：交换求和顺序 ∑ (∑' ...) * c => ∑' (∑ ...) * c
        -- 1. 把最外层的 * c 乘进去
        rw [Finset.sum_mul]
        simp_rw [← tsum_mul_right]

        -- 2. 关键，交换 Finset.sum 和 tsum
        -- 【优化策略】使用统一上界 M 对齐两边的有限和范围
        -- 既然 s > s - x，那么 s 的上界必然也是 s - x 的上界。
        let M := Nat.ceil (s / x_min)
        -- 注意：range 是左闭右开，所以我们要取到 M+1 以包含 M
        -- 只要 m > M，就意味着 m * x_min > s
        let S_M := Finset.range (M + 1)
        let S_M2 := Finset.range (M + 2) -- 宽范围：0 到 M+1

        -- 1. 证明统一上界的有效性：超出范围后，两边的项均为 0
        have h_uniform_vanish : ∀ m ∉ S_M,
            (Fintype.card (Y_X xs s m) = 0) ∧
            (∀ x : X, Fintype.card (Y_X xs (s - x.val) m) = 0) := by
          intro m hm_not
          simp [S_M] at hm_not

          -- 准备不等式：m * x_min > s
          have h_large : (m : ℝ) * x_min > s := by
            -- hm_not 给出 M + 1 ≤ m
            have hm_ge : (M + 1 : ℝ) ≤ (m : ℝ) := by
              norm_cast
            -- M 的定义给出 s / x_min ≤ M
            have hM_bound : s / x_min ≤ (M : ℝ) := Nat.le_ceil _
            -- 链式推导
            calc (m : ℝ) * x_min
                ≥ (M + 1 : ℝ) * x_min := by gcongr
              _ > (s / x_min) * x_min := by
                  apply mul_lt_mul_of_pos_right _ hx_pos
                  linarith
              _ = s := div_mul_cancel₀ s (ne_of_gt hx_pos)

          -- 使用 h_large 证明两个结论
          constructor
          · -- 证明 Fintype.card (Y_X xs s m) = 0
            rw [Fintype.card_eq_zero_iff]
            exact Y_X_isEmpty_of_large_m h_ne s m h_large
          · -- 证明 ∀ x : X, Fintype.card (Y_X xs (s - x.val) m) = 0
            intro x
            rw [Fintype.card_eq_zero_iff]
            apply Y_X_isEmpty_of_large_m h_ne
            -- 需要证明 m * x_min > s - x.val
            have hx_ge : x.val ≥ x_min := x₀_le_all h_ne x
            calc (m : ℝ) * x_min
              > s := h_large
              _ ≥ s - x.val := by linarith [hx_ge, hx_pos]

        -- 3. 利用集合包含关系，直接推导 S_M2 的消失性质
        -- 逻辑：因为 S_M ⊂ S_M2，所以 S_M2 之外的元素 一定在 S_M 之外
        have h_uniform_vanish2 : ∀ m ∉ S_M2,
            (Fintype.card (Y_X xs s m) = 0) ∧
            (∀ x : X, Fintype.card (Y_X xs (s - x.val) m) = 0) := by
          intro m hm_not_2
          apply h_uniform_vanish
          -- 证明：m ∉ S_M2 -> m ∉ S_M
          simp [S_M, S_M2] at *
          -- m ≥ M + 2 implies m ≥ M + 1
          omega

        -- 2. 构造通用截断引理 (利用刚才证好的 h_uniform_vanish)
        have h_trunc : ∀ (f : ℕ → ℝ), (∀ m ∉ S_M2, f m = 0) → (∑' m, f m) = ∑ m ∈ S_M2, f m := by
          intro f hf
          rw [tsum_eq_sum (s := S_M2)] -- 显式指定有限集 S_M2
          intro b hb; exact hf b hb

        -- 3. 开始“偷天换日”：对等式两边同时应用截断
        -- 左边：进入求和内部进行截断 (利用 h_uniform_vanish 的第2部分：对 s-x 有效)
        conv_lhs =>
          enter [2, x]
          rw [h_trunc _ (fun m hm => mul_eq_zero_of_left (by simp [ (h_uniform_vanish2 m hm).2 x ]) _)]

        -- 右边：对 s 应用截断 (利用 h_uniform_vanish 的第1部分：对 s 有效)
        rw [h_trunc _ (fun m hm => mul_eq_zero_of_left (by simp [ (h_uniform_vanish2 m hm).1 ]) _)]

        -- 4. 现在两边都是基于 S_M2 的有限和，直接交换！
        -- 交换律：∑ x, ∑ m ∈ S_M2 <-> ∑ m ∈ S_M2, ∑ x
        rw [Finset.sum_comm]

        -- rw [Finset.sum_range_succ']
      -- 1. 处理右边 (RHS): 剥离 m=0，并对剩余项进行下标平移 (m -> m+1)
        -- sum_{0..M} f(m) = f(0) + sum_{0..M-1} f(m+1)
        conv_rhs => rw [Finset.sum_range_succ']
        simp [card_Y_X_zero s, ne_of_gt s_pos] -- 这里用到 s > 0
        conv_lhs => rw [Finset.sum_range_succ]
        simp [h_uniform_vanish (M+1) (by simp [S_M])] -- 这里用到 M 不在范围内

        -- 1. 剥离外层求和，进入每一项进行对比
        -- 两边的范围都是 Finset.range (M + 1)，直接一一对应
        apply Finset.sum_congr rfl
        intro k hk
        -- 2. 处理c ^ k * c = c ^ (k + 1)
        rw [← Finset.sum_mul, ← Finset.sum_mul, mul_assoc, ← pow_succ]
        congr 1
        simp [card_Y_X_recursive s k]

theorem reachProb_eq_series (t : ℝ) :
    reachProb xs h_pos t = ∑' m : ℕ, (Fintype.card (Y_X xs t m) : ℝ) * c ^ m := by
  -- 利用列表的二分性质：要么是空，要么非空
  rcases xs.eq_empty_or_nonempty with h_empty | h_ne

  · -- 情况 1: xs = ∅
    -- 直接调用你证明好的 empty 版本
    exact reachProb_eq_series_empty h_pos h_empty t

  · -- 情况 2: xs ≠ ∅
    -- 直接调用你刚刚证明好的 nonempty 版本
    exact reachProb_eq_series_nonempty h_pos h_ne t

-- ====================================================
-- Phase 1: Definitions
-- ====================================================

noncomputable def sorted_xs (xs : Finset ℝ) : List ℝ := xs.sort (· ≤ ·)
lemma sorted_xs_nodup (xs : Finset ℝ) : (sorted_xs xs).Nodup :=
  Finset.sort_nodup _ _
-- 引理：通过 sorted_xs，Fin (n xs) 遍历 xs 中所有元素
lemma sorted_xs_toFinset_eq (xs : Finset ℝ) :
    (sorted_xs xs).toFinset = xs := by
  simp [sorted_xs]
noncomputable abbrev n (xs : Finset ℝ): ℕ := (sorted_xs xs).length
noncomputable def v (xs : Finset ℝ) : Fin (n xs) → ℝ :=
  fun i => (sorted_xs xs).get i
-- 关键引理：v xs 和 sorted_xs 的关系
lemma v_eq_sorted_xs_get (xs : Finset ℝ) (i : Fin (n xs)) :
    v xs i = (sorted_xs xs).get i := rfl
lemma v_mem (xs : Finset ℝ) (i : Fin (n xs)) :
    v xs i ∈ xs := by
  simp only [v, sorted_xs]
  have : (xs.sort (· ≤ ·)).get i ∈ (xs.sort (· ≤ ·)) := List.get_mem _ _
  rwa [Finset.mem_sort] at this
lemma v_mem_exist (xs : Finset ℝ) (x : ℝ ) (hx : x ∈ xs) :
    ∃ i : Fin (n xs), v xs i = x := by
  have h_mem : x ∈ (xs.sort (· ≤ ·)) := by rw [Finset.mem_sort]; exact hx
  obtain ⟨idx, h_eq⟩ := List.mem_iff_get.mp h_mem
  use ⟨idx.val, by simp only [n, sorted_xs]; exact idx.isLt⟩
  simp only [v, sorted_xs]
  exact h_eq
noncomputable def bij_fin2xs (xs : Finset ℝ) : Fin xs.card ≃ {x // x ∈ xs} :=
  (xs.orderIsoOfFin rfl).toEquiv

-- noncomputable def bij_v2xs (xs : Finset ℝ) :
--     Fin (n xs) ≃ {x // x ∈ xs} := {
--   toFun := fun i => ⟨v xs i, v_mem xs i⟩,
--   invFun := fun x => Classical.choose (v_mem_exist xs x.val x.property),
--   left_inv := fun i => by
--     -- 需要证明 invFun (toFun i) = i
--     -- invFun 使用 Classical.choose 从存在性命题中提取索引
--     simp only
--     have h_exists := v_mem_exist xs (v xs i) (v_mem xs i)
--     have h_eq := Classical.choose_spec h_exists
--     -- 由于 sorted_xs 无重复，v xs j = v xs i 意味着 j = i
--     have h_nodup : (sorted_xs xs).Nodup := sorted_xs_nodup xs
--     simp only [v, sorted_xs] at h_eq
--     exact List.nodup_iff_injective_get.mp h_nodup h_eq,
--   right_inv := fun x => by
--     -- 需要证明 toFun (invFun x) = x
--     -- toFun 返回的是 ⟨v xs i, _⟩，需要证明它等于 x
--     apply Subtype.ext
--     simp only
--     exact Classical.choose_spec (v_mem_exist xs x.val x.property)
-- }
-- ====================================================
-- Phase 2: Lemmas for Fiber Counting
-- ====================================================

-- 辅助引理：列表的长度等于对所有不同元素计数的和
-- lemma list_length_eq_sum_count {α : Type*} [DecidableEq α] (l : List α) (s : Finset α)
--     (h : ∀ x ∈ l, x ∈ s) :
--     l.length = ∑ x ∈ s, l.count x := by
--   -- 使用 Mathlib 的现成定理
--   rw [← List.sum_toFinset_count_eq_length l]
--   -- 证明在 s 上求和和在 l.toFinset 上求和相等
--   apply Finset.sum_subset
--   · -- 证明 l.toFinset ⊆ s
--     intro x hx
--     simp at hx
--     exact h x hx
--   · -- 证明不在 l.toFinset 中的元素 count 为 0
--     intro x hx_in_s hx_not_in_toFinset
--     simp at hx_not_in_toFinset
--     exact List.count_eq_zero_of_not_mem hx_not_in_toFinset

-- 辅助引理：列表的和等于每个元素乘以其出现次数的和
-- lemma list_sum_eq_sum_mul_count (l : List ℝ) (s : Finset ℝ)
--     (h : ∀ x ∈ l, x ∈ s) :
--     l.sum = ∑ x ∈ s, (l.count x : ℝ) * x := by
--   induction l with
--   | nil => simp
--   | cons head tail ih =>
--     simp only [List.sum_cons, List.count_cons]
--     have h_tail : ∀ x ∈ tail, x ∈ s := fun x hx => h x (List.mem_cons_of_mem head hx)
--     rw [ih h_tail]
--     have h_head : head ∈ s := h head List.mem_cons_self
--     rw [← Finset.sum_erase_add _ _ h_head]
--     simp only [Finset.mem_erase, ne_eq, not_true_eq_false, false_and, not_false_eq_true, ite_true, ite_false]
--     ring_nf
--     congr 1
--     apply Finset.sum_congr rfl
--     intro x hx
--     simp only [Finset.mem_erase] at hx
--     simp only [hx.1, ite_false]



-- 求和转换引理
lemma sum_over_fin_eq_sum_over_finset {α : Type*} [AddCommMonoid α] (xs : Finset ℝ) (f : ℝ → α) :
    ∑ i : Fin (n xs), f (v xs i) = ∑ x ∈ xs, f x := by
  -- 使用和 fv_eq_fxs 相同的 sum_bij 策略
  apply Finset.sum_bij (fun i _ => v xs i)
  · -- 1. 映射结果在 xs 里
    intro i _
    simp only [v, sorted_xs]
    have : (xs.sort (· ≤ ·)).get i ∈ (xs.sort (· ≤ ·)) := List.get_mem _ _
    rwa [Finset.mem_sort] at this
  · -- 2. 单射
    intro i₁ _ i₂ _ h
    simp only [v, sorted_xs] at h
    have h_nodup : (xs.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
    have h_idx_eq : i₁ = i₂ := List.nodup_iff_injective_get.mp h_nodup h
    exact h_idx_eq
  · -- 3. 满射
    intro x hx
    have h_mem : x ∈ (xs.sort (· ≤ ·)) := by rw [Finset.mem_sort]; exact hx
    have ⟨idx, h_eq⟩ := List.mem_iff_get.mp h_mem
    refine ⟨⟨idx.val, by simp only [n, sorted_xs]; exact idx.isLt⟩, Finset.mem_univ _, ?_⟩
    simp only [v, sorted_xs]
    exact h_eq
  · -- 4. 值相等
    intro i _
    rfl

-- 辅助引理 1: 计数之和等于列表长度
-- 只要列表元素都在集合 xs 里，那么对 xs 里的每个元素统计其在列表出现的次数之和，就是列表总长
lemma sum_count_eq_len (xs : Finset ℝ) (seq : List ℝ)
  (h_sub : ∀ x ∈ seq, x ∈ xs) :
  ∑ x ∈ xs, seq.count x = seq.length := by
  rw [← List.sum_toFinset_count_eq_length seq]
  symm
  apply Finset.sum_subset
  · -- 证明 seq.toFinset ⊆ xs
    intro x hx
    rw [List.mem_toFinset] at hx
    exact h_sub x hx
  · -- 证明不在 seq.toFinset 中的元素 count 为 0
    intro x _ hx_not_in_toFinset
    rw [List.mem_toFinset] at hx_not_in_toFinset
    exact List.count_eq_zero_of_not_mem hx_not_in_toFinset

-- 辅助引理 2: (计数 * 值) 之和等于列表总和
-- 只要列表元素都在集合 xs 里，加权求和就等于列表原本的 sum
lemma sum_count_mul_eq_sum (xs : Finset ℝ) (seq : List ℝ)
  (h_sub : ∀ x ∈ seq, x ∈ xs) :
  ∑ x ∈ xs, (seq.count x : ℝ) * x = seq.sum := by
  induction seq with
  | nil => simp
  | cons head tail ih =>
    have h_tail : ∀ x ∈ tail, x ∈ xs := fun x hx => h_sub x (List.mem_cons_of_mem head hx)
    have h_head : head ∈ xs := h_sub head List.mem_cons_self
    calc ∑ x ∈ xs, ((head :: tail).count x : ℝ) * x
        = ∑ x ∈ xs, ((tail.count x + if head = x then 1 else 0) : ℝ) * x := by
            congr 1; ext x; simp [List.count_cons, beq_iff_eq]
      _ = ∑ x ∈ xs, (tail.count x : ℝ) * x + ∑ x ∈ xs, (if head = x then 1 else 0 : ℝ) * x := by
            simp_rw [add_mul]; rw [Finset.sum_add_distrib]
      _ = tail.sum + head := by
            rw [ih h_tail]
            congr 1
            simp [h_head]
      _ = (head :: tail).sum := by simp [List.sum_cons]; ring

-- lemma fv_eq_fxs : ∀ (f : ℝ → ℝ),
--     (∑ i : Fin (n xs), f (v xs i)) = (∑ x ∈ xs, f x) := by
--     intro f
--     -- 使用 sum_bij 建立桥梁
--     apply Finset.sum_bij (fun i _ => v xs i)
--     · -- 1. 映射结果在 xs 里
--       intro i _
--       simp only [v, sorted_xs]
--       have : (xs.sort (· ≤ ·)).get i ∈ (xs.sort (· ≤ ·)) := List.get_mem _ _
--       rwa [Finset.mem_sort] at this
--     · -- 2. 单射
--       intro i₁ _ i₂ _ h
--       simp only [v, sorted_xs] at h
--       have h_nodup : (xs.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
--       have h_idx_eq : i₁ = i₂ := List.nodup_iff_injective_get.mp h_nodup h
--       exact h_idx_eq
--     · -- 3. 满射
--       intro x hx
--       have h_mem : x ∈ (xs.sort (· ≤ ·)) := by rw [Finset.mem_sort]; exact hx
--       have ⟨idx, h_eq⟩ := List.mem_iff_get.mp h_mem
--       refine ⟨⟨idx.val, by simp only [n, sorted_xs]; exact idx.isLt⟩, Finset.mem_univ _, ?_⟩
--       simp only [v, sorted_xs]
--       exact h_eq
--     · -- 4. 值相等
--       intro i _
--       rfl





-- [映射] 从序列映射到计数向量
noncomputable def to_vec (xs : Finset ℝ) (seq : List ℝ) : Fin (n xs) → ℕ :=
  fun i => seq.count (v xs i)

-- 4. 解空间 Solutions [显式参数 xs]
    -- 这里的 t和m 可以不带 xs，但 Solutions 本身需要知道 xs 才能算 v和n
noncomputable def K_X (xs : Finset ℝ) (t : ℝ) (m : ℕ) : Finset (Fin (n xs) → ℕ) :=
  (Fintype.piFinset (fun _ => Finset.range (m + 1))).filter (fun k =>
    -- 约束 1: 总个数为 m (注意 n xs)
    (∑ i : Fin (n xs), k i) = m ∧

    -- 约束 2: 点积为 t (注意 v xs i)
    (∑ i : Fin (n xs), (k i : ℝ) * (v xs i)) = t
  )

-- 6. 核心引理：映射的像就在 K_X 里
-- 只要 seq 满足 "长度为 m" 且 "和为 t"，它的计数向量一定在 K_X 里
lemma to_vec_mem_K_X (xs : Finset ℝ) (t : ℝ) (m : ℕ) (seq : List ℝ)
  (h_len : seq.length = m) (h_sum : seq.sum = t)
  (h_mem : ∀ x ∈ seq, x ∈ xs) :
  to_vec xs seq ∈ K_X xs t m := by
  -- 只需要证明满足两个约束条件
  simp [K_X, Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_range, to_vec]
  rw [sum_over_fin_eq_sum_over_finset xs (fun x => seq.count x)]
  rw [sum_over_fin_eq_sum_over_finset xs (fun x => (seq.count x : ℝ) * x)]
  rw [sum_count_eq_len xs seq h_mem]
  rw [sum_count_mul_eq_sum xs seq h_mem]
  refine ⟨?_, h_len, h_sum⟩
  intro a
  rw [← h_len]
  apply Nat.lt_succ_of_le
  apply List.count_le_length

-- 1. 定义：从计数向量 k 生成多重集
-- 公式：M = ∑ (k_i 个 v_i)
noncomputable def vec_to_multiset (xs : Finset ℝ) (k : Fin (n xs) → ℕ) : Multiset ℝ :=
  (Finset.univ : Finset (Fin (n xs))).sum (fun i => Multiset.replicate (k i) (v xs i))

-- 2. 引理：这个多重集的计数确实等于 k
-- 证明 vec_to_multiset 没造假，生成的 x 数量正好是 k 要求的
lemma count_vec_to_multiset (xs : Finset ℝ) (k : Fin (n xs) → ℕ) (i : Fin (n xs)) :
  (vec_to_multiset xs k).count (v xs i) = k i := by
  simp [vec_to_multiset]
  rw [Multiset.count_sum']
  rw [Finset.sum_eq_single i]
  · -- 证明 i 在求和范围内
    simp
  · -- 证明 j ≠ i 时，count 为 0
    intro j _ h_diff
    simp only [Multiset.count_replicate]
    rw [if_neg]
    intro h_eq
    apply h_diff
    apply List.nodup_iff_injective_get.mp (sorted_xs_nodup xs)
    rw [← v_eq_sorted_xs_get xs _, ← v_eq_sorted_xs_get xs _]
    exact h_eq
  . -- 证明 i 不在求和范围内的情况不可能
    simp


-- 3. 核心引理：计数向量为 k 的列表，就是 M_k 的全排列
-- mem_permutations 表示 "l 是 m 的一个排列"
lemma to_vec_eq_iff_perm (xs : Finset ℝ) (k : Fin (n xs) → ℕ) (l : List ℝ) :
  (h_mem : ∀ x ∈ l, x ∈ xs) → -- 前提：列表元素合法
  let m: Multiset ℝ := vec_to_multiset xs k
  (to_vec xs l = k ↔ ↑l = m) := by

  intro h_mem m
  rw [Multiset.ext]
  constructor
  · -- 正向：to_vec xs l = k -> ↑l = m
    intro h_vec_eq x
    by_cases hx : x ∈ xs
    · -- 情况 1: x ∈ xs
      -- 利用计数引理证明
      have h_exists := v_mem_exist xs x hx
      let i := Classical.choose h_exists
      have h_v_i : v xs i = x := Classical.choose_spec h_exists

      rw [← h_v_i]
      have h_left : (l : Multiset ℝ).count (v xs i) = k i := by
        have := congr_fun h_vec_eq i
        simp [to_vec] at this
        rw [Multiset.coe_count]
        exact this

      have h_right : m.count (v xs i) = k i := by
        apply count_vec_to_multiset

      rw [h_left, h_right]
    · -- 情况 2: x ∉ xs
      -- 左右两边的计数都为 0
      have h_left : (l : Multiset ℝ).count x = 0 := by
        rw [Multiset.count_eq_zero]
        intro h_in
        exact hx (h_mem x h_in)
      have h_right : m.count x = 0 := by
        simp only [m, vec_to_multiset]
        rw [Multiset.count_sum']
        apply Finset.sum_eq_zero; intro i _; rw [Multiset.count_replicate, if_neg]
        intro h; apply hx;
        rw [← h]
        exact v_mem xs i
      rw [h_left, h_right]
  · -- 反向：↑l = m -> to_vec xs l = k
    intro h_count_eq
    funext i
    simp [to_vec]
    rw [← Multiset.coe_count]
    rw [h_count_eq (v xs i)]
    rw [count_vec_to_multiset]

-- 辅助引理：多重集的总大小 = 向量分量之和
-- card (∑ replicate k v) = ∑ k
lemma card_vec_to_multiset (xs : Finset ℝ) (k : Fin (n xs) → ℕ) :
  (vec_to_multiset xs k).card = ∑ i, k i := by
  simp only [vec_to_multiset]
  -- 多重集求和的大小 = 各部分大小之和
  rw [Multiset.card_sum]
  -- 交换 map 和 sum
  -- rw [Finset.sum_map_val]
  -- 每一项 replicate (k i) 的大小就是 k i
  apply Finset.sum_congr rfl
  intro i _
  simp only [Multiset.card_replicate]

-- 辅助引理：将 Multiset 的阶乘分母转化为向量 k 的阶乘乘积
lemma prod_factorial_eq (xs : Finset ℝ) (k : Fin (n xs) → ℕ) :
  let m := vec_to_multiset xs k
  (∏ x ∈ m.toFinset, (m.count x).factorial) = ∏ i, (k i).factorial := by
  -- 证明思路：
  -- 1. 当 k i = 0 时，右边贡献 0! = 1，左边 v xs i 不在 m.toFinset 中
  -- 2. 当 k i ≠ 0 时，v xs i ∈ m.toFinset 且 m.count (v xs i) = k i
  -- 3. 由于 v 是单射，且 0! = 1，两边相等
  -- 完整证明需要仔细处理边界情况，这里暂时用 sorry
  intro m
  let S : Finset ℝ := m.toFinset
  symm
  rw [Finset.prod_subset (s₁:=S) (s₂ := xs)]
  .
    apply Finset.prod_bij (fun i _ => v xs i)
    .
      intro i _
      exact v_mem xs i
    .
      intro i₁ _ i₂ _ h
      simp only [v, sorted_xs] at h
      have h_nodup : (xs.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
      have h_idx_eq : i₁ = i₂ := List.nodup_iff_injective_get.mp h_nodup h
      exact h_idx_eq
    .
      intro x hx
      simp
      exact v_mem_exist xs x hx
    .
      intro i _
      rw [← count_vec_to_multiset xs k i]
  .
    intro x hx
    simp only [S, Multiset.mem_toFinset, m, vec_to_multiset] at hx
    rw [Multiset.mem_sum] at hx
    rcases hx with ⟨i, _, h_val⟩
    rw [Multiset.mem_replicate] at h_val
    have : x ∈ xs := by simp [h_val.2, v_mem]
    exact this
  .
    intro x hx h_not_in_s
    -- 证明 m.count x = 0
    simp only [S, Multiset.mem_toFinset] at h_not_in_s
    rw [← Multiset.count_eq_zero] at h_not_in_s
    simp [h_not_in_s]

  -- 构造包含关系 S ⊆ xs


-- 4. 最终计数引理：映射到 k 的列表个数等于多项式系数
-- 注意：这里我们需要把 Mathlib 的 "除以元素阶乘" 转化为我们的 "除以 k_i 阶乘"
lemma card_fiber_eq_coeff (xs : Finset ℝ) (k : Fin (n xs) → ℕ) :
  let S := { l : List ℝ | (∀ x ∈ l, x ∈ xs) ∧ to_vec xs l = k }
  Nat.card S = Nat.factorial (∑ i, k i) / ∏ i, Nat.factorial (k i) := by
  let m := vec_to_multiset xs k
  intro S
  -- 1. 证明 S 的基数等于 m 的全排列数量
  -- 我们不需要把 S 转成 Finset，直接利用 Set 和 Multiset 的对应关系
  -- Step 1: 建立双射 S ≃ { l // l ~ m }
  -- 直接利用你证好的 to_vec_eq_iff_perm
  let iso : S ≃ { l : List ℝ // ↑l = m } := {
    toFun := fun ⟨l, hl⟩ => ⟨l, (to_vec_eq_iff_perm xs k l hl.1).mp hl.2⟩
    invFun := fun ⟨l, hl⟩ => ⟨l, by
      have h_mem: ∀ x ∈ l, x ∈ xs := by
        intro x hx
        have h_in_m: x ∈ m := by rw [← hl]; exact hx
        -- 既然 x 在 m (由 xs 生成) 里，那 x 一定在 xs 里
        simp only [m, vec_to_multiset] at h_in_m
        rw [Multiset.mem_sum] at h_in_m
        rcases h_in_m with ⟨i, _, h_val⟩
        rw [Multiset.mem_replicate] at h_val
        have : x ∈ xs := by simp [h_val.2, v_mem]
        exact this
      constructor
      -- 只需要补一个: l ~ m implies l ⊆ xs
      ·
        exact h_mem
      · -- 这里的 hl 就是 to_vec = k
        rw [← (to_vec_eq_iff_perm xs k l h_mem).mpr hl]
    ⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl
  }

  -- 2. 利用双射传递基数 (S 的大小 = 全排列集合的大小)
  rw [Nat.card_congr iso]

  -- 3. 应用 Mathlib 的全排列计数定理
  -- 先把 Nat.card 转为 Fintype.card (因为 Mathlib 定理是用 Fintype 描述的)
  rw [Nat.card_eq_fintype_card]
  -- 核心定理：多重集的全排列数 = m! / Π(count!)
  rw [card_permutations_eq_multinomial m]
  congr 1
  · -- 分子替换: card m = ∑ k
    rw [card_vec_to_multiset]
  · -- 分母替换: Π (count x)! = Π (k i)!
    rw [prod_factorial_eq]

noncomputable def k_multinomial (xs : Finset ℝ) (k : Fin (n xs) → ℕ) : ℕ :=
  (∑ i, (k i)).factorial / ∏ i, ((k i).factorial)

lemma card_fiber_eq_coeff_k (xs : Finset ℝ) (k : Fin (n xs) → ℕ) :
  let S := { l : List ℝ | (∀ x ∈ l, x ∈ xs) ∧ to_vec xs l = k }
  Nat.card S = k_multinomial xs k:= by
  simp [k_multinomial]
  apply card_fiber_eq_coeff


theorem YX_eq_KX (t : ℝ) :
    ∑' m : ℕ, (Fintype.card (Y_X xs t m) : ℝ) * c ^ m =
    ∑' m : ℕ, ∑ k ∈ K_X xs t m,
      (k_multinomial xs k : ℝ) * c ^ m := by
  apply tsum_congr
  intro m
  rw [← Finset.sum_mul]
  congr
  norm_cast
  let F : Y_X xs t m → Fin (n xs) → ℕ := fun seq => to_vec xs (seq.val.map Subtype.val)
  simp only [k_multinomial]
  rw [← Finset.card_univ]
  rw [Finset.card_eq_sum_card_fiberwise (s := Finset.univ) (f := F) (t := K_X xs t m)]
  .
    apply Finset.sum_congr rfl
    intro k hk
    rw [← card_fiber_eq_coeff xs k]
    rw [← Fintype.card_ofFinset]
    rw [Fintype.card_eq_nat_card]
    apply Nat.card_congr
    refine {
      -- === 正向映射: seq -> k ===
      -- 输入 seq (它是 Y_X 的元素，即一个 Subtype)
      toFun := fun seq => ⟨
        -- 提取出的 k 实际上就是 seq 的计数向量
        -- seq.1.val 是 List {x//x∈xs}，再 map val 变成 List ℝ
        seq.1.val.map Subtype.val,
        by
          -- 1. 证明向量相等
          have h_vec : F seq.1 = k := by
             have h := seq.property
             -- 【关键】告诉 Lean ?m 就是这个 filter，消除歧义
             change seq.1 ∈ Finset.filter (fun a => F a = k) Finset.univ at h
             simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
             exact h
          constructor
          · -- 证明都在 xs 里
            intro x hx
            rcases List.mem_map.mp hx with ⟨y, _, rfl⟩
            exact y.property
          · -- 证明计数向量相等
            exact h_vec
      ⟩,

      -- === 逆向映射: k -> seq ===
      -- 输入是一个 pair，包含一个列表 l (我们把它视为还原后的 seq 数据)
      -- 和两个证明：1. 元素都在 xs 里; 2. 它的计数向量等于 k
      invFun := fun ⟨l_data, ⟨h_mem, h_vec⟩⟩ => ⟨
        -- 构造 seq (Y_X 元素)
        ⟨l_data.pmap Subtype.mk (fun x h => h_mem x h), by
          constructor
          · -- 证明 seq.length = m
            dsimp; rw [List.length_pmap]
            rw [← sum_count_eq_len xs l_data h_mem]
            rw [← sum_over_fin_eq_sum_over_finset]
            change (∑ i, to_vec xs l_data i) = m
            rw [h_vec]
            simp only [K_X, Finset.mem_filter] at hk
            exact hk.2.1
          · -- 证明 seq.sum = t
            dsimp; rw [List.map_pmap]
            simp
            rw [← sum_count_mul_eq_sum xs l_data h_mem]
            rw [← sum_over_fin_eq_sum_over_finset]
            change (∑ i, (to_vec xs l_data i) * (v xs i) ) = t
            rw [h_vec]
            simp only [K_X, Finset.mem_filter] at hk
            exact hk.2.2
        ⟩,
        by
          -- 【关键】同样需要指明类型，证明这个 seq 属于左边的 filter
          change _ ∈ Finset.filter (fun a => F a = k) Finset.univ
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          dsimp [F, to_vec]
          rw [List.map_pmap]
          simp
          exact h_vec
      ⟩
      -- === 证明左逆: inv(to(seq)) = seq ===
      left_inv := fun seq => by
        apply Subtype.ext; apply Subtype.ext
        dsimp;
        rw [List.pmap_map]
        simp
      -- === 证明右逆: to(inv(pair)) = pair ===
      right_inv := fun x => by
        rcases x with ⟨l_data, h_mem, h_vec⟩
        apply Subtype.ext
        dsimp
        -- simp only
        rw [List.map_pmap]
        simp
    }
    intro x; rfl
  .
    intro seq hx
    apply to_vec_mem_K_X
    · simp
      exact seq.property.1
    · exact seq.property.2
    · intro x hx
      rcases (List.mem_map.mp hx) with ⟨y, _, rfl⟩
      exact y.property
-- ====================================================

theorem reachProb_eq_multinomial (t : ℝ) :
  reachProb xs h_pos t =
        ∑' m : ℕ, ∑ k ∈ K_X xs t m,
      (k_multinomial xs k : ℝ) * c ^ m := by
  rw [← YX_eq_KX, reachProb_eq_series]

end ReachProb
