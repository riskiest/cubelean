import Mathlib
import Cubelean.composition
import Mathlib.Data.List.Zip
import Mathlib.Data.List.Permutation -- 注意是单数 Permutation
import Mathlib.Data.Fintype.Perm
open Set List Classical Function
/-!
# 定理：f_X(t) 的组合系数求和表示

本文件证明从有序序列计数表示到组合系数表示的转换定理。

## 主要内容

1. **组合集合定义** `K_X(t)`：表示所有满足 ∑ k_i * x_i = t 的非负整数组合
2. **核心引理**：建立有序序列与组合的双射关系
3. **主定理**：f_X(t) = ∑_{k ∈ K_X(t)} (多项式系数) / 6^n

## 证明思路

从 composition.lean 中已知：
  f_X(t) = ∑_{m=0}^∞ |Y_X(t;m)| / 6^m

本文件证明：
  f_X(t) = ∑_{k ∈ K_X(t)} C(n; k₀,k₁,...,k_{j-1}) / 6^n

其中 n = ∑ k_i，通过以下步骤：
1. 定义序列到组合的映射 ψ
2. 证明组合对应的序列数等于多项式系数
3. 交换求和顺序（有限性保证合法性）
-/

open BigOperators

-- ========================================
-- 第一部分：组合集合的定义
-- ========================================

/-- 组合集合 K_X(t)：所有满足 ∑ k_i * x_i = t 的非负整数向量 -/
def K_X (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) : Set (List ℕ) :=
  { ks : List ℕ | ks.length = xs.length ∧
    (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t }

lemma sum_map_cast {l : List ℕ} : (l.map (λ k => (k : ℝ))).sum = (l.sum : ℝ) :=
  by induction l with
  | nil => simp
  | cons h t ih =>
  simp
  rw [← List.flatMap_pure_eq_map, Nat.cast]
  rfl

lemma elem_le_sum {ks : List ℕ} (k : ℕ) (hk : k ∈ ks) : k ≤ ks.sum := by
  -- 对列表 ks 进行归纳
  induction ks with
  | nil =>
    -- 基础情况：空列表
    -- 空列表中不可能有元素 k，导致矛盾
    contradiction
  | cons head tail ih =>
    -- 递归情况：ks = head :: tail
    -- 此时 hk 的类型是 k ∈ head :: tail
    -- 根据列表成员关系的定义，k 要么是 head，要么在 tail 中
    cases hk with
    | head =>
      -- 情况 1: k 就是 head
      -- 此时目标变成了证明: head ≤ head + tail.sum
      -- 对于自然数，x ≤ x + y 总是成立的 (Nat.le_add_right)
      apply Nat.le_add_right
    | tail _ h_in_tail =>
      -- 情况 2: k 在 tail 中 (k ∈ tail)
      -- 此时目标是证明: k ≤ head + tail.sum

      -- 利用归纳假设 (ih): 因为 k 在 tail 中，所以 k ≤ tail.sum
      have h_le_tail_sum : k ≤ tail.sum := ih h_in_tail

      -- 利用传递性：
      -- 已知 k ≤ tail.sum
      -- 显见 tail.sum ≤ head + tail.sum (Nat.le_add_left)
      apply Nat.le_trans h_le_tail_sum
      apply Nat.le_add_left

lemma elem_le_sum_cast {ks : List ℕ} (k : ℕ) (hk : k ∈ ks) : (k : ℝ) ≤ (ks.sum : ℝ) := by
  -- 1. 将实数不等式转化为自然数不等式
  -- Nat.cast_le 的方向是：(↑a ≤ ↑b) ↔ (a ≤ b)
  -- 我们这里是从右往左推，通常写作 Nat.cast_le.2 或者 rw [← Nat.cast_le]
  rw [Nat.cast_le]

  -- 2. 现在目标变成了 k ≤ ks.sum (在自然数域)
  -- 直接应用你刚才证明的引理
  apply elem_le_sum k hk

lemma sum_le_sum (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (ks : List ℕ)
    (h_length : ks.length = xs.length) :
    (ks.map (fun k => (k : ℝ) * xs[0]!)).sum ≤ (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum := by
  -- 1. 定义 x₀ 以简化书写
  let x₀ := xs[0]!

-- 【步骤 1】应用 Forall₂.sum_le_sum
  -- 这将目标从 "sum <= sum" 转化为 "证明这两个列表满足 Forall₂ (≤) 关系"
  apply List.Forall₂.sum_le_sum

  -- 【步骤 2】应用 forall₂_iff_get
  -- 将 Forall₂ 关系转化为 "长度相等" 和 "逐项索引满足关系"
  rw [List.forall₂_iff_get]

-- 此时产生两个子目标：
  -- 1. 长度相等
  -- 2. 对于任意索引 i，第 i 项满足不等式
  constructor

  -- 【子目标 1：证明长度相等】
  ·
    simp [List.length_zipWith, h_length]

  -- 【子目标 2：证明逐项不等式】
  ·
    intro i h_len_map h_len_zip
    -- 目标：(map (fun k => (k : ℝ) * xs[0]!) ks)[i] ≤ (List.zipWith (fun k x => (k : ℝ) * x) ks xs)[i]
    -- rw [List.getElem_map, List.getElem_zipWith]
    -- 目标：(ks[i] : ℝ) * xs[0]! ≤ (ks[i] : ℝ) * xs[i]
    have h_index : i < xs.length := by
      simp [h_length] at h_len_map
      exact h_len_map
    have h_head_le : xs[0]! ≤ xs[i] := by
      apply head_le_of_pairwise_lt h_nonempty.1 h_sorted (xs[i]'h_index)
      apply List.get_mem

    simp only [List.pure_def, bind_eq_flatMap, get_eq_getElem, getElem_map, getElem_zipWith, ge_iff_le]
    -- simp?
    apply mul_le_mul_of_nonneg_left
    exact h_head_le

    simp only [← List.map_eq_flatMap]
    simp only [List.getElem_map]
    apply Nat.cast_nonneg

lemma zipwith_length_equal (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (ks : List ℕ)
    (h_length : ks.length = xs.length) :
    (List.zipWith (fun k x => (k : ℝ) * x) ks xs).length = xs.length := by

  simp [List.length_zipWith, h_length]

-- ========================================
-- 新提取的引理 (Extracted Lemmas)
-- ========================================

/-- 引理 A: 总和的界 -/
lemma sum_mul_head_le_t
  (xs : List ℝ)
  (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
  (h_sorted : xs.Pairwise (· < ·))
  (t : ℝ)
  (ks : List ℕ)
  (hks : ks ∈ K_X xs h_nonempty h_sorted t):
  -- (h_length : ks.length = xs.length)
  -- (h_sum_eq_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t) :
  (ks.sum : ℝ) * xs[0]! ≤ t := by

  -- 1. 证明基础不等式
  have h_base_le : (ks.map (fun k => (k : ℝ) * xs[0]!)).sum ≤ t := by
    have h_sum_eq_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t := by
      exact hks.2
    rw [← h_sum_eq_t]
    -- 这里调用你之前的证明逻辑或者公理
    apply sum_le_sum xs h_nonempty h_sorted ks hks.1
    -- xs h_length  .1 h_nonempty.2

  -- 2. 代数化简
  rw [List.sum_map_mul_right] at h_base_le
  rw [sum_map_cast] at h_base_le
  exact h_base_le

lemma sum_le_div_head
  (xs : List ℝ)
  (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
  (h_sorted : xs.Pairwise (· < ·))
  (t : ℝ)
  (ks : List ℕ)
  (hks : ks ∈ K_X xs h_nonempty h_sorted t):
  -- (h_length : ks.length = xs.length)
  -- (h_sum_eq_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t) :
  (ks.sum : ℝ) ≤ t / xs[0]!:= by
  have h_total := sum_mul_head_le_t xs h_nonempty h_sorted t ks hks
  rwa [le_div_iff₀ h_nonempty.2]

/-- 引理 A: 总和的界 -/
lemma sum_le_bound
  (xs : List ℝ)
  (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
  (h_sorted : xs.Pairwise (· < ·))
  (t : ℝ)
  (ks : List ℕ)
  (hks : ks ∈ K_X xs h_nonempty h_sorted t):
  -- (h_length : ks.length = xs.length)
  -- (h_sum_eq_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t) :
  ks.sum ≤ Nat.ceil (t / xs[0]!) := by
  have h_total := sum_le_div_head xs h_nonempty h_sorted t ks hks
  have h_ceil : t / xs[0]! ≤ Nat.ceil (t / xs[0]!) := by
    apply Nat.le_ceil
  have h_real_div : (ks.sum : ℝ) ≤ Nat.ceil (t / xs[0]!) := le_trans h_total h_ceil
-- 3. 利用 Ceil 的单调性转回自然数
    --    目标: ks.sum ≤ ⌈t / x₀⌉
  have h_final : ks.sum ≤ Nat.ceil (t / xs[0]!) := by
    -- 对 h_real_div 两边同时取 ceil
    have h_ceil := Nat.ceil_mono h_real_div
    -- 关键一步: Nat.ceil (n : ℝ) = n
    simp only [Nat.ceil_natCast] at h_ceil
    exact h_ceil
  exact h_final

/-- 引理 B: 单项乘积的界 -/
lemma elem_mul_head_le_t
  (xs : List ℝ)
  (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
  (h_sorted : xs.Pairwise (· < ·))
  (t : ℝ)
  (ks : List ℕ)
  (hks : ks ∈ K_X xs h_nonempty h_sorted t)
  (hk : k ∈ ks):
  (k : ℝ) * xs[0]! ≤ t := by

  -- 直接调用引理 A，把所有参数显式传进去
  have h_total := sum_mul_head_le_t xs h_nonempty h_sorted t ks hks
  have h_elem_le_sum:= elem_le_sum_cast k hk

  have h_part : (k : ℝ) * xs[0]! ≤ (ks.sum : ℝ) * xs[0]! := by
    apply mul_le_mul_of_nonneg_right
    · exact h_elem_le_sum
    · exact le_of_lt h_nonempty.2

  exact le_trans h_part h_total

/-- 引理 C: 单项数值的界 (最终要用的) -/
lemma elem_le_div_head
  (xs : List ℝ)
  (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
  (h_sorted : xs.Pairwise (· < ·))
  (t : ℝ)
  (ks : List ℕ)
  (hks : ks ∈ K_X xs h_nonempty h_sorted t)
  (hk : k ∈ ks):
  (k : ℝ) ≤ t / xs[0]! := by

  -- 直接调用引理 B
  have h_raw := elem_mul_head_le_t xs h_nonempty h_sorted t ks hks hk
  rwa [le_div_iff₀ h_nonempty.2]

/-- 引理 A: 总和的界 -/
lemma elem_le_bound
  (xs : List ℝ)
  (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
  (h_sorted : xs.Pairwise (· < ·))
  (t : ℝ)
  (ks : List ℕ)
  (hks : ks ∈ K_X xs h_nonempty h_sorted t)
  (hk : k ∈ ks):
  -- (h_length : ks.length = xs.length)
  -- (h_sum_eq_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t) :
  k ≤ Nat.ceil (t / xs[0]!) := by
  have h_total := elem_le_div_head xs h_nonempty h_sorted t ks hks hk
  have h_ceil : t / xs[0]! ≤ Nat.ceil (t / xs[0]!) := by
    apply Nat.le_ceil
  have h_real_div := le_trans h_total h_ceil
-- 3. 利用 Ceil 的单调性转回自然数
    --    目标: ks.sum ≤ ⌈t / x₀⌉
  have h_final : k ≤ Nat.ceil (t / xs[0]!) := by
    -- 对 h_real_div 两边同时取 ceil
    have h_ceil := Nat.ceil_mono h_real_div
    -- 关键一步: Nat.ceil (n : ℝ) = n
    simp only [Nat.ceil_natCast] at h_ceil
    exact h_ceil
  exact h_final

-- ========================================
-- 第三部分：有限性引理
-- ========================================

/--
引理 3.1：K_X(t) 是有限集
证明：由于 x₀ > 0，总使用次数 n = ∑k_i ≤ t/x₀，
     故满足条件的组合只有有限个
-/
lemma K_X_finite (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) :
    (K_X xs h_nonempty h_sorted t).Finite := by
  -- 证明思路：
  -- 1. K_X(t) 中的每个 ks 满足 ks.length = xs.length（固定长度）
  -- 2. 对每个 k_i，由于 k_i * x₀ ≤ k_i * x_i ≤ ∑(k_j * x_j) = t
  --    所以 k_i ≤ t / x₀，即 k_i ≤ ⌈t / x₀⌉
  -- 3. 因此 K_X(t) ⊆ {ks : List ℕ | ks.length = xs.length ∧ ∀ k ∈ ks, k ≤ ⌈t/x₀⌉}
  -- 4. 后者是有限集（有界自然数列表的有限集）

  let x₀ := xs[0]!
  let bound := Nat.ceil (t / x₀)
  have h_x₀_pos : x₀ > 0 := h_nonempty.2

  -- 定义包含 K_X(t) 的有限集：长度固定且每个分量有界的列表
  let BoundedLists : Set (List ℕ) :=
    {ks | ks.length = xs.length ∧ ∀ k ∈ ks, k ≤ bound}

  -- 步骤1：证明 K_X(t) ⊆ BoundedLists
  have h_subset : K_X xs h_nonempty h_sorted t ⊆ BoundedLists := by
    intro ks hks
    simp only [K_X, BoundedLists, mem_setOf] at *
    constructor
    .
      exact hks.1
    .
      intro k hk
      have := elem_le_bound xs h_nonempty h_sorted t ks hks hk
      exact this

  -- 步骤2：证明 BoundedLists 是有限的
  have h_bounded_finite : Set.Finite BoundedLists := by
    let A := {k : ℕ | k ≤ bound}
    have hA : Set.Finite A := by
      apply Set.Finite.subset (Finset.range (bound + 1)).finite_toSet
      intro k hk
      simp only [Finset.mem_coe, Finset.mem_range]
      exact Nat.lt_succ_of_le hk
    let P : ℕ → Set (List ℕ) := fun n => {l | l.length = n ∧ ∀ k ∈ l, k ∈ A}
    let rec h_P : ∀ n, Set.Finite (P n) :=
      fun n =>
        match n with
        | 0 =>
            have : P 0 = {[]} := by
              ext l; constructor
              · intro h; have : l = [] := List.eq_nil_of_length_eq_zero h.1; rw [this]; trivial
              · intro h; rw [h]; exact ⟨rfl, fun k hk => by cases hk⟩
            Eq.mp (by rw [this]) (Set.finite_singleton [])
        | n'+1 =>
            let ProdSet := A ×ˢ (P n')
            let h_prod_fin := Set.Finite.prod hA (h_P n')
            let f : ℕ × List ℕ → List ℕ := fun p => p.1 :: p.2
            have : P (n'+1) = Set.image f ProdSet := by
              ext l; constructor
              · intro hl
                obtain ⟨h_len, h_all⟩ := hl
                cases l with
                | nil => exfalso; simp at h_len
                | cons x xs =>
                    have len_xs : xs.length = n' := by rw [List.length_cons] at h_len; exact Nat.succ.inj h_len
                    have xA := h_all x List.mem_cons_self
                    have xsA := fun k hk => h_all k (List.mem_cons_of_mem x hk)
                    exact ⟨(x, xs), ⟨xA, ⟨len_xs, xsA⟩⟩, rfl⟩
              · intro hl
                rcases hl with ⟨⟨x, xs⟩, ⟨hxA, ⟨h_len, h_all⟩⟩, rfl⟩
                exact ⟨by rw [List.length_cons, h_len], fun k hk =>
                  match List.mem_cons.mp hk with
                  | .inl h_eq => by rw [h_eq]; exact hxA
                  | .inr h_mem => h_all k h_mem⟩
            Eq.mp (by rw [this]) (Set.Finite.image f h_prod_fin)
    apply Set.Finite.subset (h_P xs.length)
    intro l hl
    simp only [BoundedLists, Set.mem_setOf_eq] at hl
    simp only [P, Set.mem_setOf_eq]
    exact ⟨hl.1, fun k hk_mem => hl.2 k hk_mem⟩

  -- 步骤3：有限集的子集也是有限的
  exact h_bounded_finite.subset h_subset

-- ========================================
-- 第二部分：关键引理 - 序列与组合的对应关系
-- ========================================

-- ====================================================
-- 0. 准备工作：多项式系数与排列
-- ====================================================

/--
定义映射 ψ (psi): 将一个序列映射为它在 xs 中各元素出现的次数向量
例如：xs = [1, 2], seq = [1, 2, 1] -> ks = [2, 1]
-/
noncomputable def psi (xs : List ℝ) (seq : List ℝ) : List ℕ :=
  xs.map (fun x => seq.count x)



-- ====================================================
-- 1. 证明 ψ 将 Y_X 映射入 K_X
-- ====================================================

/--
引理：如果序列 seq 的元素都在 xs 中，且 seq 的和为 t，
那么它的计数向量 ks = psi(seq) 满足加权和也为 t。
-/

-- lemma sum_eq_weighted_sum_real (xs : List ℝ) (seq : List ℝ)
--     (h_nodup : xs.Nodup)
--     (h_subset : ∀ y ∈ seq, y ∈ xs) :
--     (xs.map (fun x => (seq.count x : ℝ) * x)).sum = seq.sum := by
--   -- 1. 构造一个标准列表 canonical，它是 xs 中元素按计数展开的结果
--   let canonical := (xs.map (fun x => List.replicate (seq.count x) x)).flatten

--   -- 2. 证明 seq 是 canonical 的一个排列 (Permutation)
--   --    两个列表互为排列 <-> 它们对所有元素的计数相同
--   have h_perm : seq ~ canonical := by
--     rw [List.perm_iff_count]
--     intro y
--     by_cases hy : y ∈ xs
--     · -- 如果 y 在 xs 里，计算 canonical 中 y 的数量
--       dsimp [canonical]
--       rw [List.count_flatten]
--       -- canonical 是由 replicate 组成的，只有当 x=y 时才有贡献
--       rw [List.sum_map_eq_sum_map_count_of_nodup _ h_nodup]
--       simp only [List.count_replicate, List.count_map]
--       -- 稍微复杂的重写，说明只有 xs 里的 y 会贡献 count y
--       -- 为了简化，这里可以直接用 Mathlib 的强力策略或手动归纳
--       -- 但更简单的思路是：canonical 本质上就是“按 count 重建 seq”
--       sorry -- 这是一个纯组合证明，如果卡住可以用 induction xs 证明
--     · -- 如果 y 不在 xs 里
--       have c1 : seq.count y = 0 := List.count_eq_zero_of_not_mem (mt (h_subset y) hy)
--       have c2 : canonical.count y = 0 := by
--         -- y 不在 xs 里，自然也不在由 xs 生成的 canonical 里
--         sorry
--       rw [c1, c2]

--   -- 3. 排列不改变求和
--   rw [List.Perm.sum_eq h_perm]

--   -- 4. 计算 canonical 的和
--   dsimp [canonical]
--   rw [List.sum_join, List.sum_map_eq_sum_map] -- 分配律

--   -- 5. 证明每一项 (replicate k x).sum = k * x
--   apply congrArg
--   ext x
--   rw [List.sum_replicate, List.nsmul_eq_mul]

-- 这是一个通用的数学事实，不依赖于你主定理里那些复杂的 context
theorem sum_eq_weighted_sum_real (xs seq : List ℝ)
  (h_nodup : xs.Nodup)
  (h_subset : ∀ y ∈ seq, y ∈ xs) :
  (xs.map (fun x => x * (seq.count x : ℝ))).sum = seq.sum := by

  induction xs generalizing seq with
  | nil =>
    -- 【基础情况】xs 为空
    simp
    have : seq = [] := by
      -- 1.【起手式】假设结论是错的 (即 seq ≠ [])
      -- h_contra 就是那个 "seq ≠ []" 的假设
      by_contra h_contra

      -- 2.【拆解结构】既然 seq 不等于空，那它肯定长成 (head :: tail) 的样子
      -- 我们对 seq 进行分类讨论 (cases)
      cases seq with
      | nil =>
        -- 情况 A: seq 是 []
        -- 这直接跟我们的假设 h_contra (seq ≠ []) 打架了
        contradiction

      | cons head tail =>
        -- 情况 B: seq 是 head :: tail
        -- 既然 seq 里有个 head，那 head 就在 seq 里
        have h_in_seq : head ∈ (head :: tail) := by
          simp

        -- 利用题目给的条件 h_subset: seq 里的都在 xs (也就是 []) 里
        have h_in_empty : head ∈ [] := h_subset head h_in_seq

        -- head 居然属于空列表？这是不可能的 (False)
        -- contradiction 会自动发现这个显而易见的荒谬
        contradiction
    -- 3.【结论】既然 seq 只能是 []，那结论自然成立
    rw [this]; simp
  | cons head tail ih =>
    -- 【归纳步骤】xs = head :: tail
    -- 1. 拆解 Nodup 条件
    -- rw [nodup_cons] at h_nodup
    simp at h_nodup

    obtain ⟨h_head_not_in_tail, h_tail_nodup⟩ := h_nodup

    -- 2. 把 seq 分解为两部分：等于 head 的，和不等于 head 的
    -- seq_head: 所有的 head
    -- seq_tail: 剩下的元素 (必然属于 tail)
    let seq_tail := seq.filter (· ≠ head)

    -- 3. 准备归纳假设 (IH) 所需的条件
    have h_subset_tail : ∀ y ∈ seq_tail, y ∈ tail := by
      intro y hy
      simp only [seq_tail, List.mem_filter] at hy
      obtain ⟨h_in_seq, h_ne_head⟩ := hy
      -- 下面是证明逻辑：
      -- 1. 因为 y 在 seq 里，根据 h_subset，y 就在 xs (head::tail) 里
      have h_in_xs := h_subset y h_in_seq

      -- 2. y 在 head::tail 里，意味着 y = head 或者 y ∈ tail
      rw [List.mem_cons] at h_in_xs

      -- 3. 排除掉 y = head 的情况（因为 h_ne_head）
      cases h_in_xs with
      | inl h_eq =>
          -- 矛盾：那边说不相等，这边说相等
          rw [h_eq] at h_ne_head
          simp at h_ne_head
      | inr h_in_tail =>
          -- 这就是我们要的结论
          exact h_in_tail

    -- 4. 展开左边 (LHS)
    simp only [List.map_cons, List.sum_cons]
    -- LHS 现在是: head * count head seq + (tail.map ...).sum

    -- 5. 应用归纳假设到 tail 部分
    -- 注意：我们需要证明 count x seq = count x seq_tail (对于 x ∈ tail)
    have h_counts_eq : (tail.map (fun x => x * (seq.count x : ℝ))).sum =
                       (tail.map (fun x => x * (seq_tail.count x : ℝ))).sum := by
      apply congrArg
      apply List.map_congr_left
      intro x hx_in_tail
      congr 1
      -- 关键：因为 x 在 tail 里，且 xs 无重复，所以 x ≠ head
      -- 在不等于 head 的前提下，过滤掉 head 不影响 x 的计数
      rw [List.count_filter]
      -- simp
      -- simp only [h_head_not_in_tail x hx_in_tail, Bool.true_and]
      -- x != head 为真
      have h_ne : x ≠ head := ne_of_mem_of_not_mem hx_in_tail h_head_not_in_tail
      -- have : (x == head) = false := by
      --   rw [beq_iff_eq]
      --   apply ne_of_mem_of_not_mem hx_in_tail h_head_not_in_tail
      simp [h_ne]

    rw [h_counts_eq]
    rw [ih seq_tail h_tail_nodup h_subset_tail] -- 这一步把 tail map sum 变成了 seq_tail.sum
    -- 1. 构造排列证明：seq 可以重排为 "等于 head 的部分" 接上 "不等于 head 的部分"
    have h_perm : (seq.filter (· = head) ++ seq.filter (· ≠ head)).Perm seq := by
      simp [List.filter_append_perm (· = head) seq]
    -- 2. 利用排列性质替换求和
    -- List.sum_perm h_perm 说：重排后和不变
    -- List.sum_append 说：连接后的和 = 两部分和相加
    rw [← List.Perm.sum_eq h_perm, List.sum_append]
    congr 1
    -- 1. 把 filter 列表转化为 replicate 列表 (重复列表)
    -- filter (· = a) l = replicate (count a l) a
    rw [List.filter_eq]

    -- 2. 计算 replicate 列表的和
    -- (replicate n a).sum = n • a
    rw [List.sum_replicate]

    -- 3. 处理代数类型：把 nsmul (•) 转化为乘法 (*)
    -- 因为我们在实数域 ℝ，这两个是等价的
    rw [nsmul_eq_mul]
    rw [mul_comm]



lemma psi_maps_to_weight_sum (xs : List ℝ) (seq : List ℝ)
    (h_sorted : xs.Pairwise (· < ·))
    -- (h_nodup : xs.Nodup) -- 需要 xs 无重复元素，h_sorted 蕴含此条件
    (h_subset : ∀ y ∈ seq, y ∈ xs) :
    (List.zipWith (fun k x => (k : ℝ) * x) (psi xs seq) xs).sum = seq.sum := by
  -- 证明思路：
  -- 1. seq.sum 可以按照元素值分组求和： ∑ y = ∑_{x ∈ xs} (count x seq) * x
  -- 2. 右边正是 zipWith (psi seq) xs 的和
  -- let ks := psi xs seq
  let map_list := (List.range xs.length).map (fun i => xs[i]! * (seq.count (xs[i]!) : ℝ))
  have h_map_size : map_list.length = xs.length := by
    unfold map_list; simp
  have h_psi_size :(psi xs seq).length = xs.length := by
    unfold psi; simp
  -- simp [List.length_map, List.length_range]
  have h_forall_map_list :Forall₂ (· = ·) (List.zipWith (fun k x => (k : ℝ) * x) (psi xs seq) xs) map_list := by
    rw [List.forall₂_iff_get]
    constructor
    ·
      simp [List.length_zipWith, h_map_size, h_psi_size]
    ·
      intro i h_len
      simp [List.length_zipWith, h_psi_size] at h_len
      simp
      simp only [← List.map_eq_flatMap]
      simp only [List.getElem_map]
      intro h_lt
      dsimp [map_list]
      simp only [List.getElem_map, List.getElem_range]
      rw [mul_comm]
      -- rw [List.getElem!_eq_getElem xs i h_lt]
      have : xs[i]! = xs[i] := by
        simp [h_len]
      rw [this]
      rw [mul_eq_mul_left_iff]
      left
      dsimp [psi]
      simp only [List.getElem_map]

  have h_eq_map_list: (List.zipWith (fun k x => (k : ℝ) * x) (psi xs seq) xs)=map_list := by
    rw [← List.forall₂_eq_eq_eq]
    exact h_forall_map_list

  have h_transform : map_list = xs.map (fun x => x * (seq.count x : ℝ)) := by
    dsimp [map_list]
    apply List.ext_getElem
    .
      simp only [List.length_map, List.length_range]
    .
      intro i h_lt_left h_lt_right
      simp only [List.getElem_map, List.getElem_range]
      simp at h_lt_right
      have : xs[i]! = xs[i] := by
        simp [h_lt_right]
      rw [this]

  rw [h_eq_map_list, h_transform]
  have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted

  apply sum_eq_weighted_sum_real xs seq h_nodup h_subset

/--
列表求和的一个通用性质：
把列表中等于 a 的项映为 1，不等于的映为 0，
求和的结果就等于 a 在列表中出现的次数。
-/
theorem sum_map_if_eq_count {α : Type*} [DecidableEq α] (l : List α) (a : α) :
  (l.map (fun x => if x = a then 1 else 0)).sum = l.count a := by
induction l with
  | nil => simp
  | cons head tail ih =>
    -- 1. 展开定义
    simp only [List.map_cons, List.sum_cons, List.count_cons]
    rw [ih]
    rw [add_comm]

    -- 2. 聚焦于“头元素”的比较
    -- 目标变成了: (if head = a then 1 else 0) = (if a == head then 1 else 0)
    congr 1

    -- 3. 手动分类讨论 head 和 a 是否相等
    by_cases h : head = a
    · -- 情况 A: 相等
      -- 把所有的 head 都换成 a
      rw [h]
      -- 此时变成: (if a = a ...) = (if a == a ...)
      -- simp 知道 a = a 是 True，a == a 也是 True
      simp

    · -- 情况 B: 不相等 (h : head ≠ a)
      -- 左边: if head = a 是 False
      simp

/--
如果在全集 xs 中统计 seq 的元素个数，总和就是 seq 的长度。
前提：seq 的所有元素都在 xs 里，且 xs 无重复。
-/
theorem sum_map_count_eq_length {α : Type*} [DecidableEq α]
    (xs seq : List α)
    (h_nodup : xs.Nodup)
    (h_subset : ∀ x ∈ seq, x ∈ xs) :
    (xs.map (seq.count ·)).sum = seq.length := by
  -- 对样本 seq 进行归纳，而不是对 xs 归纳
  induction seq with
  | nil =>
    -- 基础情况：seq 为空，两边都是 0
    simp
  | cons y ys ih =>
    -- 准备归纳假设需要的条件
    have h_sub_ys : ∀ x ∈ ys, x ∈ xs := fun x h => h_subset x (List.mem_cons_of_mem y h)
    have hy : y ∈ xs := h_subset y List.mem_cons_self
    -- 1. 展开 count (y :: ys) 为 count ys + (if x==y then 1 else 0)
    simp only [List.count_cons, List.length_cons]

    -- 2. 将 map (a + b) 拆分为 map a + map b
    -- 这里的 cong 稍微有点技巧，把 lambda 里的加法拆开
    have h_split : (xs.map (fun x => ys.count x + if x == y then 1 else 0)).sum =
                   (xs.map (ys.count ·)).sum + (xs.map (fun x => if x == y then 1 else 0)).sum := by
      -- rw [← List.sum_add_distrib]
      -- congr; funext x
      -- 只是单纯的把 nat 加法结合起来
      -- rfl
      simp

    simp

    -- 3. 应用归纳假设 (第一部分)
    rw [ih h_sub_ys]

    -- 4. 处理第二部分 (那个 if 产生的 1)
    congr 1

    have h_swap : (xs.map (fun i => if y = i then 1 else 0)).sum = (xs.map (fun i => if i = y then 1 else 0)).sum := by
      simp only [eq_comm]

    -- 从这一行开始，代码无法识别
    rw [h_swap]
    rw [sum_map_if_eq_count xs y]
    exact List.count_eq_one_of_mem h_nodup hy




/-
定理 1：映射的合法性
如果 seq ∈ Y_X(t; m)，则 psi(seq) ∈ K_X(t)且 m = ks.sum，
-/
theorem psi_mem_K_X (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) (m : ℕ)
    (seq : List ℝ) (h_seq : seq ∈ Y_X xs h_nonempty h_sorted t m) :
    let ks := psi xs seq
    ks ∈ K_X xs h_nonempty h_sorted t ∧ ks.sum = m := by

  let ks := psi xs seq

  -- 从 h_seq 中提取条件
  obtain ⟨h_len, h_subset, h_sum⟩ := h_seq

  have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted

  constructor
  · -- 证明 ks ∈ K_X
    simp only [K_X, Set.mem_setOf_eq]
    constructor
    · -- 1. 长度相等
      unfold psi
      rw [List.length_map]
    · -- 2. 加权和为 t
      rw [psi_maps_to_weight_sum xs seq h_sorted h_subset]
      exact h_sum

  · -- 证明 ks.sum = m
    -- ks.sum = ∑ (count x seq) = seq.length = m
    unfold psi
    rw [sum_map_count_eq_length]
    exact h_len
    exact h_nodup
    exact h_subset


-- ====================================================
-- 2. 证明原像的大小为多项式系数
-- ====================================================

/--
定义：给定一个计数向量 ks，构造一个“标准”序列（Canonical Sequence）
例如 xs=[1,2], ks=[2,1] -> [1, 1, 2]
这是为了利用排列定理。
-/
def canonical_seq (xs : List ℝ) (ks : List ℕ) : List ℝ :=
  (List.zipWith (fun k x => List.replicate k x) ks xs).flatten

/--
通用工具：证明 canonical_seq 里的元素一定来源于 xs
通用工具：证明 canonical_seq 里的元素一定来源于 xs
(使用归纳法，不依赖 mem_zipWith)
-/
theorem mem_canonical_seq {xs : List ℝ} {ks : List ℕ} {y : ℝ} :
    y ∈ canonical_seq xs ks → y ∈ xs := by
  -- 对 xs 和 ks 同时归纳
  induction xs generalizing ks with
  | nil =>
    -- xs 为空，canonical 也是空，不可能有 y
    intro h
    cases ks <;> try contradiction
  | cons x xs_tail ih =>
    cases ks with
    | nil =>
      intro h; simp [canonical_seq] at h;
    | cons k ks_tail =>
      intro h
      -- 展开定义
      simp only [canonical_seq, List.zipWith_cons_cons, List.flatten_cons] at h

      -- y 要么在头部 (replicate k x)，要么在尾部
      rw [List.mem_append] at h
      rcases h with hy_head | hy_tail
      · -- 情况 1: y 在头部 -> y = x
        rw [List.mem_replicate] at hy_head
        rw [hy_head.2]
        exact List.mem_cons_self
      · -- 情况 2: y 在尾部 -> y ∈ xs_tail (由归纳假设)
        right
        -- 这里需要稍微调整一下参数来调用 IH
        -- canonical_seq xs_tail ks_tail 正是我们要的东西
        -- apply ih (y := y)
        exact ih hy_tail


/--
引理 0 (修正版)：canonical_seq 生成的序列属于 Y_X
我们只证明它满足：
1. 长度为 m
2. 所有元素都在 xs 里
3. 和为t

【内部核心引理】
干脏活的：不涉及 K_X 集合定义，纯粹处理 List 递归逻辑。
允许 t 和 m 在递归中变化。
-/
private theorem canonical_seq_core {xs : List ℝ} {ks : List ℕ}
    (h_len : ks.length = xs.length)
    (m : ℕ) (h_sum_m : ks.sum = m)
    (t : ℝ) (h_weighted :  (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t):
    let seq := canonical_seq xs ks
    seq.length = m ∧ (∀ y ∈ seq, y ∈ xs) ∧ seq.sum = t := by
  induction xs generalizing ks m t with
  | nil =>
    cases ks <;> try contradiction
    simp [canonical_seq] at h_weighted ⊢
    constructor
    .
      simp at h_sum_m; exact h_sum_m
    .
      exact h_weighted
  | cons x xs_tail ih =>
    cases ks with
    | nil => contradiction
    | cons k ks_tail =>
      simp at h_len
      simp only [canonical_seq, List.zipWith_cons_cons, List.flatten_cons]

      -- 准备递归参数
      let m_tail := ks_tail.sum
      -- let t_tail := (List.zipWith (fun k x => (k : ℝ) * x) ks_tail xs_tail).sum
      -- 2. 【关键修复】调用归纳假设
      -- 我们传入 `_` 作为 t 的参数，并传入 `rfl` 作为证明。
      -- Lean 会自动推断出 t 必须等于 (zipWith ...).sum
      have h_ih := ih h_len m_tail rfl _ rfl

      -- 解包归纳结果
      rcases h_ih with ⟨h_len_tail, h_mem_tail, h_sum_tail⟩

      refine ⟨?_, ?_, ?_⟩
      · -- 1. 计算长度
        rw [List.length_append, List.length_replicate]
        rw [canonical_seq] at h_len_tail
        rw [h_len_tail]
        simp at h_sum_m; exact h_sum_m
      · -- 2. 证明元素属于 xs
        intro y hy
        rw [List.mem_append] at hy
        rcases hy with hy_head | hy_tail
        · -- 来自头部 replicate 的元素
          rw [List.mem_replicate] at hy_head
          rw [hy_head.2]
          exact List.mem_cons_self
          -- exact List.mem_cons_of_mem y (by rw [hy_head.2]; exact List.mem_cons_self _ _)
        ·
          right; exact h_mem_tail y hy_tail
      · -- 3. 计算和
        rw [List.sum_append, List.sum_replicate]
        rw [canonical_seq] at h_sum_tail
        rw [h_sum_tail]
        rw [nsmul_eq_mul]
        simp at h_weighted
        simp
        -- simp only [List.zipWith_cons_cons, List.sum_cons] at h_weighted
        exact h_weighted

/--
【主定理】
直接使用 ks ∈ K_X 作为前提。
证明：如果 ks 来自 K_X，并且总个数是 m，那么生成的序列一定属于 Y_X。
-/
theorem canonical_mem_Y_X (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (t : ℝ) (m : ℕ)
    (ks : List ℕ)
    -- 【关键】直接引入 K_X 条件
    (h_ks_mem : ks ∈ K_X xs h_nonempty h_sorted t)
    (h_m : ks.sum = m) :
    canonical_seq xs ks ∈ Y_X xs h_nonempty h_sorted t m := by

  -- 1. 拆包 K_X，拿到核心原料
  -- K_X 定义：长度相等 且 加权和为 t
  rw [K_X, Set.mem_setOf_eq] at h_ks_mem
  rcases h_ks_mem with ⟨h_len, h_weighted⟩

  -- 2. 展开 Y_X 目标
  rw [Y_X, Set.mem_setOf_eq]
  simp at h_weighted
  simp only [← List.map_eq_flatMap] at h_weighted

  rw [List.zipWith_map_left] at h_weighted
  -- 3. 直接调用核心引理，把拆出来的原料喂进去
  -- 这里的逻辑非常顺滑：K_X 给了我们需要的一切，core 负责把这些转化为 Y_X 需要的属性
  exact canonical_seq_core h_len m h_m t h_weighted


/--
引理 A：右逆性质 (Right Inverse)
证明：如果 xs 无重复，那么"还原再计数"等于"原始计数"。
即：psi (canonical(ks)) = ks
-/
theorem psi_canonical_eq_self (xs : List ℝ)
    (h_nodup : xs.Nodup)
    (ks : List ℕ)
    (h_len : ks.length = xs.length) :
    psi xs (canonical_seq xs ks) = ks := by

  -- 依然是对 xs 和 ks 归纳
  induction xs generalizing ks with
  | nil =>
    cases ks <;> try contradiction
    rfl

  | cons x xs_tail ih =>
    cases ks with
    | nil => contradiction
    | cons k ks_tail =>
      simp at h_len
      -- 拆解 Nodup：x 不在 tail 里，tail 自身无重复
      rw [List.nodup_cons] at h_nodup
      rcases h_nodup with ⟨h_x_not_in_tail, h_nodup_tail⟩

      -- 展开 canonical
      simp only [canonical_seq, List.zipWith_cons_cons, List.flatten_cons]

      -- 展开 psi (利用 map_cons)
      rw [psi, List.map_cons]

      -- 我们需要证明两件事：头部=k，尾部=ks_tail
      congr 1

      -- 【部分 1】证明头部计数正确: count x (...) = k
      · rw [List.count_append, List.count_replicate_self]
        -- 此时只需证: count x (canonical tail) = 0
        -- 这等价于证: x ∉ canonical tail
        simp only [add_eq_left]
        apply List.count_eq_zero_of_not_mem
        intro h_in
        -- 🌟 关键一击：调用刚才写好的工具
        have h_in_tail := mem_canonical_seq h_in
        -- x 在 tail 里，这就矛盾了
        exact h_x_not_in_tail h_in_tail

      -- 【部分 2】证明尾部计数正确: psi tail (...) = ks_tail
      · -- 目标: psi xs_tail (replicate ++ canonical) = ks_tail

        -- 1. 使用传递性：中间插入 "psi (canonical)"
        -- 也就是证明: psi (replicate ++ canonical) = psi (canonical) = ks_tail
        trans psi xs_tail (canonical_seq xs_tail ks_tail)
        -- 【阶段一】证明: 加上 replicate 不改变 psi 结果
        ·
          rw [psi]
          apply List.map_congr_left
          intro y hy
          -- 此时目标: count y (replicate ++ canonical) = count y (canonical)
          rw [List.count_append]
          -- 证明 replicate 部分为 0
          have h_rep_zero : (List.replicate k x).count y = 0 := by
            rw [List.count_replicate, if_neg]
            -- 理由: y ∈ tail 而 x ∉ tail
            intro h_eq_bool
            rw [beq_iff_eq] at h_eq_bool
            rw [← h_eq_bool] at hy
            exact h_x_not_in_tail hy
          rw [h_rep_zero, zero_add]
          rw [canonical_seq]
        ·
          exact ih h_nodup_tail ks_tail h_len



/--
定理 2：原像计数公式
对于任意 ks ∈ K_X(t)，满足 psi(seq) = ks 的序列 seq 的数量
等于多项式系数 (ks.sum)! / (k₀! * k₁! * ...)

核心引理 2：逐元素计数相等
证明：对于 xs 中的元素 y，"还原后再计数"的结果 等于 "原始计数"。
(这是 seq_perm_canonical 的心脏)
-/
theorem count_canonical_psi_eq {xs : List ℝ} (h_nodup : xs.Nodup)
    (seq : List ℝ) (y : ℝ) (hy : y ∈ xs) :
    (canonical_seq xs (psi xs seq)).count y = seq.count y := by
  induction xs with
  | nil => contradiction -- hy 说 y ∈ []，矛盾
  | cons x xs_tail ih =>
    -- 1. 拆解 Nodup 条件
    rw [List.nodup_cons] at h_nodup
    rcases h_nodup with ⟨h_x_not_in_tail, h_nodup_tail⟩
    rw [psi, List.map_cons]
    -- 2. 展开定义
    simp only [canonical_seq, List.zipWith_cons_cons, List.flatten_cons]

    -- rw [psi, List.map_cons]
    rw [List.count_append]

    -- 3. 分情况讨论 y 是否等于 x
    by_cases h_eq : y = x
    · -- 情况 A: y = x
      rw [h_eq]
      -- replicate 部分的计数就是 (seq.count x)
      rw [List.count_replicate_self]

      -- tail 部分的计数必须是 0
      have h_tail_zero : count x (canonical_seq xs_tail (psi xs_tail seq)) = 0 := by
        apply List.count_eq_zero_of_not_mem
        intro h
        -- 如果 x 在 canonical tail 里，那它就在 xs_tail 里 (引用工具 1)
        exact h_x_not_in_tail (mem_canonical_seq h)
      simp only [canonical_seq, psi] at h_tail_zero
      rw [h_tail_zero, add_zero]
      -- psi 的头部定义正是 seq.count x，证毕
      -- simp

    · -- 情况 B: y ≠ x
      -- replicate 部分贡献为 0
      rw [List.count_replicate]
      have h_ne : x ≠ y := Ne.symm h_eq
      rw [beq_false_of_ne h_ne]
      simp

      -- y 肯定在 xs_tail 里 (因为 y ∈ x::tail 且 y≠x)
      rw [List.mem_cons] at hy
      rcases hy with rfl | hy_tail
      · contradiction -- 已经被 h_eq 排除

      -- 直接调用归纳假设
      exact ih h_nodup_tail hy_tail

/--
引理 B (最终版)：排列关系
证明：如果 seq 的元素都在 xs 里，那么 seq 就是 canonical(psi(seq)) 的一个排列。
-/
theorem seq_perm_canonical {xs : List ℝ}
    (h_nodup : xs.Nodup)
    (seq : List ℝ)
    (h_mem : ∀ y ∈ seq, y ∈ xs) :
    seq.Perm (canonical_seq xs (psi xs seq)) := by

  -- 策略：证明任意元素的 count 相等
  rw [List.perm_iff_count]
  intro y

  -- 分情况讨论：y 是否在 xs 里
  by_cases hy : y ∈ xs

  · -- 情况 1: y ∈ xs
    -- 直接调用核心引理 2
    -- 注意：这里左右边反了一下，不过等式是对称的
    rw [count_canonical_psi_eq h_nodup seq y hy]

  · -- 情况 2: y ∉ xs
    -- 左边 seq.count y = 0
    rw [List.count_eq_zero_of_not_mem]
    · -- 右边 canonical.count y = 0
      rw [List.count_eq_zero_of_not_mem]
      · intro h_in
        apply hy
        exact mem_canonical_seq h_in -- 引用工具 1
    · -- 证明左边为0的条件
      intro h_in
      apply hy
      exact h_mem y h_in

/--
辅助引理：排列不改变 psi 的结果
如果 l₁ ~ l₂ (是排列关系)，那么 psi xs l₁ = psi xs l₂
-/
theorem perm_implies_psi_eq {xs : List ℝ} {l₁ l₂ : List ℝ} (h : l₁ ~ l₂) :
    psi xs l₁ = psi xs l₂ := by
  -- psi 的定义是 map count
  rw [psi, psi]
  -- map 出来的结果相等，只要每个元素的 count 相等
  apply List.map_congr_left
  intro x _ -- 这里的 _ 是 x ∈ xs，但我们不需要它
  -- Perm 的核心性质：排列后的列表，对任意元素的计数相等
  exact List.Perm.count_eq h x

/--
集合等价定理：
{ seq ∈ Y_X | psi(seq) = ks }  <===>  { seq | seq ~ canonical(ks) }
-/
theorem preimage_eq_permutations (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (ks : List ℕ)
    (m : ℕ) (h_m : ks.sum = m)
    (t : ℝ) (h_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t) -- 注意这里的类型可能带有 do/map
    (h_len : ks.length = xs.length) :
    { seq | seq ∈ (Y_X xs h_nonempty h_sorted t m) ∧ psi xs seq = ks } = { seq | seq ~ canonical_seq xs ks } := by

  -- 证明两个集合相等，就是证明元素互属
  ext seq
  have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted

  constructor


  -- ==========================================
  -- 方向 1: 左 -> 右 (Forward)
  -- 证明：如果 seq 满足条件，那它一定是 canonical 的排列
  -- ==========================================
  · intro h
    rcases h with ⟨h_in_Y, h_psi_eq⟩

    -- 1. 既然 seq 在 Y_X 里，它的元素肯定都在 xs 里
    rw [Y_X] at h_in_Y; simp at h_in_Y
    rcases h_in_Y with ⟨_, h_mem_xs, _⟩

    -- 2. 调用我们要塞 Pillar 3 (seq_perm_canonical)
    -- 它告诉我们：seq ~ canonical(psi(seq))

    have h_perm := seq_perm_canonical h_nodup seq h_mem_xs

    -- 3. 因为已知 psi(seq) = ks，替换一下
    rw [h_psi_eq] at h_perm
    exact h_perm

  -- ==========================================
  -- 方向 2: 右 -> 左 (Backward)
  -- 证明：如果是 canonical 的排列，那它一定满足条件
  -- ==========================================
  · intro h_perm
    -- 我们需要证明两件事：1. seq ∈ Y_X   2. psi seq = ks
    constructor

    -- 【准备工作】先拿到 canonical 自身的完美性质 (Pillar 1)
    -- 这里我们需要处理一下 h_t 的格式，以匹配 core 的要求
    have h_t_clean : (List.zipWith (fun k x => (k:ℝ) * x) ks xs).sum = t := by
       -- 这里的处理取决于 h_t 具体被 Lean 识别成什么
       -- 如果遇到 flatMap (do)，用这个：
       try simp only [← List.map_eq_flatMap] at h_t
       -- 如果遇到 map cast，用这个：
       try rw [List.zipWith_map_left] at h_t
       exact h_t

    -- 现在召唤 canonical_seq_core

    have h_core := canonical_seq_core h_len m h_m t h_t
    rcases h_core with ⟨h_can_len, h_can_mem, h_can_sum⟩

    -- 【目标 1】证明 seq ∈ Y_X
    · rw [Y_X]; simp
      refine ⟨?_, ?_, ?_⟩

      -- 1.1 长度相等？
      -- 排列不改变长度，canonical 长度是对的
      · rw [List.Perm.length_eq h_perm, h_can_len]

      -- 1.2 元素都在 xs 里？
      -- 排列不改变元素归属
      · intro y hy
        apply h_can_mem
        -- seq 有 y -> canonical 有 y
        exact (List.Perm.mem_iff h_perm).mp hy

      -- 1.3 和为 t ?
      -- 排列不改变 Sum
      · rw [List.Perm.sum_eq h_perm, h_can_sum]

    -- 【目标 2】证明 psi seq = ks
    · -- 利用辅助引理：排列不改变 psi
      rw [perm_implies_psi_eq h_perm]
      -- 现在变成了证明: psi (canonical) = ks
      -- 这正是我们的 Pillar 2 (右逆性质)
      exact psi_canonical_eq_self xs h_nodup ks h_len

open Nat
#check Fintype.card
/--
终极定理：基数等于多项式系数
Fintype.card { seq ∈ Y_X | psi(seq) = ks } = Nat.multinomial ks
-/
theorem card_preimage_eq_multinomial (xs : List ℝ)
    (h_nonempty : xs ≠ [] ∧ xs[0]! > 0)
    (h_sorted : xs.Pairwise (· < ·))
    (ks : List ℕ)
    (m : ℕ) (h_m : ks.sum = m)
    (t : ℝ) (h_t : (List.zipWith (fun k x => (k : ℝ) * x) ks xs).sum = t)
    (h_len : ks.length = xs.length) :
    -- Fintype.card { seq // (seq ∈ (Y_X xs h_nonempty h_sorted t m)) ∧ psi xs seq = ks } = Nat.multinomial ks := by
    Set.ncard { seq | (seq ∈ (Y_X xs h_nonempty h_sorted t m)) ∧ psi xs seq = ks } = m ! / (ks.map factorial).prod := by

-- 1. 【偷天换日】引用集合等价定理
  -- 我们把目标集合替换成 canonical 的排列集合
  -- 注意：我们直接操作 Set，而不是 Fintype
  have h_nodup : xs.Nodup := pairwise_lt_nodup h_sorted
  rw [preimage_eq_permutations xs h_nonempty h_sorted ks m h_m t h_t h_len]

  -- 现在目标变成了: Set.ncard { seq | seq ~ canonical } = ...

  -- 2. 【利用有限性】
  -- 我们需要告诉 Lean: "排列集合是有限的，可以用 Fintype 计算"
  -- Mathlib 已经知道 { l | l ~ canonical } 是有限的

  -- 把 Set.ncard 转化为 Fintype.card
  -- rw [Set.ncard_eq_toFinset_card]

  -- 这时候 Lean 需要知道 { l | l ~ canonical } 是有限的
  -- 幸好 Mathlib 有 instance : Fintype { l | l ~ canonical }
  -- 但我们需要显式把 Set 转成 Fintype 能够识别的形式，或者利用 list.permutations 的性质

  -- 更简单的路：直接利用 List.card_permutations 公式
  -- List.card_permutations 给出的就是 Fintype.card { l' // l' ~ l }
  -- 我们需要把 Set.ncard 桥接到 Fintype.card 上
  let ms : Multiset ℝ := ↑(canonical_seq xs ks)
  have h_set_eq : { seq : List ℝ | seq ~ canonical_seq xs ks } = { seq : List ℝ | ↑seq = ms } := by
    apply Set.ext
    -- ext seq
    intro seq
    dsimp only [ms]
    -- rw [Set.mem_setOf_eq, Set.mem_setOf_eq]
    exact Multiset.coe_eq_coe.symm
  rw [h_set_eq]
  -- let ms := Multiset.ofList (canonical_seq xs ks)
-- 3. 显式调用 ncard 转换定理
-- 证明有限性：{ l | ↑l = ms } 等价于 canonical_seq 的所有排列

-- 证明有限性：{ l | ↑l = ms } 等价于 canonical_seq 的所有排列
  have h_finite : { seq : List ℝ | ↑seq = ms }.Finite := by
    -- 1. 证明集合 S = { l | ↑l = ms } 等于 List.permutations (canonical_seq ...) 的成员集合
    -- 我们不调用 .toSet，而是直接写成 { seq | seq ∈ ... }
    have h_eq : { seq : List ℝ | ↑seq = ms } = { seq | seq ∈ (canonical_seq xs ks).permutations } := by
      ext seq
      -- 核心：Perm <-> Coe_eq_coe
      simp only [Set.mem_setOf_eq]
      rw [List.mem_permutations]
      dsimp [ms]
      rw [← Multiset.coe_eq_coe]
      -- rw [Set.mem_setOf_eq, List.mem_permutations, ← Multiset.coe_eq_coe]
      -- rfl

    -- 2. 利用 h_eq 和 List.finite_toSet
    rw [h_eq]

    -- 直接应用你找到的定理：List.finite_toSet
    -- 它证明了 { x | x ∈ l } 是有限的
    exact List.finite_toSet (canonical_seq xs ks).permutations

  let h₁_s := h_finite.toFinset
  rw [@Set.ncard_eq_toFinset_card _ _ h_finite]
  rw [← Fintype.card_coe]
  -- sorry
  -- #check Nat.multinomial_spec
  -- 4. 调用 Multiset 的基数定理
  -- rw [Multiset.card_coe]

  -- 5. 对账 Nat.multinomial 定义
  -- rw [Nat.multinomial_def]
  congr 1

  -- 5.1 分子对账：ms.card = m
  · dsimp [ms]
    rw [Multiset.coe_card, ← h_m]
    simp only [canonical_seq, List.length_flatten, List.map_zipWith]
    rw [List.map_zipWith_left (fun k x => (List.replicate k x).length)]
    · simp [List.length_replicate]; rfl
    · exact h_len

  -- 5.2 分母对账：Π (count)! = Π (k!)
  · dsimp [ms]
    -- 替换 ks
    have h_ks_sub : ks = xs.map (fun x => (canonical_seq xs ks).count x) := by
       apply List.ext_get
       · rw [List.length_map, h_len]
       · intro i hi _
         rw [List.get_map, List.get_of_eq (psi_canonical_eq_self xs h_nodup ks h_len).symm]
         rw [psi]; simp only [List.get?_map, List.map_map]; rfl
    nth_rw 1 [h_ks_sub]
    rw [List.map_map]

    -- 转化 Finset.prod 域
    rw [List.prod_eq_prod_toFinset_of_nodup h_nodup]
    rw [Multiset.coe_toFinset]
    apply Finset.prod_subset
    · intro x hx; rw [List.mem_toFinset] at hx ⊢; exact mem_canonical_seq hx
    · intro x _ h_miss; rw [List.mem_toFinset] at h_miss
      rw [Multiset.coe_count, List.count_eq_zero_of_not_mem h_miss]; rfl
