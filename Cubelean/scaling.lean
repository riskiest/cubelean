import Mathlib
-- 假设你之前的定义在一个叫 Cubelean.multinomial 的包里，或者直接把上一段代码放在前面
import Cubelean.new_composition

open BigOperators

-- ==========================================
-- 1. 定义部分
-- ==========================================

/-- 定义标量乘法：将集合中每个元素乘以 a -/
noncomputable def scale (a : ℝ) (xs : Finset ℝ) : Finset ℝ :=
  xs.image (fun x => a * x)

-- ==========================================
-- 2. 辅助引理 (为证明做准备)
-- ==========================================

/-- 引理：如果 xs 里的数都是正的，且 a > 0，那么 a * xs 里的数也都是正的 -/
lemma h_pos_scale {xs : Finset ℝ} {a : ℝ} (ha : 0 < a) (h_pos : ∀ x ∈ xs, 0 < x) :
    ∀ y ∈ scale a xs, 0 < y := by
  intro y hy
  -- 展开 scale 的定义：y 是由某个 x 乘以 a 得到的
  rw [scale, Finset.mem_image] at hy
  rcases hy with ⟨x, hx, rfl⟩
  -- 证明 a * x > 0
  apply mul_pos ha
  exact h_pos x hx

/-- 引理：由于 a > 0，乘法是单射 (Injective)。
    这对求和很重要，防止 a*x1 = a*x2 导致两个不同的元素合并成一个，弄乱概率和。 -/
lemma scale_inj {a : ℝ} (ha : 0 < a) :
    Function.Injective (fun x => a * x) := by
  intro x y h
  simp only [mul_eq_mul_left_iff, ne_of_gt ha] at h
  tauto

/-- 引理：缩放后的集合非空 当且仅当 原集合非空 -/
lemma scale_nonempty_iff {a : ℝ} {xs : Finset ℝ} :
    (scale a xs).Nonempty ↔ xs.Nonempty := by
  simp [scale, Finset.image_nonempty]

-- ==========================================
-- 3. 主定理证明
-- ==========================================

/--
  定理：线性缩放不变性
  对于任意 a > 0，reachProb(xs, t) = reachProb(a*xs, a*t)
-/
theorem reachProb_scale (xs : Finset ℝ) (h_pos : ∀ x ∈ xs, 0 < x)
    (a : ℝ) (ha : 0 < a) (t : ℝ) :
    reachProb xs h_pos t = reachProb (scale a xs) (h_pos_scale ha h_pos) (a * t) := by

  -- 使用函数自带的归纳原理
  induction t using reachProb.induct xs h_pos with
  | case1 t  =>
    -- 【情况 1】: t = 0
    -- 此时 t ≤ 0 且 t = 0
    -- subst ht_zero -- t 变成 0
    simp [reachProb, reachProb] -- 展开两边
    -- 0 * a = 0, 所以两边都是 if 0 ≤ 0 then (if 0=0 then 1) ...

  | case2 t ht_le_zero ht_ne_zero =>
    -- 【情况 2】: t < 0
    rw [reachProb, reachProb]
    -- have h_t_neg : t < 0 := lt_of_le_of_ne ht_le_zero ht_ne_zero
    -- have h_at_neg : a * t < 0 := by simp [mul_neg_of_pos_of_neg ha h_t_neg]
    -- 左边 t ≤ 0 且 t ≠ 0 -> 0
    simp [ht_le_zero, ht_ne_zero]
    -- 右边 a * t ≤ 0 且 a * t ≠ 0
    have ha_t_le : a * t ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt ha) ht_le_zero
    have ha_t_ne : a * t ≠ 0 := mul_ne_zero (ne_of_gt ha) ht_ne_zero
    simp [ha_t_le]
    linarith
  | case3 t ht_pos h_ne ih =>
    -- 1. 准备条件
    have h_scale_ne : (scale a xs).Nonempty := scale_nonempty_iff.mpr h_ne
    have ha_t_pos : 0 < a * t := mul_pos ha (lt_of_not_ge ht_pos)
    -- 2. 证明 c ≠ 0，这是消去它的前提
    have hc_ne_zero : c ≠ 0 := by
      simp [c]
    -- 2. 展开 reachProb
    rw [reachProb, reachProb]
    simp [ht_pos, h_ne, not_le.mpr ha_t_pos, h_scale_ne]
    simp [hc_ne_zero]
    -- 3. 剥离系数 c
    -- congr 1

    -- 4. 展开 scale 定义
    simp [scale]

    -- 5. 【核心】使用 sum_bij 直接建立映射
    -- 我们不试图消除 attach，而是直接证明：
    -- 左边的集合 (xs.attach) 和 右边的集合 ((image... ).attach) 是一一对应的
    -- 映射关系是：左边的 x 映射到 右边的 a * x
    apply Finset.sum_bij (fun x _ => ⟨a * x, by
      -- 证明 a*x 在 image 集合里
      rw [Finset.mem_image]
      exact ⟨x, x.2, rfl⟩
    ⟩)

    · -- 证明映射后的元素确实在目标集合里（上面已经证过了，这里走个过场）
      intro x hx
      simp

    · -- 证明单射：a*x = a*y -> x=y
      intro x hx y hy h_eq
      simp at h_eq
      simp [ne_of_gt ha] at h_eq
      exact h_eq

    · -- 证明满射：对于右边的任意元素 y，都能找到左边的 x
      intro y hy
      rcases y with ⟨val, hval⟩
      -- simp at hy
      rw [Finset.mem_image] at hval
      rcases hval with ⟨x_origin, hx_mem, rfl⟩
      -- hy 说 y 在 image 里，所以存在一个 x 使得 a*x = y
      -- rcases hy with ⟨val, ⟨x, hx_mem, rfl⟩, h_eq⟩
      -- 我们找到了这个 x，构造它
      -- simp
      refine ⟨⟨x_origin, hx_mem⟩, ?_, ?_⟩
      · simp -- 证明 x 在左边集合里
      · -- 证明映射过去确实等于 y
        simp

    · -- 证明值相等：f(x) = g(map(x))
      intro x hx
      -- 这里的 x 是 Subtype，可以直接传给归纳假设
      specialize ih x
      simp
      -- 左边是 reachProb ... (t - x)
      -- 右边是 reachProb ... (a*t - a*x)
      -- 利用分配律：a*t - a*x = a*(t - x)
      rw [← mul_sub]
      exact ih
  | case4 t ht_pos h_empty =>
    -- 【情况 4】: t > 0 但 xs 为空
    rw [reachProb, reachProb]
    -- 左边
    simp [ht_pos, h_empty]
    -- 右边
    have h_t_pos : 0 < t := lt_of_not_ge ht_pos
    have h_at_pos : 0 < a * t := mul_pos ha h_t_pos
    simp [not_le.mpr h_at_pos, scale_nonempty_iff, h_empty]
