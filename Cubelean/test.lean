import Mathlib

-- --- 剥离辅助引理：关于 List 和 Multiset 的基础操作 ---
/-- 辅助引理：列表的首元素必在其对应的多重集中 -/
lemma head_mem_multiset {α : Type*} {l : List α} {m : Multiset α} (h_empty : l ≠ []) (h_eq : ↑l = m) :
    l.head h_empty ∈ m := by
  rw [← h_eq]
  exact List.head_mem h_empty

variable {α : Type*} [DecidableEq α]

-- --- 核心映射函数 ---

/-- 映射 1：拆分列表为 (头, 尾) -/
def split_list (m : Multiset α) (h_ne : m ≠ 0) (x : { l : List α // ↑l = m }) :
    Σ a : m.toFinset, { l' : List α // ↑l' = m.erase a } :=

  -- 直接匹配 Subtype 的内容：l 是列表，hl 是 ↑l = m 的证明
  match x with
  | ⟨l, hl⟩ =>
    -- 1. 证明 l 非空
    let h_l_ne : l ≠ [] := by
      intro h_empty
      subst h_empty
      simp at hl
      symm at hl
      exact h_ne hl

    let a := l.head h_l_ne
    let lt := l.tail

    -- 3. 构造输出的对子
    ⟨
      -- 第一项 (head)：带证明的 a
      ⟨a, by
        simp [← hl]
        exact List.head_mem h_l_ne⟩,
      -- 第二项 (tail)：带证明的 lt
      ⟨lt, by
        have h_decomp := List.cons_head_tail h_l_ne
        have hl_expanded : ↑(a :: lt) = m := by
          rw [h_decomp, hl]
        rw [← Multiset.cons_coe] at hl_expanded
        simp [← hl_expanded]⟩
    ⟩


/-- 映射 2：合并元素和尾部为完整列表 -/
def combine_list (m : Multiset α) (s : Σ a : m.toFinset, { l' : List α // ↑l' = m.erase a }) :
    { l : List α // ↑l = m } :=
  -- 1. 使用 match 拆解 Sigma 类型，获取具体的 a, lt 以及它们的证明 ha, hlt
  match s with
  | ⟨⟨a, ha_finset⟩, ⟨lt, hlt⟩⟩ =>
    -- 2. 构造 Subtype
    ⟨a :: lt, by
      -- 目标是：↑(a :: lt) = m

      -- 第一步：将列表的 cons 转换为多重集的 cons
      -- 使用你找到的引理：a ::ₘ ↑lt = ↑(a :: lt)
      rw [← Multiset.cons_coe]

      -- 第二步：利用 hlt (↑lt = m.erase a) 进行重写
      rw [hlt]

      -- 第三步：利用引理 a ::ₘ m.erase a = m
      -- 前提是 a ∈ m
      apply Multiset.cons_erase

      -- 将 a ∈ m.toFinset 转换为 a ∈ m
      simpa [Multiset.mem_toFinset] using ha_finset⟩

-- --- 建立等价关系 ---

/-- 核心双射：列表排列集合 ≃ 各分支排列集合的不相交并集 -/
def list_sigma_equiv (m : Multiset α) (h_ne : m ≠ 0) :
    { l : List α // ↑l = m } ≃ Σ a : m.toFinset, { l' : List α // ↑l' = m.erase a } where
  toFun := split_list m h_ne
  invFun := combine_list m
  left_inv x := by
    apply Subtype.ext
    simp [split_list, combine_list]
  right_inv s := by
    simp [split_list, combine_list]

-- --- 最终定理证明 ---

noncomputable instance (m : Multiset α) : Fintype { l : List α // ↑l = m } :=
  let L : List { l : List α // ↑l = m } :=
    (Quotient.out m).permutations.attach.map
      (fun p =>
        ⟨p.1, by
          have h_mem := p.2
          rw [List.mem_permutations] at h_mem
          rw [← Multiset.coe_eq_coe] at h_mem
          rw [h_mem]
          exact Quotient.out_eq m
        ⟩)
  Fintype.ofList L
    (by
      intro x
      rcases x with ⟨l, hl⟩
      have h_perm : l ∈ (Quotient.out m).permutations := by
        rw [List.mem_permutations, ← Multiset.coe_eq_coe, hl]
        exact (Quotient.out_eq m).symm
      have h_attach : ⟨l, h_perm⟩ ∈ (Quotient.out m).permutations.attach := List.mem_attach _ _

      rw [List.mem_map]
      use ⟨l, h_perm⟩
      -- constructor
      -- · exact h_attach
      -- · apply Subtype.ext; simp
    )


open BigOperators

theorem card_permutations_sum_recurrence  (m : Multiset α) (h_ne : m ≠ 0) :
    Fintype.card { l : List α // ↑l = m } = ∑ a ∈  m.toFinset, Fintype.card { l : List α // ↑l = m.erase a } := by
  -- 1. 通过双射转换基数计算对象
  rw [Fintype.card_congr (list_sigma_equiv m h_ne)]
  rw [Fintype.card_sigma]
  rw [Finset.univ_eq_attach]
  rw [Finset.sum_attach m.toFinset (fun i => Fintype.card { l : List α // ↑l = m.erase i })]

open Nat

theorem card_permutations_eq_multinomial (m : Multiset α) :
    Fintype.card { l : List α // ↑l = m } = m.card.factorial / (m.toFinset.prod (fun a => (m.count a)!)) := by

  -- Step 1: 使用 suffices 建立一个关于 n 的通用命题
  -- 我们说：只要能证明对于任意 n，所有基数为 n 的多重集都满足公式，那么原命题成立
  suffices h_strong : ∀ n : ℕ, ∀ (ms : Multiset α), ms.card = n →
    Fintype.card { l : List α // ↑l = ms } = ms.card.factorial / (ms.toFinset.prod (fun a => (ms.count a).factorial)) by
    -- 证明 A → B：直接把当前的 m 传入这个通用命题
    exact h_strong m.card m rfl

  intro n
  induction n with
  | zero =>
      -- 此时 m = 0，列表只能是空列表，card 为 1，公式右边也是 1
      simp
  | succ n ih =>
      -- 情况 2: n = k + 1 (递归步骤)
      -- 我们需要用到刚才证出的递归等式
      intro ms h_card
      have h_ne : ms ≠ 0 := by
        intro h; subst h; simp at h_card

      rw [card_permutations_sum_recurrence ms h_ne]
      -- 1. 我们的目标是 ∑ a ∈ ms.toFinset, f a = ...
            -- 我们先用 apply Finset.sum_congr rfl 进入求和号内部
            -- 但由于右边不是求和，我们需要先对左边进行“原地重写”
      have h_sum_replaced : ∑ a ∈ ms.toFinset, Fintype.card { l: List α // ↑l = ms.erase a } =
          ∑ a ∈ ms.toFinset, (ms.erase a).card.factorial / ∏ x ∈ (ms.erase a).toFinset, ((ms.erase a).count x).factorial := by
        apply Finset.sum_congr rfl
        intro a ha
        -- 这里的 a 和 ha 现在是有效的了！
        have mem_a : a ∈ ms := Multiset.mem_toFinset.mp ha
        have : (ms.erase a).card = ms.card - 1 := by
          rw [Multiset.card_erase_of_mem mem_a]
          simp
        have h_card_erase : (ms.erase a).card = n := by
          rw [this, h_card]
          simp
        -- 应用归纳假设
        rw [ih (ms.erase a) h_card_erase]
      rw [h_sum_replaced]

      -- 定义右边的分母，方便后续重写
      let den := ∏ x ∈ ms.toFinset, (ms.count x).factorial
      -- 建议：通过两边同乘 den，转为乘法证明
      suffices h_mul : (∑ a ∈ ms.toFinset, (ms.erase a).card.factorial / ∏ x ∈ (ms.erase a).toFinset, ((ms.erase a).count x).factorial) * den = ms.card.factorial by
        rw [Nat.div_eq_of_eq_mul_left _ h_mul.symm]
        · -- 证明分母不为 0
          apply Nat.pos_of_ne_zero
          apply Multiset.prod_ne_zero
          simp
          intro dx h_dx
          apply Nat.factorial_ne_zero

      -- 1. 将乘法分配进求和号
      rw [Finset.sum_mul]

      -- 2. 将右边的 n! 写成 n * (n-1)! 以便最后对齐
      rw [h_card, Nat.factorial_succ, ← h_card]

      -- 3. 对齐求和项
      -- 目标变为：∑ a, ((n-1)! / den_a) * den = n * (n-1)!
      -- 我们证明内部每一项：((n-1)! / den_a) * den = (n-1)! * ms.count a
      have h_item : ∀ a ∈ ms.toFinset,
        ((ms.erase a).card.factorial / ∏ x ∈ (ms.erase a).toFinset, ((ms.erase a).count x).factorial) * den =
        (ms.erase a).card.factorial * ms.count a := by
        intro a ha
        let mem_a := Multiset.mem_toFinset.mp ha
        let n_sub := (ms.erase a).card
        let ki := ms.count a
        have h_ki_pos : 0 < ki := Multiset.count_pos.mpr mem_a
        have h_ki_ne : ki ≠ 0 := by linarith

        -- 1. 这里的 den = (ki!) * ∏ x ∈ (ms.toFinset.erase a), (ms.count x)!
        -- dsimp only [den]
        -- 1. 明确定义 f 为计算阶乘的函数
        let f := fun x => (ms.count x).factorial

        -- 2. 使用 mul_prod_erase，它只涉及乘法，不涉及除法，在 Nat 上最稳
        have h_sep : den = f a * ∏ x ∈ ms.toFinset.erase a, f x := by
          -- 显式指定我们要用 Finset 的引理，并喂给它正确的参数
          rw [Finset.mul_prod_erase ms.toFinset f ha]

        rw [h_sep]
        -- dsimp only [f]

        -- 1. 证明 f a 的拆解
        have h_fa : f a = ms.count a * (ms.count a - 1).factorial := by
          dsimp [f]
          -- 这个引理专门处理 k! = k * (k-1)!，前提是 k > 0
          rw [Nat.mul_factorial_pred h_ki_ne]
        rw [h_fa]

        -- 3. 整理括号，准备消去分母
        -- 我们希望把 (ki - 1)! 和 prod_erase 凑在一起
        rw [Nat.mul_assoc, Nat.mul_comm (ms.count a) _, ← Nat.mul_assoc]

        -- 4. 证明剩下的那部分乘积正好等于 (ms.erase a) 的分母
        -- 建议定义一个 have
        have h_D_sub : ∏ x ∈ (ms.erase a).toFinset, ((ms.erase a).count x).factorial =
                     (ms.count a - 1).factorial * ∏ x ∈ ms.toFinset.erase a, (ms.count x).factorial := by
        -- 引入变量 ki 方便书写
          let ki := ms.count a

          -- 分类讨论：ki = 1 还是 ki ≠ 1
          by_cases h_ki_eq : ki = 1

          -- Case 1: ki = 1
          · -- 1. 证明集合变小了
            have h_sets : (ms.erase a).toFinset = ms.toFinset.erase a := by
              ext x
              simp
              -- simp only [Multiset.mem_toFinset, Finset.mem_erase, ne_eq]
              -- 这里利用 count_erase_self 和 count_erase_of_ne 的逻辑
              constructor
              ·
                intro h;
                constructor
                .
                  -- 1.2: 证明 x ≠ a
                  intro x_eq_a
                  rw [x_eq_a] at h
                  -- 利用 ki = 1 得出矛盾
                  -- rw [Multiset.count_erase_self, h_ki_eq] at h
                  have h_count : (ms.erase a).count a = 0 := by
                    dsimp [ki] at h_ki_eq
                    rw [Multiset.count_erase_self, h_ki_eq]
                  rw [Multiset.count_eq_zero] at h_count
                  contradiction
                .
                  -- 1.1: 证明 x ∈ ms
                  apply Multiset.mem_of_mem_erase h

              ·
                intro h
                have h_count_ne_zero: (ms.erase a).count x ≠ 0 := by
                  rw [Multiset.count_erase_of_ne]
                  rw [Multiset.count_ne_zero]
                  exact h.2
                  exact h.1
                rw [Multiset.count_ne_zero] at h_count_ne_zero
                exact h_count_ne_zero

            -- 2. 重写左边的集合范围
            rw [h_sets]

            -- 3. 处理右边的 (ki - 1)! = (1-1)! = 0! = 1
            dsimp [ki] at h_ki_eq
            rw [h_ki_eq]
            simp only [Nat.sub_self, Nat.factorial_zero, Nat.one_mul]

            -- 4. 证明剩下的乘积相等 (x ≠ a 时 count 不变)
            apply Finset.prod_congr rfl
            intro x hx
            -- hx 意味着 x ∈ ms.toFinset.erase a，所以 x ≠ a
            have h_ne : x ≠ a := (Finset.mem_erase.mp hx).1
            rw [Multiset.count_erase_of_ne h_ne]

          -- Case 2: ki ≠ 1 (即 ki > 1)
          · -- 1. 此时移除 a 后，a 依然存在，集合范围不变
            have h_sets : (ms.erase a).toFinset = ms.toFinset := by
              ext x
              simp
              constructor
              · intro h
                exact Multiset.mem_of_mem_erase h
              ·
                intro h
                by_cases hx : x = a
                .
                  -- 如果 x = a，因为 ki ≠ 1 且 ki > 0，所以 ki - 1 > 0
                  have h_count : (ms.erase a).count a ≠ 0 := by
                    dsimp [ki] at h_ki_eq
                    simp
                    omega
                  rw [Multiset.count_ne_zero] at h_count
                  rw [hx]
                  exact h_count
                .
                  -- 如果 x ≠ a，保持不变
                  rw [Multiset.mem_erase_of_ne hx]
                  exact h


            -- 2. 重写左边的集合
            rw [h_sets]
            rw [← Finset.mul_prod_erase ms.toFinset (fun x => ((ms.erase a).count x).factorial) ha]

            -- 4. 证明提出来的项和剩下的项分别相等
            congr 1
            · -- 证明头部相等：((erase a).count a)! = (ki - 1)!
              rw [Multiset.count_erase_self]
            · -- 证明尾部相等：对于 x ≠ a，count 不变
              apply Finset.prod_congr rfl
              intro x hx
              rw [Multiset.count_erase_of_ne (Finset.mem_erase.mp hx).1]


        -- have h_D_sub : ∏ x ∈ (ms.erase a).toFinset, ((ms.erase a).count x).factorial =
        --               (ms.count a - 1).factorial * ∏ x ∈ ms.toFinset.erase a, (ms.count x).factorial := by
        --   -- 这里是最后一块硬骨头，涉及到我们之前说的 ki = 1 的分类讨论
        --   sorry

        rw [h_D_sub]
        rw [Nat.div_mul_cancel]
        let mea : Multiset α := ms.erase a
        have h_dvd_ready : ∏ x ∈ mea.toFinset, (mea.count x).factorial ∣ mea.card ! := by
          let f := fun x => mea.count x
          have : mea.card = ∑ x ∈ mea.toFinset, f x := by
            dsimp [f]
            simp
          rw [this]
          exact Nat.prod_factorial_dvd_factorial_sum mea.toFinset f
        rw [← h_D_sub] -- 假设 h_den_eq_part 是你之前证明分母相等的那个 have
        exact h_dvd_ready
        -- 1. 将 f(a) 展开为 k_a * (k_a - 1)!
        -- 这里 f a 就是 (ms.count a).factorial

        -- sorry -- 见下方详细说明
    -- 1. 处理右边的 n!，使其与左边的 (ms.erase i).card! 对齐
      -- 因为 h_card : ms.card = n + 1，所以 n = ms.card - 1
      -- 而 (ms.erase i).card 恰好也是 ms.card - 1
      have h_n : n = (ms.card - 1) := by
        rw [h_card]
        simp

      -- 1. 不要直接 apply sum_congr，因为右边不对称。
      -- 我们先证明左边的求和等于一个新的形式：
      have h_left : ∑ i ∈ ms.toFinset, ((ms.erase i).card ! / ∏ x ∈ (ms.erase i).toFinset, (Multiset.count x (ms.erase i))!) * den =
                    ∑ i ∈ ms.toFinset, ((ms.erase i).card ! * Multiset.count i ms) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact h_item i hi
      rw [h_left]

      have h_left2 : ∑ i ∈ ms.toFinset, ((ms.erase i).card ! * Multiset.count i ms) =
                    ∑ i ∈ ms.toFinset, (n.factorial * Multiset.count i ms) := by
        apply Finset.sum_congr rfl
        intro i hi
        have : (ms.erase i).card = n := by
          rw [Multiset.card_erase_of_mem (Multiset.mem_toFinset.mp hi), h_card]
          simp
        rw [this]
      rw [h_left2]
      -- 4. 提取 (n-1)!
      rw [← Finset.mul_sum]
      rw [mul_comm]
      simp
