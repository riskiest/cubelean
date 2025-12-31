
# 证明文档：ReachProb 的线性缩放不变性 (Linear Scaling Invariance)

## 1. 概述 (Overview)

本文档记录了 `reachProb` 函数的一个核心性质证明：**线性缩放不变性**。

该定理表明，如果将骰子的面值集合 $`xs`$ 和目标值 $`t`$ 同时放大 $`a`$ 倍（$`a > 0`$），其到达目标值的概率保持不变。这是将实数域上的优化问题映射到有理数/整数域的重要理论基础。

### 数学表述

对于任意实数有限集 $`xs \subset \mathbb{R}^+`$，目标值 $`t \in \mathbb{R}`$，以及缩放因子 $`a > 0`$，有：

$$
\text{reachProb}(xs, t) = \text{reachProb}(a \cdot xs, a \cdot t)
$$

其中 $`a \cdot xs = \{ a \cdot x \mid x \in xs \}`$。

---

## 2. 核心定义与引理 (Definitions & Lemmas)

为了在 Lean 4 中形式化该命题，我们首先定义了集合的标量乘法操作。

### 2.1 标量乘法 (`scale`)
我们在 `Finset` 上定义 `scale` 操作，利用 `image` 映射实现：

```lean
noncomputable def scale (a : ℝ) (xs : Finset ℝ) : Finset ℝ :=
  xs.image (fun x => a * x)
```

### 2.2 辅助引理
为了支撑主定理的证明，我们证明了以下三个引理：

1.  **保正性 (`h_pos_scale`)**:
    * **内容**：若 $`\forall x \in xs, x > 0`$ 且 $`a > 0`$，则 $`\forall y \in a \cdot xs, y > 0`$。
    * **作用**：满足 `reachProb` 函数对输入集合元素必须为正的要求。

2.  **单射性 (`scale_inj`)**:
    * **内容**：当 $`a > 0`$ 时，函数 $`f(x) = a \cdot x`$ 是单射 (Injective)。
    * **作用**：保证集合在缩放过程中元素不会发生合并（即集合基数不变），这对求和公式至关重要。

3.  **非空保持 (`scale_nonempty_iff`)**:
    * **内容**：$`xs`$ 非空 $`\iff`$ $`a \cdot xs`$ 非空。
    * **作用**：确保递归定义的基准情况逻辑一致。

---

## 3. 证明策略：良基归纳法 (Well-founded Induction)

由于 `reachProb` 是基于度量函数 (measure) 的递归定义，我们采用**良基归纳法**。

在 Lean 4 中，使用 `induction t using reachProb.induct xs h_pos`，这能完美复刻函数定义中的 `if-else` 分支逻辑，将证明分解为四个情况 (Cases)。

### 3.1 Case 1: $`t = 0`$ (基准情况)
* **逻辑**：根据定义，目标值为 0 时概率为 1。
* **证明**：若 $`t=0`$，则 $`a \cdot t = 0`$。两边展开定义均为 1，等式成立。

### 3.2 Case 2: $`t < 0`$ (基准情况)
* **逻辑**：目标值为负数时概率为 0。
* **证明**：因 $`a > 0`$，若 $`t < 0`$，则 $`a \cdot t < 0`$。两边展开定义均为 0，等式成立。

### 3.3 Case 3: $`t > 0`$ 且 $`xs \neq \emptyset`$ (递归步 - 核心难点)
这是证明中最关键的部分。我们需要证明：

$$
\sum_{x \in xs} \text{reachProb}(xs, t - x) = \sum_{y \in a \cdot xs} \text{reachProb}(a \cdot xs, a \cdot t - y)
$$

*(注：两边的系数 $`c`$ 已被消去)*

**证明步骤**：

1.  **消去常数**：证明 $`c \neq 0`$，利用 `simp` 或 `mul_right_inj'` 消去两边的乘数 $`c`$。
2.  **构造双射 (`Finset.sum_bij`)**：
    * 这是解决 Lean 中类型匹配问题的关键。我们不直接使用 `rw` 重写集合，而是使用 `sum_bij` 显式构造映射关系。
    * **映射函数**：$`\phi(x) = a \cdot x`$。
3.  **验证映射性质**：
    * **合法性**：证明 $`a \cdot x \in a \cdot xs`$ (由 `image` 定义显然)。
    * **单射**：由 $`a > 0`$ 推导 $`ax = ay \implies x = y`$。
    * **满射**：对任意 $`y \in a \cdot xs`$，存在原像 $`x`$ 使得 $`ax = y`$ (由 `rcases` 解构得出)。
4.  **值相等验证**：
    * 利用乘法分配律：$`a \cdot t - a \cdot x = a(t - x)`$。
    * 应用归纳假设 (IH)：$`\text{reachProb}(\dots, t-x) = \text{reachProb}(\dots, a(t-x))`$。

### 3.4 Case 4: $`t > 0`$ 且 $`xs = \emptyset`$ (边界情况)
* **逻辑**：集合为空且目标值大于 0，无法移动，概率为 0。
* **证明**：利用 `scale_nonempty_iff` 引理，若 $`xs`$ 为空，则 $`scale \ a \ xs`$ 也为空。两边均为 0，等式成立。

---

## 4. 关键 Lean 技术点

* **`simp [scale]`**: 显式展开缩放定义，方便 `rcases` 解构，比 `rw` 更稳健。
* **`Finset.sum_bij`**: 代替 `rw` 处理复杂的集合变换求和，规避了 `Subtype` 和 `attach` 带来的类型推断困难。
* **`congr 1`** / **`mul_right_inj'`**: 在不引入额外类型类限制的情况下，剥离等式外层的函数应用（如乘以常数 $`c`$）。
* **`specialize ih x`**: 在归纳证明中，显式地将特定元素喂给归纳假设，使证明逻辑更清晰。

## 5. 结论

本证明严格建立了 `reachProb` 函数的线性缩放不变性。这意味着我们在寻找最优解时，可以将实数域的问题同胚地映射到离散的整数域进行搜索，从而验证了算法设计中“离散化搜索”的数学合法性。