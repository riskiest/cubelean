# 多重集排列数公式 (Lean 4 证明) 数学推导文档

## 1. 简介

本文档旨在阐述 Lean 4 代码 `card_permutations_eq_multinomial` 背后的数学原理。该定理证明了多重集（Multiset）的全排列数量等于多项式系数（Multinomial Coefficient）。

### 核心定理
设 $`m`$ 是一个多重集，其基数（总元素个数）为 $`n = |m|`$。
设 $`S`$ 是 $`m`$ 的所有排列组成的集合（即所有元素之和等于 $`m`$ 的列表集合）：

$$
S = \{ l \in \text{List } \alpha \mid \uparrow l = m \}
$$

我们需要证明 $`S`$ 的基数（即排列数）满足以下公式：

$$
|S| = \frac{n!}{\prod_{x \in \text{supp}(m)} (\text{count}(x, m))!}
$$

其中：
* $`\text{count}(x, m)`$ 表示元素 $`x`$ 在 $`m`$ 中出现的次数（重数）。
* $`\text{supp}(m)`$ 是 $`m`$ 的去重元素集合（即 Lean 中的 `m.toFinset`）。

---

## 2. 证明策略概述

证明分为两个主要阶段：
1.  **建立递推关系**：通过构造双射，证明排列数满足关于子多重集的求和递推关系。
2.  **数学归纳法**：利用上述递推关系，结合代数化简证明多项式系数公式。

---

## 3. 第一阶段：递推关系的建立

### 3.1 构造双射
代码中定义了两个核心函数 `split_list` 和 `combine_list`，建立了如下等价关系：

$$
\{ l \mid \uparrow l = m \} \simeq \coprod_{a \in \text{supp}(m)} \{ l' \mid \uparrow l' = m \setminus \{a\} \}
$$

**数学直觉**：
一个排列是一个有序列表 $`l = [x_1, x_2, \dots, x_n]`$。
* **分解 (`split_list`)**：我们要确定第一个元素 $`x_1`$。$`x_1`$ 可以是 $`m`$ 中的任意一个**不同**的元素 $`a`$（遍历 `m.toFinset`）。一旦选定 $`x_1 = a`$，剩下的列表 $`[x_2, \dots, x_n]`$ 就是多重集 $`m \setminus \{a\}`$ 的一个排列。
* **合并 (`combine_list`)**：给定一个元素 $`a`$ 和一个 $`m \setminus \{a\}`$ 的排列 $`l'`$，我们可以通过 $`a :: l'`$ 构造出 $`m`$ 的一个排列。

### 3.2 得到求和公式
基于上述双射，利用基数的加法原理（对应代码 `card_permutations_sum_recurrence`），我们要证的目标基数 $`N(m)`$ 满足：

$$
N(m) = \sum_{a \in \text{supp}(m)} N(m \setminus \{a\})
$$

---

## 4. 第二阶段：归纳与代数证明

### 4.1 归纳假设
对多重集的大小 $`n`$ 进行归纳。
* **基准情况 ($`n=0`$)**：$`m = \emptyset`$。排列只有空列表，数量为 1。公式右边 $`0! / 1 = 1`$。成立。
* **归纳步骤**：假设对于所有大小为 $`n`$ 的多重集公式成立。现在考虑大小为 $`n+1`$ 的多重集 $`m`$。

### 4.2 核心推导过程
根据递推公式：
$$
N(m) = \sum_{a \in \text{supp}(m)} N(m \setminus \{a\})
$$

由于 $`m \setminus \{a\}`$ 的大小为 $`n`$，应用归纳假设：
$$
N(m \setminus \{a\}) = \frac{n!}{\prod_{x} (\text{count}(x, m \setminus \{a\}))!}
$$

代入递推式，我们需要证明：
$$
\sum_{a \in \text{supp}(m)} \frac{n!}{\prod_{x} (\text{count}(x, m \setminus \{a\}))!} = \frac{(n+1)!}{\prod_{x} (\text{count}(x, m))!}
$$

### 4.3 关键代数化简 (代码中的 `h_item`)
这是代码中最复杂的部分。为了证明上述等式，我们令：
* **总分母** $`D = \prod_{x \in \text{supp}(m)} k_x!`$，其中 $`k_x = \text{count}(x, m)`$。
* **子分母** $`D_a = \prod_{x \in \text{supp}(m \setminus \{a\})} k'_x!`$，其中 $`k'_x = \text{count}(x, m \setminus \{a\})`$。

我们需要证明每一项满足：
$$
\frac{n!}{D_a} \cdot D = n! \cdot k_a
$$

一旦证明了这一点，求和式变为：
$$
\sum_a \frac{n!}{D_a} = \sum_a \frac{n! \cdot k_a}{D} = \frac{n!}{D} \sum_a k_a = \frac{n!}{D} \cdot (n+1) = \frac{(n+1)!}{D}
$$
这就证明了原命题。

#### 4.3.1 证明 $`D = D_a \cdot k_a`$
在代码的 `h_D_sub` 和 `h_sep` 部分，详细处理了分母之间的关系。

对于选定的元素 $`a`$：
1.  **当 $`x \neq a`$ 时**：$`k'_x = k_x`$。
2.  **当 $`x = a`$ 时**：$`k'_a = k_a - 1`$。

因此，子分母 $`D_a`$ 可以写为：
$$
D_a = (k_a - 1)! \cdot \prod_{x \neq a} k_x!
$$

而总分母 $`D`$ 可以写为：
$$
D = k_a! \cdot \prod_{x \neq a} k_x! = k_a \cdot (k_a - 1)! \cdot \prod_{x \neq a} k_x!
$$

显而易见：
$$
D = k_a \cdot D_a \implies \frac{D}{D_a} = k_a
$$

#### 4.3.2 处理 $`k_a=1`$ 的边界情况 (代码 `by_cases ki=1`)
在 Lean 代码中，这部分通过 `by_cases` 单独处理，因为当 $`k_a=1`$ 时，移除元素会导致集合的拓扑结构发生变化（元素从 `toFinset` 中消失）。

* **数学上**：如果 $`k_a = 1`$，则 $`k'_a = 0`$，且 $`0! = 1`$。公式依然成立。
* **Lean 实现上**：当 $`k_a = 1`$ 时，元素 $`a`$ 会从 `toFinset` 中消失。代码证明了：
    $$
    \prod_{x \in \text{supp}(m \setminus \{a\})} k'_x! = 1 \cdot \prod_{x \in \text{supp}(m) \setminus \{a\}} k_x!
    $$
    这与 $`(1-1)! = 0! = 1`$ 完美对应。

---

## 5. 代码实现与数学步骤对照表

| 数学步骤 | 代码位置 | 说明 |
| :--- | :--- | :--- |
| **全排列分解** | `list_sigma_equiv` | 将 $`N(m)`$ 拆解为 $`\sum N(m \setminus \{a\})`$ |
| **归纳假设代入** | `rw [ih ...]` | 将子问题的解替换为多项式系数公式 |
| **定义 $`D`$ 和 $`D_a`$** | `let den := ...` | 定义总分母，方便通分 |
| **代数变换目标** | `suffices h_mul ...` | 将证明除法和转化为证明乘法积（避免 Nat 除法陷阱） |
| **消去分母** | `h_item` | 核心引理，证明 $`\frac{1}{D_a} \cdot D = k_a`$ |
| **阶乘拆分** | `Nat.mul_factorial_pred` | 对应 $`k! = k \cdot (k-1)!`$ |
| **集合范围修正** | `by_cases h_ki_eq : ki = 1` | 处理当计数为 1 时，元素从集合消失的边界情况 |
| **整除性保证** | `Multiset.prod_factorial...` | 保证 $`\frac{n!}{D_a}`$ 是整数（排列数必为整数） |
| **最终求和** | `rw [multiset_sum_count...]` | 对应 $`\sum k_a = n+1`$ |

## 6. 结论

代码通过构造性的双射证明了递归关系，并通过严谨的代数推导解决了分母阶乘的消去问题，最终利用 `Nat` 上的算术性质（如 `div_mul_cancel`）完成了 $`N(m) = \frac{n!}{\prod k_i!}`$ 的证明。整个过程不仅涵盖了组合数学的逻辑，还处理了形式化证明中特有的类型一致性（如 Multiset 与 Finset 的转换）问题。