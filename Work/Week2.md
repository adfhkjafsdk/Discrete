# 第二次练习题
同学们可以按照自己的时间安排选择其中数道进行尝试。欢迎探索不同的证明方法。题目较多，请同学们量力而行。
## 第二章
### 2.8.1
证明以下推理公式：

(1) $ P \land Q \Rightarrow P $

(2) $ \neg (P \rightarrow Q) \Rightarrow P $

(3) $ \neg (P \rightarrow Q) \Rightarrow \neg Q $

(4) $ P \Rightarrow P \lor Q $

(5) $ \neg P \Rightarrow P \rightarrow Q $

(6) $ Q \Rightarrow P \rightarrow Q $

(7) $ \neg P \land (P \lor Q) \Rightarrow Q $

(8) $ P \land (P \rightarrow Q) \Rightarrow Q $

(9) $ \neg Q \land (P \rightarrow Q) \Rightarrow \neg P $

(10) $ (P \rightarrow Q) \land (Q \rightarrow R) \Rightarrow P \rightarrow R $

(11) $ (P \leftrightarrow Q) \land (Q \leftrightarrow R) \Rightarrow P \leftrightarrow R $

(12) $ (P \rightarrow R) \land (Q \rightarrow R) \land (P \lor Q) \Rightarrow R $

(13) $ (P \rightarrow Q) \land (R \rightarrow S) \land (P \lor R) \Rightarrow Q \lor S $

(14) $ (P \rightarrow Q) \land (R \rightarrow S) \land (\neg Q \lor \neg S) \Rightarrow \neg P \lor \neg R $

(15) $ (Q \rightarrow R) \Rightarrow ((P \lor Q) \rightarrow (P \lor R)) $

(16) $ (Q \rightarrow R) \Rightarrow ((P \rightarrow Q) \rightarrow (P \rightarrow R)) $

### 2.9.2
证明以下题目：

(1) $ (P \rightarrow Q) \land (Q \rightarrow R) \land P \Rightarrow R $

(2) $ (C \vee D) \land ((C \vee D) \rightarrow \neg E) \land (\neg E \rightarrow (A \land \neg B)) \land ((A \land \neg B) \rightarrow (R \vee S)) \Rightarrow R \vee S $

(3) $ (P \vee Q) \land (P \rightarrow R) \land (Q \rightarrow S) \Rightarrow S \vee R $

(4) $ (P \rightarrow (Q \rightarrow S)) \land (\neg R \vee P) \land Q \Rightarrow R \rightarrow S $

(5) $ (\neg(P \rightarrow Q) \rightarrow \neg(R \vee S)) \land ((Q \rightarrow P) \vee \neg R) \land R \Rightarrow (P \leftrightarrow Q) $

### 习题二 第7题
证明以下题目：

(1) $ (P \rightarrow Q) \Rightarrow ((P \land R) \rightarrow Q) $

(2) $ (P \rightarrow Q) \Rightarrow (P \rightarrow (Q \lor R)) $

(8) $ (P \land Q) \lor (P \rightarrow Q) \Rightarrow P \rightarrow Q $

(12) $ (P \lor Q \lor R) \Rightarrow \neg P \rightarrow ((Q \lor R) \land \neg P) $

(13) $ \neg(P \rightarrow Q) \land (Q \rightarrow P) \Rightarrow (P \land \neg Q) $

(14) $ (P \rightarrow Q) \rightarrow (Q \rightarrow R) \Rightarrow(R \rightarrow P) \rightarrow (Q \rightarrow P) $

(15) $ (P \rightarrow Q) \land (R \rightarrow Q) \land (S \rightarrow Q) \Rightarrow (P \land R \land \neg S \rightarrow Q) $


### 习题二 第8题
证明以下题目：

(1) $ (P \vee Q) \land (P \rightarrow S) \land (Q \rightarrow R) \Rightarrow S \vee R $

(2) $ (\neg P \vee Q) \land (\neg Q \vee R) \land (R \rightarrow S) \Rightarrow P \rightarrow S $

(3) $ (P \rightarrow (Q \rightarrow R)) \land (\neg S \vee P) \land Q \Rightarrow S \rightarrow R $

(4) $ (P \vee Q \rightarrow R \land S) \land (S \vee E \rightarrow U) \Rightarrow P \rightarrow U $

(5) $ (\neg R \vee S) \land (S \rightarrow Q) \land (\neg Q) \Rightarrow Q \leftrightarrow R $

(6) $ (\neg Q \vee S) \land ((E \rightarrow \neg U) \rightarrow \neg S) \Rightarrow Q \rightarrow E $

### 习题二 第9题
证明下列推理关系：

(1) 在大城市球赛中，如果北京队第三，那么如果上海队第二，那么天津队第四。沈阳队不是第一或北京队第三。上海队第二。从而知，如果沈阳队第一，那么天津队第四。

(2) 如果国家不对农产品给予补贴，那么国家就要对农产品进行控制。如果对农产品进行控制，农产品就不会短缺。或者农产品短缺或者农产品过剩。事实上农产品不过剩。从而国家对农产品给予了补贴。

### 习题二 第10题
如果合同是有效的，那么张三应受罚。如果张三应受罚，他将破产。如果银行给张三贷款，他就不会破产。事实上，合同有效并且银行给张三贷款了。验证这些前提是否有矛盾。

### 补充题

证明以下题目：

(1) $( R \to (P \vee Q) ) \wedge S \wedge (S \to T) \wedge (\neg T \vee R) \wedge (Q \to U) \wedge (\neg U) \Rightarrow P$

(2) $((T\to R)\to \neg(P\to R)) \land (Q \vee \neg T) \ \Rightarrow\ (\neg P \to Q)$

(3) $(\neg R \to (\neg S \vee Q)) \land S \land ((S \wedge P) \to R) \ \Rightarrow\ (P \vee \neg Q) \to R$

### 附加题：归结推理

归结推理的核心是利用互补对进行归结，即：$ C_1 \land C_2 \Rightarrow R(C_1, C_2)$。其lean4的一种证明如下：
```lean
theorem resolution_general (P Γ Δ : Prop)
  (h1 : ¬P ∨ Γ) (h2 : P ∨ Δ) : Γ ∨ Δ := by
  cases h1 with
  | inl h_not_p =>
    cases h2 with
    | inl h_p => exact (h_not_p h_p).elim
    | inr hΔ  => exact Or.inr hΔ
  | inr hΓ =>
    exact Or.inl hΓ
```

可以调用上述函数，利用归结法证明：
#### 2.10.2

(1) $ ( P \rightarrow Q) \land P \Rightarrow Q $

(2) $ ( ( P \rightarrow Q) \land ( Q \rightarrow R) ) \Rightarrow ( P \rightarrow R) $

#### 习题2 第12题
(1) $ ( P  \lor Q)  \land ( P  \rightarrow R)  \land ( Q \rightarrow R)  \Rightarrow R $

(2) $( S \rightarrow \lnot Q)  \land ( P  \rightarrow Q)  \land ( R \lor S ) \land ( R \rightarrow \lnot Q)  \Rightarrow \lnot P $

(3) $\lnot ( P  \land \lnot Q)  \land ( \lnot Q \lor R)  \land \lnot R \Rightarrow \lnot P$


#### 补充题目
(1) 在某博物馆，一颗珍贵的宝石被盗。警方根据线索和嫌疑人的证词，整理出以下事实：
  1. 保安或者游客偷了宝石。
  2. 如果保安偷了宝石，则盗窃未发生在闭馆前。
  3. 如果游客的证词是正确的，则盗窃发生在闭馆前。
  4. 如果游客的证词不正确，则闭馆时警报未响。
  5. 如果保安诚实，则他会主动报告异常情况。
  6. 宝石被盗时，保安未报告任何异常情况。
  7. 闭馆时警报响了

请根据以上事实，判断是谁偷了宝石，并证明。 

(2) 利用归结法证明：
$((P \to Q) \wedge (R \to Q) \wedge (S \to Q)) \Rightarrow (P \wedge \neg R \wedge \neg S \to Q)$

## 第三章

### 3.2.6定理
证明以下定理：

(1) $\vdash (Q\rightarrow R)\rightarrow((P\rightarrow Q)\rightarrow(P\rightarrow R)) $

(2) $\vdash P\rightarrow P $

(3) $\vdash \neg P\vee P $

(4) $\vdash P\vee\neg P $

(5) $\vdash P\rightarrow\neg\neg P $

(6) $\vdash \neg\neg  P\rightarrow P $

(7) $\vdash (P\rightarrow Q)\rightarrow(\neg Q\rightarrow\neg P) $

### 习题三 第1题
证明以下定理（可以使用上面3.2.6中的七条已证明定理，这七条定理使用时可以直接使用sorry占位，不必全部证明一遍）

(1)$\vdash \neg (P \wedge Q)\rightarrow (\neg P \vee \neg Q)$

(2)$\vdash (\neg P \vee \neg Q)\rightarrow \neg (P \wedge Q)$

(3)$\vdash P \rightarrow (Q\vee P)$

(4)$\vdash Q\rightarrow (P \rightarrow Q)$

### 补充题
由于罗素公理部分较难，这里提供补充题的参考答案。

1. 
* 题干
  * [依照罗素公理系统证明命题：$\vdash P \wedge Q \to Q$。可以使用课件上的定理3.2.1-3.2.7。]
* 题解
  * (1)$\vdash P\rightarrow(P\vee Q)$&emsp;&emsp;公理二
  * (2)$\vdash (P \vee Q)\rightarrow(Q\vee P)$&emsp;&emsp;公理三
  * (3)$\vdash(Q \rightarrow R)\rightarrow(( P\rightarrow Q)\rightarrow( P\rightarrow R))$&emsp;&emsp;课件定理3.2.1
  * (4)$\vdash((P\vee Q) \rightarrow (Q \vee P))\rightarrow(( P\rightarrow(P\vee Q))\rightarrow( P\rightarrow(Q\vee P)))$&emsp;&emsp;(3)代入$\frac{Q}{P\vee Q},\frac{R}{Q \vee P}$
  * (5)$\vdash( P\rightarrow(P\vee Q))\rightarrow( P\rightarrow(Q\vee P))$&emsp;&emsp;(2),(4)分离
  * (6)$\vdash P\rightarrow(Q\vee P)$&emsp;&emsp;(1),(5)分离
  * (7)$\vdash \neg P \vee P\rightarrow(\neg Q \vee \neg P \vee P)$&emsp;&emsp;(6)代入$\frac{P}{\neg P \vee P},\frac{Q}{\neg Q}$
  * (8)$\vdash \neg P \vee P$&emsp;&emsp;课件定理3.2.3
  * (9)$\vdash \neg Q \vee \neg P \vee P$&emsp;&emsp;(7),(8)分离
  * (10)$\vdash (\neg Q \vee \neg P \vee P)\rightarrow(P\vee \neg Q \vee \neg P)$&emsp;&emsp;(2)代入$\frac{P}{\neg Q \vee \neg P},\frac{Q}{P}$
  * (11)$\vdash P \vee \neg Q \vee \neg P $&emsp;&emsp;(9),(10)分离
  * (12)$\vdash(Q \rightarrow R)\rightarrow((P\vee Q)\rightarrow(P\vee R))$&emsp;&emsp;公理四
  * (13)$\vdash(\neg Q \vee \neg P \rightarrow \neg \neg (\neg Q \vee \neg P))\rightarrow((P\vee \neg Q \vee \neg P)\rightarrow(P\vee \neg \neg (\neg Q \vee \neg P)))$&emsp;&emsp;(12)代入$\frac{Q}{\neg Q \vee \neg P},\frac{R}{\neg \neg (\neg Q \vee \neg P)}$
  * (14)$\vdash P \rightarrow \neg \neg P$&emsp;&emsp;课件定理3.2.5
  * (15)$\vdash \neg Q \vee \neg P \rightarrow \neg \neg (\neg Q \vee \neg P)$&emsp;&emsp;(14)代入$\frac{P}{\neg Q \vee \neg P}$ 
  * (16)$\vdash(P\vee \neg Q \vee \neg P)\rightarrow(P\vee \neg \neg (\neg Q \vee \neg P))$&emsp;&emsp;(13),(15)分离
  * (17)$\vdash P\vee \neg \neg (\neg Q \vee \neg P)$&emsp;&emsp;(11),(16)分离
  * (18)$\vdash P\vee \neg \neg (\neg Q \vee \neg P) \to  \neg \neg (\neg Q \vee \neg P) \vee P$&emsp;&emsp;(2)代入$\frac{Q}{\neg \neg (\neg Q \vee \neg P)}$
  * (19)$\vdash \neg \neg (\neg Q \vee \neg P) \vee P$&emsp;&emsp;(17),(18)分离
  * (20)$\vdash \neg  (Q \wedge  P) \vee P$&emsp;&emsp;定义二
  * (21)$\vdash Q \wedge  P \to P$&emsp;&emsp;定义一
  * (22)$\vdash P \wedge  Q \to Q$&emsp;&emsp;$P，Q$相互代入


2. 
* 题干
  * 依托罗素公理系统证明：$ P \wedge Q \rightarrow P$
* 题解
  * (1)$ \vdash (P \rightarrow Q) \rightarrow (\neg Q \rightarrow \neg P) $ 定理7
  * (2)$\vdash  (P \rightarrow P \vee \neg Q) \rightarrow (\neg (P \vee \neg Q) \rightarrow \neg P)  代入 \frac{Q}{P \vee \neg Q}  $
  * (3)$\vdash P \rightarrow P \vee Q$ 公理2
  * (4)$\vdash P \rightarrow P \vee \neg Q $  (3)代入$ \frac{Q}{\neg Q}$
  * (5)$\vdash \neg (P \vee \neg Q ) \rightarrow \neg P$ (2)(4)分离
  * (6)$\vdash \neg (\neg P \vee \neg Q ) \rightarrow \neg \neg P$ (5)代入$\frac{P}{\neg P}$
  * (7)$\vdash (Q \rightarrow R) \rightarrow ((P \rightarrow Q)\rightarrow (P \rightarrow R)) $ 定理1
  * (8)$\vdash (\neg \neg P \rightarrow  P) \rightarrow ((\neg (\neg P \vee \neg Q ) \rightarrow \neg \neg P)\rightarrow ((\neg (\neg P \vee \neg Q )  \rightarrow P)))$ (7)代入 $\frac{Q}{\neg \neg P},\frac{R}{P}, \frac{P}{\neg (\neg P \vee \neg Q)}$
  * (9)$\vdash  (\neg \neg P \rightarrow  P)$ 定理6
  * (10)$ \vdash ((\neg (\neg P \vee \neg Q ) \rightarrow \neg \neg P)\rightarrow ((\neg (\neg P \vee \neg Q )  \rightarrow P)))$ (8)(9)分离
  * (11)$ \vdash (\neg (\neg P \vee \neg Q )  \rightarrow P)$ (6)(10)分离
  * (12)$ \vdash P\wedge Q \rightarrow P$  (11)定义2

3. 
* 题干
  * [利用罗素公理系统证明：$(p\to q)\vee \neg q$(可以使用书上定理1-7)]
* 题解
  * $1.(p\vee q)\to (q\vee p) 公理3\\
  2.(q\vee \neg p)\to (\neg p \vee q) 1代入\frac{p}{q},\frac{q}{\neg p}\\
  3.p\to (p\vee q)公理2\\
  4.q\to (q\vee \neg p)3代入\frac{p}{q},\frac{q}{\neg p}\\
  5.(q\to r)\to ((p\to q)\to (p\to r))定理1\\
  6.((q \vee \neg p)\to(p\to q))\to ((q\to (q \vee \neg p))\to(q\to  (p \to q))) 5代入\frac{p}{q},\frac{q}{q\vee \neg p},\frac{r}{p\to q}\\
  7.(q\vee \neg p )\to (p \to q) 2定义1\\
  8.(q\to (q \vee \neg p))\to(q\to  (p \to q))6,7分离\\
  9.q\to  (p \to q)4,8分离\\
  10.\neg q \vee (p \to q)9定义1\\
  11.(\neg q \vee (p \to q))\to ((p\to q)\vee \neg q)1代入\frac{p}{\neg q},\frac{q}{p\to q}\\
  12.(p\to q)\vee \neg q10，11分离$


4. 
* 题干
  * 利用罗素公理系统证明：$\vdash (P\wedge Q)\rightarrow (P\vee Q)$
* 题解
  * 证明:
    * $(1)\vdash P\rightarrow (P\vee Q) \qquad\qquad\qquad\qquad\qquad\qquad\qquad \ \ \       公理2 $
    * $(2)\vdash \neg P \vee (P\vee Q) \qquad\qquad\qquad\qquad\qquad\qquad\qquad \ \                (1)定义1 $
    * $(3)\vdash (P\vee Q)\rightarrow (Q\vee P) \quad\qquad\qquad\qquad\qquad\qquad\ \ \ \             公理3 $
    * $(4)\vdash (\neg P\vee (P\vee Q))\rightarrow ((P\vee Q)\vee \neg P) \qquad\qquad\quad\         (3)代入{P\over \neg P},{Q\over P\vee Q}$
    * $(5)\vdash (P\vee Q)\vee \neg P \qquad\qquad\qquad\qquad\qquad\qquad\qquad\ \,                 (2)(4)分离$
    * $(6)\vdash \neg P\rightarrow (\neg P\vee \neg Q) \qquad\qquad\qquad\qquad\qquad\qquad\ \,\     (1)代入{P\over \neg P},{Q\over \neg Q}$
    * $(7)\vdash (Q\rightarrow R)\rightarrow ((P\vee Q)\rightarrow (P\vee R))\qquad\quad\qquad\ \ \  公理4$
    * $(8)\vdash (\neg P\rightarrow (\neg P\vee \neg Q))\rightarrow (((P\vee Q)\vee \neg P)\rightarrow ((P\vee Q)\vee (\neg P\vee \neg Q))) \\
    \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad                        (7)代入{P\over P\vee Q},{Q\over \neg P},{R\over \neg P\vee \neg Q}$
    * $(9)\vdash ((P\vee Q)\vee \neg P)\rightarrow ((P\vee Q)\vee (\neg P\vee \neg Q))\qquad         (6)(8)分离 $
    * $(10)\vdash (P\vee Q)\vee (\neg P\vee \neg Q)\qquad\qquad\qquad\qquad\qquad\ \ \,              (5)(9)分离$
    * $(11)\vdash P\rightarrow \neg\neg P\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad\ \          定理5$
    * $(12)\vdash (P\rightarrow \neg \neg P)\rightarrow ((W\vee P)\rightarrow(W\vee \neg \neg P))\qquad (7)代入{P\over W},{Q\over P},{R\over \neg \neg P}$ 
    * $(13)\vdash (W\vee P)\rightarrow (W\vee \neg \neg P)\qquad\qquad\qquad\qquad\quad\ \ (11)(12)分离$
    * $(14)\vdash ((P\vee Q)\vee (\neg P\vee \neg Q))\rightarrow((P\vee Q)\vee \neg \neg(\neg P\vee \neg Q))\\
    \qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\qquad\quad              (13)代入{P\over \neg P\vee \neg Q},{W\over P\vee Q}$
    * $(15)(P\vee Q)\vee \neg \neg (\neg P\vee \neg Q) \qquad\qquad\qquad\qquad\qquad\ \ (10)(14)分离$
    * $(16)(P\vee Q)\vee \neg (P\wedge Q)\qquad\qquad\qquad\qquad\qquad\qquad\ \ (15)定义2$
    * $(17)((P\vee Q)\vee \neg (P\wedge Q))\rightarrow (\neg (P\wedge Q)\vee (P\vee Q))\ \ \,(3)代入{P\over P\vee Q},{Q\over \neg (P\wedge Q)}$
    * $(18)\neg (P\wedge Q)\vee (P\vee Q)\qquad\qquad\qquad\qquad\qquad\qquad\ \  (16)(17)分离$
    * $(19)(P\wedge Q)\rightarrow (P\vee Q)\qquad\qquad\qquad\qquad\qquad\qquad\ \ \ (18)定义1 $
