# Equivalence of Poisson‑Process Definitions in Lean 4

## 1  Introduction

This document explains **step‑by‑step** how the Lean 4 development contained in `PoissonProcess.lean` proves (half of) the equivalence between two common definitions of a *Poisson process*.

* **Definition 1** (`IsPoissonProcess1`) Definition 2.1.1 in Sheldon

    1. $N(0)=0$
    2. Indepedent increment
    3. Number of events in any interval of length $t$ follows $\rm{Poi}(\lambda t)$
* **Definition 2** (`IsPoissonProcess2`) Definition 2.1.2 in Sheldon
    
    1. $N(0)=0$
    2. independent **and** *stationary* increments,
    3. a *small‑time jump formula* $\mathbb P[N_h = 1] = \lambda h + o(h)$, and
    4. a *small‑time no‑large‑jump formula* $\mathbb P[N_h \ge 2] = o(h)$.

The Lean file proves

$$
\texttt{IsPoissonProcess1}\; \longrightarrow \;\texttt{IsPoissonProcess2},
$$

leaving the reverse implication as `sorry` (to be filled in later).

The exposition below mirrors the file’s internal section numbering.

> **Notation.**  Throughout, `Ω` is a type equipped with a `MeasurableSpace`, `μ : ProbabilityMeasure Ω` is the background probability measure, and the counting process is a function `u : ℝ≥0 → Ω → ℕ`.

---

## 2  Preliminaries

### 2.1  Counting processes

```lean
@[class] structure IsCountingProcess (u : ℝ≥0 → Ω → ℕ) : Prop
```

A counting process is assumed to be measurable, non‑negative, integer‑valued and monotone in `t`.

### 2.2  Increment properties

* **Independent increments**—`HasIndpendentIncrements`—are packaged using `iIndepFun` from `Mathlib.Probability`.
* **Stationary increments**—`HasStationaryIncrements`—state translation invariance of increment distributions.

### 2.3  Two Poisson‑process definitions

```lean
structure IsPoissonProcess1 … (r : ℝ≥0) : Prop
structure IsPoissonProcess2 … (r : ℝ≥0) : Prop
```

Definition 1 uses `poissonPMFReal` for part iii; Definition 2 use landau notation for part iii and iv.

---

## 3  From Definition 1 to Definition 2

The Lean file splits the proof into **three thematic blocks**.

### 3.1  Independent ⇒ Stationary increments  (Section 1.1)

Lemma `poisson_process1_has_stationary_increments` shows that the explicit Poisson formula in Definition 1 already implies the increments are stationary.

*Takeaway:* In the homogeneous Poisson law the parameter depends **only** on `t₂ − t₁`; therefore translating both endpoints by ` s ` leaves the law unchanged.

### 3.2  Small‑time probabilities (Section 1.2)

Before tackling the $o(h)$ statements we compute *closed forms* for $\mathbb P[N_h = k]$ with $k = 0,1,\ge 2$.

| Lemma       | Lean identifier                  | Formula                                  |
| ----------- | -------------------------------- | ---------------------------------------- |
| Zero jumps  | `poisson_process1_zero_jump`     | $\mathbb P[N_h=0]=e^{-rh}$               |
| Single jump | `poisson_process1_single_jump`   | $\mathbb P[N_h=1]=e^{-rh}(rh)$           |
| Many jumps  | `poisson_process1_multiple_jump` | $\mathbb P[N_h≥2]=1-e^{-rh}-e^{-rh}(rh)$ |

The last lemma uses a *partition of unity* of `Ω` into the three events and a bespoke measurability/disjointness helper `probability_measure_union`.

### 3.3  Building the $o(h)$ error terms (Section 1.3)

#### 3.3.1  The one‑jump error `f2iii`

We define

$$
 f_{2,\text{iii}}(h) \;:=\; e^{-rh}(rh) - rh.
$$

Using `Real.exp_sub_sum_range_succ_isLittleO_pow` from `Mathlib.Analysis`, the lemma

```lean
theorem f2iii_is_little_O : …
```

proves `f2iii =o[𝓝[>] 0] id`.

With this in hand, `poisson_process1_implies_process2iii` matches Definition 2.iii:

$$
 \mathbb P[N_h = 1] = rh + f_{2,\text{iii}}(h).
$$

#### 3.3.2  The large‑jump error `f_zero`

A similar construction,

$$
 f_0(h) := e^{-rh} - (1 - rh),
$$

leads to `f_zero_is_little_O` and, after a small algebraic rearrangement, `poisson_process1_implies_process2iv` realises Definition 2.iv.

### 3.4  Assembling the puzzle

Finally, `poisson_process_equiv` puts the pieces together:

* Part (i) is inherited verbatim (`u 0 = 0`).
* Part (ii) merges independent increments (from Definition 1) with the new stationary‑increment lemma (Section 3.1).
* Parts (iii) and (iv) are the \$o(h)\$ statements proved in Section 3.3.

The forward implication is thus **completely mechanised**. The reverse implication remains as a future exercise (marked `sorry`).

---

## 4  Future work

<!-- To close the equivalence we must show `IsPoissonProcess2 → IsPoissonProcess1`. The classical route goes via the Laplace transform or the Lévy–Khintchine formula; in Lean this will require

* building a uniqueness theorem for the *Kolmogorov forward equation* satisfied by the moment generating function, or
* using the *characteristic function* of increments together with the Carathéodory extension theorem.

Contributions welcome! -->

---

## 5  File synopsis

```
PoissonProcess.lean
├ 0. Counting‑process preliminaries
├ 1. Definition 1 ⇒ Definition 2
│  ├ 1.1 Stationary increments
│  ├ 1.2 Small‑time probabilities (0/1/≥2 jumps)
│  └ 1.3 Construction of little‑o error terms
├ 2. (todo) Definition 2 ⇒ Definition 1
└ 3. IsPoissonProcess (combined structure)
```

---

## 6  How to navigate the code

*Search tips*

* `#find IsPoissonProcess1` shows the definition.
* `#print poisson_process1_single_jump` displays a proof’s statement.

*Suggested reading order*

1. Skim the structures at the top of the file.
2. Read Lemma `poisson_process1_multiple_jump`—it showcases Lean’s measure theory tactics.
3. Follow the dependencies of `poisson_process_equiv`.

---

## 7  Acknowledgements

The proof relies on `Mathlib`’s extensive probability library and on the work of many contributors who formalised measure theory, asymptotics and the exponential function. Special thanks to the `Mathlib` maintainers for prompt reviews.

---

*Last compiled:* **16 May 2025** (Europe/London).
