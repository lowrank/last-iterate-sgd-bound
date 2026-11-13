# Improved last-iterate bounds for SGD with and without replacement

Lean formalization of last-iterate population-loss bounds for stochastic gradient descent
under sampling with replacement (WR) and without replacement (WOR). The proof covers both
interpolation and nonzero gradient noise at the optimum, with an explicit universal constant.

The main statements are in [Challenge.lean](Challenge.lean), and their proofs are supplied by
[Solution.lean](Solution.lean). The full proof development is in [LastIterate/](LastIterate/).

## Mathematical result

Let $f_1,\ldots,f_n:\mathbb R^d\to\mathbb R$ be differentiable convex functions whose gradients
are $\beta$-Lipschitz, where $n\ge 1$ and $\beta>0$. Suppose the population objective

$$
F(x)=\frac1n\sum_{z=1}^n f_z(x)
$$

has a minimizer $x^*$. Starting from a deterministic $x_0$, run SGD with constant step size
$\eta>0$:

$$
x_{t+1}=x_t-\eta\nabla f_{z_t}(x_t).
$$

Write

$$
R^2=\lVert x_0-x^*\rVert^2,
\qquad
\sigma_*^2=\frac1n\sum_{z=1}^n\lVert\nabla f_z(x^*)\rVert^2,
\qquad
\delta=\min\{1,2-\eta\beta\}.
$$

For a positive integer horizon $T$, define

$$
\ell_T=\log(T+2),
\qquad
\lambda_T=\log(2+\ell_T),
\qquad
P_T=\frac{\ell_T^3}{\lambda_T}.
$$

For every $0<\eta\beta<2$, the formalization proves

$$
\mathbb E\bigl[F(x_T)-F(x^*)\bigr]
\le 280000\,P_T
\left(
\frac{R^2}{\delta^3\eta T}
+\frac{\eta\sigma_*^2}{\delta^4}
\right).
$$

The sampling laws and permitted horizons are:

| Sampling | Distribution of the update labels | Horizons |
| --- | --- | --- |
| WR | Independent uniform labels from the population | Every $T\ge 1$ |
| WOR | A uniform ordered sample of distinct labels, equivalently a prefix of a uniform permutation | Every $1\le T\le n$, including $T=n$ |

In the interpolation regime, $\sigma_*^2=0$. At the greedy step $\eta=1/\beta$, the bound becomes

$$
\mathbb E\bigl[F(x_T)-F(x^*)\bigr]
\le 280000\,\beta R^2\frac{P_T}{T}
=O\!\left(\frac{\beta R^2\log^3 T}{T\log\log T}\right).
$$

The constant is conservative and has not been optimized. Both sampling rules satisfy the
same upper bound; the theorem does not order their losses on individual problems.

## Formal statements and scope

The two public submission theorems are:

| Declaration in `Solution.lean` | Conclusion |
| --- | --- |
| `SGDLastIterate.noisy_wr_wor` | The full noisy loss bound for WR and one-pass WOR |
| `SGDLastIterate.interpolation_wr_wor` | The interpolation loss bound at $\eta=1/\beta$ |

Their assumptions explicitly require the actual gradients, convexity, Lipschitz continuity of
the gradients, and a minimizer of the population objective. Expectations are literal finite
averages over all words for WR and all injective words for WOR. The iteration starts at $x_0$
and performs exactly $T$ updates.

The final theorems derive all history comparisons, gradient estimates, and restart budgets
from these assumptions. The proof development also contains conditional intermediate lemmas;
their hypotheses are discharged before the final results in
[LastIterate/Main.lean](LastIterate/Main.lean).

The submission covers the population-loss conclusions. The separate population-gradient
bound, tuned-step results, and quadratic special cases from the manuscript are outside its
stated scope. WOR is restricted to one pass.

## Proof structure

1. **Smooth geometry and normalization.** Convexity and a Lipschitz gradient give the strong
   interpolation inequality. Centering each loss at the population minimizer separates a
   common-minimizer loss from its affine residual.
2. **Actual sampling histories.** Finite trajectories are lifted to a Hilbert space of
   histories. Coordinate permutations give the rotation and frozen-query identities. The
   residual fields have zero off-diagonal inner products under WR and nonpositive ones under WOR.
3. **History and gradient budgets.** The proof retains the loss sum while controlling radius,
   displacement, and gradient energy. Restricting permutations to the remaining positions
   constructs restarts whose starting iterate is invariant under those permutations.
4. **The log-log saving.** Gradient lag estimates and frozen-history comparisons control suffix
   averages at geometric scales. Choosing the integer scale ratio `ceil (ell M + 2)` gives the
   log-log denominator. Averaging the bounds over all restart times gives the queried-loss bound.
5. **Population risk.** WR uses an independent final query. WOR separates used and unused labels;
   deleting a used update is represented by an explicit permutation and controlled by the
   gradient estimate. The argument includes an empty unused-label set when $T=n$.

Useful entry points are:

| File | Role |
| --- | --- |
| [Challenge.lean](Challenge.lean) | Independent statement file importing only Mathlib |
| [Solution.lean](Solution.lean) | The same definitions and statements, with completed proofs |
| [LastIterate/Targets.lean](LastIterate/Targets.lean) | Original SGD problem and finite sampling risks |
| [LastIterate/FrozenSampling.lean](LastIterate/FrozenSampling.lean) | Frozen-history comparison from the sampling law |
| [LastIterate/LogFactor.lean](LastIterate/LogFactor.lean) | Geometric scale choice and logarithmic estimates |
| [LastIterate/GlobalQuery.lean](LastIterate/GlobalQuery.lean) | Restart averaging and queried-loss/gradient bounds |
| [LastIterate/DeletionSampling.lean](LastIterate/DeletionSampling.lean) | Deletion comparison and its exact sampling identity |
| [LastIterate/FiniteRisk.lean](LastIterate/FiniteRisk.lean) | Concrete WR/WOR population-risk bounds |
| [LastIterate/Main.lean](LastIterate/Main.lean) | Original step-size normalization and final theorems |

## Building

The project pins **Lean 4.35.0-rc2** in [lean-toolchain](lean-toolchain) and Mathlib revision
`065356127b1dc0016f66b7283ce0ce2c4055aa55`. Exact dependency revisions are recorded in
[lake-manifest.json](lake-manifest.json).

With Elan installed, run from the repository root:

```sh
export MATHLIB_NO_CACHE_ON_UPDATE=1
export LAKE_CACHE_DIR="${LAKE_CACHE_DIR:-$HOME/.cache/lean/lake}"
lake build
```

This builds the proof library, Challenge, and Solution. Missing dependencies are fetched at
their pinned revisions and compiled as needed. The environment variable disables Mathlib's
automatic precompiled-cache download; no `lake exe cache get` command is required.

Lake's local artifact cache is enabled in [lakefile.toml](lakefile.toml). Keeping
`LAKE_CACHE_DIR` at a persistent location lets compatible builds reuse locally available
artifacts. Generated files remain under `.lake/` and the selected cache directory.

## Comparator and verification

[comparator.json](comparator.json) selects both submission theorems and enables NanoDa replay.
On a Linux host where `bubblewrap` can create the required namespaces, run:

```sh
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator --config=comparator.json
```

The toolchain's `bin` directory is included so Comparator can find `nanoda_bin`.
Challenge and Solution are compiled separately. The two `sorry` occurrences in
`Challenge.lean` are deliberate statement placeholders; `Solution.lean` does not import that
file. All definitions in the Challenge have concrete bodies, and there are no proof holes
in the Solution or its proof development.

The verification performed during preparation established:

- A successful build on Lean 4.35.0-rc2.
- An axiom audit of **237 proved declarations**, using only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Comparator acceptance of both theorem statements and proof replay by Lean and NanoDa.

The local Comparator run used its documented unsandboxed mode because the preparation host
denied the user namespace required by `bubblewrap`. This establishes the reported local
comparison and replay, but does not constitute Palomar's sandboxed verification or registration.
No independent human peer review is claimed. The review and automation record is in
[formalization.yaml](formalization.yaml).

## Provenance and license

The mathematical source the manuscript *Improved last-iterate bounds for SGD
with and without replacement* [arxiv:2611.14811](https://arxiv.org/pdf/2611.14811v1) by **Yimin Zhong and Jiaxin Zhou**, specifically Theorem 2.1
and the loss conclusion of Corollary 2.2.

Yimin Zhong maintains the formalization. OpenAI Codex assisted with Lean implementation; the workflow is disclosed in
[formalization.yaml](formalization.yaml).

The repository uses the [Apache License 2.0](LICENSE). Dependencies retain their own licenses.
