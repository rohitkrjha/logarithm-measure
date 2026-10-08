FORMALIZATION OF IRRATIONALITY MEASURES FOR LOGARITHMS
====================================================

The project contains the logarithm extension and its local import closure,
together with verification scripts, configuration, and upstream licenses.
Mathematical source files are unchanged from the development project.
The Lake configuration selects the logarithm verification target.

MAIN RESULTS

  μ(log r) = 2                  (r > 0 rational, r ≠ 1)
  2 ≤ μ(log α) ≤ 2 deg_Q(α)     (α > 0 algebraic, α ≠ 1)

The compatible-embedding theorem and its hypotheses are stated in the paper.
The approximation thresholds are existential, not numerical computations.

PINNED VERSIONS

Lean: 4.34.1
Lean commit: 5045d0056413266e57c625dcd7c365b10e377c52
Mathlib: d13f23b723b8a846827a245b89c10fc7d3f11612
OpenAI mathematics: adc7f1241b42e322a6451854ab7e4b4c146bf78a
Upstream: https://github.com/openai/math

The upstream sources and Apache-2.0 license notices are retained.
The shared upstream compatibility patch is retained for provenance; it
does not add a theorem assumption to the logarithm result.

REPRODUCTION

Install the specified Lean toolchain using elan. From anc/lean, run:

  lake exe cache get
  lake build LogarithmExtension.Verification
  lake env lean --run VerifyGeneralLog.lean

Run sequentially. Do not rebuild imported modules during replay.
Retrieval of the toolchain and pinned dependencies requires network access.
Compiled objects and dependency caches are not distributed in this archive.

The audit checks 1,326 extension theorem declarations. The replay checks
33 selected roots and their closure of 118,179 declarations using Lean's
own kernel, permitting only propext, Classical.choice, and Quot.sound.
The roots include the rational and algebraic logarithms, both branches of
the compatible-embedding theorem, the stated examples, and counterexamples
for unrestricted real inputs. Earlier dedicated replay scripts are included.

The manuscript credits the upstream interpolation-determinant construction
and identifies the extension's contributions. Source integrity can be
checked with the ancillary SHA256SUMS inventory.
