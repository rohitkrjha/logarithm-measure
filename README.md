# Optimal irrationality measures for logarithms of rational numbers and a compatible-embedding extension

Rohit Kumar Jha

[Zenodo record](https://zenodo.org/records/23241863) · [DOI: 10.5281/zenodo.23241863](https://doi.org/10.5281/zenodo.23241863)

[Read the paper](release/logarithm-measure-v1.pdf) · [Version v1](https://github.com/rohitkrjha/logarithm-measure/releases/tag/v1) · [LaTeX source](sources/main.tex) · [Lean project](sources/anc/lean)

## Result

For every positive rational number r different from 1,

$$
\mu(\log r)=2.
$$

In particular, the result includes log 3. For positive algebraic numbers
alpha different from 1,

$$
2\leq\mu(\log\alpha)\leq 2\deg_{\mathbb Q}(\alpha).
$$

The paper also proves a compatible-embedding bound

$$
2\leq\mu(x)\leq\frac{2d}{s}
$$

under its stated exponential identities at s embeddings of a degree-d
number field. It includes rational-power logarithms, rational arctangents,
and quadratic-normalized examples. Approximation thresholds are existential,
not numerically computed.

The manuscript gives the full statements, hypotheses, proofs, and references.

## Contents

- **release/** contains the manuscript PDF and the four companion files prepared for the matching Zenodo deposit.
- **sources/** is the exact unpacked contents of the source archive, including its original checksum inventories.
- **sources/anc/lean/** contains the formalization, pinned Lake manifest, verification scripts, and required upstream source files.
- **CITATION.cff** supplies citation metadata for the paper and its source repository.
- **scripts/check_integrity.py** checks the release files and their agreement with the unpacked sources.

The source archive is intentionally included alongside the browsable source tree so that the downloadable publication package can be checked against it.

## Reproduce

First check the distributed files from the repository root:

    python3 scripts/check_integrity.py

To compile the manuscript, install a TeX distribution and latexmk, then run:

    cd sources
    latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

To check the proof, install [elan](https://github.com/leanprover/elan), then run the following from the repository root. The checked-in lean-toolchain and lake-manifest.json select the required versions.

    cd sources/anc/lean
    lake exe cache get
    lake build LogarithmExtension.Verification
    lake env lean --run VerifyGeneralLog.lean

Run these commands sequentially. Downloads require network access. Do not rebuild imported modules while the kernel replay is running. Compiled Lean objects and dependency caches are not included.

The pinned versions and source provenance are documented in [the ancillary README](sources/anc/README.txt). The original package instructions are also available in [release/README.txt](release/README.txt).

## Verification

The v1 checks passed the Lean build, a transitive axiom audit of 1,326 extension theorems, and a fresh-environment Lean-kernel replay of 33 selected roots and their closure of 118,179 declarations. Only propext, Classical.choice, and Quot.sound were permitted. The replay roots cover the rational and algebraic logarithm statements, both compatible-embedding branches, the stated examples, and the real-input counterexamples.

These checks reused pinned dependency/build caches; they were not clean-machine installations or full Mathlib source rebuilds. The replay uses Lean's own kernel.

The GitHub Actions workflow checks publication-file integrity only. It does not replace the Lean commands above or claim a new proof replay on every commit.

## Citation and versions

Use the repository's **Cite this repository** control or [CITATION.cff](CITATION.cff). Version v1 identifies the manuscript and source package in this release. The matching preprint is archived on [Zenodo](https://zenodo.org/records/23241863) with version-specific DOI [10.5281/zenodo.23241863](https://doi.org/10.5281/zenodo.23241863).

Substantive changes to the manuscript or proof will receive a new release rather than changing the v1 tag. Later citation-only metadata updates may appear on the main branch without changing the v1 mathematical sources.

## Provenance and licenses

The construction extends the separated-weight interpolation-determinant method of OpenAI's irrationality-exponent proof for pi, cited in the manuscript.

The manuscript, LaTeX/bibliography sources, and accompanying documentation are licensed under **CC BY 4.0**. Original Lean code, verification scripts, and build configuration are licensed under **Apache 2.0**. Third-party code retains its existing licenses and notices. These licenses apply to different components, not as interchangeable alternatives for every file.

See [LICENSE](LICENSE), [the package rights notice](sources/RIGHTS.txt), and the upstream notices retained under sources/anc/lean. The bibliography credits the mathematical sources.
