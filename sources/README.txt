Optimal irrationality measures for logarithms of rational numbers and a compatible-embedding extension
====================================================

Author: Rohit Kumar Jha
Version: v1.1

FILES

  logarithm-measure-v1.1.pdf
      The research manuscript.

  logarithm-measure-v1.1-sources.zip
      LaTeX manuscript sources and the supporting Lean source project.
      Extract into an empty directory. The manuscript is main.tex; the
      formalization is in anc/lean. See anc/README.txt for source provenance,
      dependency revisions, and the verification procedure.

  README.txt
      This file: contents, reproduction commands, and integrity checks.

  RIGHTS.txt
      Licensing scope for the manuscript, new code, and third-party code.
      An identical copy is included in the source archive.

  SHA256SUMS.txt
      SHA-256 digests of the other four deposited files. The checksum file
      does not list itself.

REBUILD THE MANUSCRIPT

From the extracted source directory, with a TeX distribution and latexmk:

  latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex

The bibliography source and generated main.bbl are both included.

CHECK THE FORMALIZATION

Install the Lean toolchain specified in anc/lean/lean-toolchain using elan.
From the extracted source directory:

  cd anc/lean
  lake exe cache get
  lake build LogarithmExtension.Verification
  lake env lean --run VerifyGeneralLog.lean

Run these commands sequentially. Toolchain and dependency downloads require
network access. Compiled Lean objects and dependency caches are not included.
Do not rebuild imported modules while the final replay is running.

The verification target audits 1,326 extension theorems. The replay rechecks
33 selected roots and their closure of 118,179 declarations using Lean's own
kernel, allowing only propext, Classical.choice, and Quot.sound.

CHECK FILE INTEGRITY

From the directory containing the five deposited files, on macOS:

  shasum -a 256 -c SHA256SUMS.txt

On Linux, the corresponding command is:

  sha256sum -c SHA256SUMS.txt

The source archive also includes SHA256SUMS.txt for its other members and
anc/SHA256SUMS for the ancillary source files. After extraction, the same
checksum command can be used at the archive root; for the ancillary
inventory, run it from anc with SHA256SUMS instead of SHA256SUMS.txt.

PROVENANCE AND RIGHTS

The construction extends the separated-weight interpolation-determinant
method of OpenAI's irrationality-exponent proof for pi, cited in the
manuscript. Bundled upstream files and their license
notices are retained. The source archive includes the formalization,
supporting local mathematical sources, build configuration, verification
scripts, and licenses.

See RIGHTS.txt for the applicable licensing scope.

REVISION HISTORY

This citation-only revision adds the independently and contemporaneously
obtained rational-logarithm theorem of Liu, Jiang, and Zhang
(arXiv:2610.10192v1) to the introduction and bibliography and distinguishes
the compatible-embedding results. The theorem statements, mathematical
proofs, Lean sources, dependency pins, and verifier scripts are unchanged
from v1.

The Lean verification counts above refer to the unchanged v1 proof sources.
No new Lean proof replay is claimed for this bibliographic correction.
