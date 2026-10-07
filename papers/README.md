# Papers

| Result | PDF | Self-contained LaTeX | Certificate program |
|---|---|---|---|
| Full exponent **0.7580758318008816** | [PDF](square-difference-free-sets-of-exponent-0.7580758318.pdf) | [TeX](square-difference-free-sets-of-exponent-0.7580758318.tex) | [Python](square-difference-free-certificate.py) |
| Simpler companion, exponent **0.758001** | [PDF](a-simpler-construction-of-square-difference-free-sets-beyond-exponent-0.758.pdf) | [TeX](a-simpler-construction-of-square-difference-free-sets-beyond-exponent-0.758.tex) | [Python](sarkozy-simple-certificate.py) |

The Lean development at the repository root proves the full result. The
companion presents a simpler construction for human readers and is not a
separate Lean formalization.

Both papers list **Eric Naslund** as author, with contact
[naslund.math@gmail.com](mailto:naslund.math@gmail.com). An asterisk on his
name refers to his supplied opening note, placed before the abstract, disclosing
the AI models' role under his prompting and supervision and explaining his
intended way of reading the paper with AI. That paragraph is reproduced from the
author's instructions, with typographic quotation marks; in the October revision
of the full paper its first sentence also names Claude Opus 5.5, which revised
the paper.

Each TeX file includes its bibliography and exact certificate program.
Compiling it writes the program and attaches it to the PDF. No external
bibliography, figure, research notes or certificate data are needed.

With standard TeX Live packages installed, copy one TeX file into a fresh
build directory and run the following command three times, substituting the
companion filename when appropriate:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape square-difference-free-sets-of-exponent-0.7580758318.tex
```

Run either certificate program using Python 3 and its standard library:

```bash
python3 square-difference-free-certificate.py
python3 sarkozy-simple-certificate.py
```

The programs are also attached to the PDFs.

**October 2026 revision.** The full paper now proves the exponent
`0.7580758318008816` and replaces the September paper for `0.75806746`, which
remains in the repository history (for example at commit
`e5d693729e23762b063a55015ad79ccaf28a3217`, the source of Palomar entry
PALOMAR-2026-09-19-000006, version 1). The new paper uses the same method with
new finite witnesses, is reorganized for readers (an introduction tracing the
method from Ruzsa and Krachun, a dependency graph of all numbered statements,
and a table showing where the gain over Krachun's exponent comes from), and
embeds a new certificate program for the new witnesses. Its build and checks
are recorded in [the October revision report](verification/revision-20261006.json).
A front-matter revision on October 7 shortens the exponent in the title to
0.7580758 (the abstract and text keep 0.7580758318008816) and moves the AI-use
statement, in the author's revised wording, into a shaded box between the
abstract and the table of contents, which now starts on page 2, with the
copyright and licence line at the foot of page 1; the companion's citation of
the title follows. Current hashes and checks are in
[revision-20261007.json](verification/revision-20261007.json).
The companion paper's mathematics and certificate program are unchanged; its
references to the full paper now give the new exponent and witness sizes.

The preserved
[full-result report](verification/full-result.json) and
[companion report](verification/simple-result.json) record the prior isolated
build and finite-verification checks. They describe the original September 11
paper versions. The September 18 front-matter revision adds the contact, author
note, and explicit licence and rebuilds both PDFs; its build checks, attachment
comparisons, and hashes for that revision are recorded in
[the publication revision report](verification/publication-20260918.json).
A subsequent revision uses the author's revised opening note, renames the TeX
and PDF files to follow the paper titles, and adds a brief discussion and
citations of Naslund's function-field conjecture and Jones's Palomar
counterexamples. Its current filenames, hashes, and PDF checks are recorded in
[the manuscript revision report](verification/revision-20260918.json).
The proofs and both certificate programs remain unchanged.
Historical paths in the earlier reports refer to the original research
workspace or earlier filenames; [PUBLICATION.md](../PUBLICATION.md) records
the copy and subsequent revisions.

Both papers, their LaTeX sources and PDFs, and their certificate programs are
licensed under the repository's [Apache License, Version 2.0](../LICENSE),
by Eric Naslund. Use, modification, and redistribution, including commercial
use, are permitted under its terms. See [NOTICE](../NOTICE) for attribution.
