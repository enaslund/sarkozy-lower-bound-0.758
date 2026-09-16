# Papers

| Result | PDF | Self-contained LaTeX | Certificate program |
|---|---|---|---|
| Full exponent **0.75806746** | [PDF](square-difference-free.pdf) | [TeX](square-difference-free.tex) | [Python](square-difference-free-certificate.py) |
| Simpler companion, exponent **0.758001** | [PDF](sarkozy_simple_0.758.pdf) | [TeX](sarkozy_simple_0.758.tex) | [Python](sarkozy-simple-certificate.py) |

The Lean development at the repository root proves the full result. The
companion presents a simpler construction for human readers and is not a
separate Lean formalization.

Each TeX file includes its bibliography and exact certificate program.
Compiling it writes the program and attaches it to the PDF. No external
bibliography, figure, research notes or certificate data are needed.

With standard TeX Live packages installed, copy one TeX file into a fresh
build directory and run the following command three times, substituting the
companion filename when appropriate:

```bash
pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape square-difference-free.tex
```

Run either certificate program using Python 3 and its standard library:

```bash
python3 square-difference-free-certificate.py
python3 sarkozy-simple-certificate.py
```

The programs are also attached to the PDFs. The preserved
[full-result report](verification/full-result.json) and
[companion report](verification/simple-result.json) record the prior isolated
build and finite-verification checks. All four deliverables and both programs
match those SHA256 hashes. Historical paths in those reports refer to the
original research workspace; [PUBLICATION.md](../PUBLICATION.md) records the copy.

The papers are reproduced unchanged from the working repository. The
Apache-2.0 license at the repository root covers the Lean formalization;
this export does not assign a new license to these paper copies.
