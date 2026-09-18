# Papers

| Result | PDF | Self-contained LaTeX | Certificate program |
|---|---|---|---|
| Full exponent **0.75806746** | [PDF](square-difference-free.pdf) | [TeX](square-difference-free.tex) | [Python](square-difference-free-certificate.py) |
| Simpler companion, exponent **0.758001** | [PDF](sarkozy_simple_0.758.pdf) | [TeX](sarkozy_simple_0.758.tex) | [Python](sarkozy-simple-certificate.py) |

The Lean development at the repository root proves the full result. The
companion presents a simpler construction for human readers and is not a
separate Lean formalization.

Both papers list **Eric Naslund** as author, with contact
[naslund.math@gmail.com](mailto:naslund.math@gmail.com). An asterisk on his
name refers to his supplied opening note, placed before the abstract, disclosing
GPT-6-Astra's role under his prompting and supervision and explaining his
intended way of reading the paper with AI. That paragraph is reproduced verbatim
from the author's instructions, with typographic quotation marks and emphasis.

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
build and finite-verification checks. They describe the original September 11
paper versions. The September 18 front-matter revision adds the contact, author
note, and explicit licence and rebuilds both PDFs; its build checks, attachment
comparisons, and current hashes are recorded in
[the publication revision report](verification/publication-20260918.json).
The mathematical text and both certificate programs remain unchanged.
Historical paths in the earlier reports refer to the original research
workspace; [PUBLICATION.md](../PUBLICATION.md) records the copy.

Both papers, their LaTeX sources and PDFs, and their certificate programs are
licensed under the repository's [Apache License, Version 2.0](../LICENSE),
by Eric Naslund. Use, modification, and redistribution, including commercial
use, are permitted under its terms. See [NOTICE](../NOTICE) for attribution.
