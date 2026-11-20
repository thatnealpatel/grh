# Alessandro Maria Masullo, *The Music of the Primes*

[Source PDF](https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf). This edition is 940 pages and 6,756,996 bytes. Its SHA-256 is `e039d3f6cf0a4b14f03c7edb85097752dd65c0a2fe543c76fe992be234f97bf5`. The URL names a location; the digest identifies the bytes read by the project.

The [source reader](../../../internal/source/pdf.go) fetches and verifies the PDF and caches it outside the checkout. For an offline copy, set `GRH_PDF` to its absolute path; the reader checks the same digest. If the URL is replaced, do not silently update the pin or carry the old passage reviews over to a different edition.

The [divisor heading](../../../.godel/obligations/divisor-heading.json) and [trace comparison](../../../.godel/obligations/trace-assembly.json) records cite the passages and identify the readers' evidence. For these passages the printed page numbers match the one-based PDF ordinals. To make a disposable search aid from a verified copy, run `pdftotext -layout "$GRH_PDF" /tmp/masullo-music-of-the-primes.txt`. Use the rendered pages, not the extraction, to check formulas, footnotes, and page boundaries.

This record identifies the edition; it is not a redistribution license or an offline archive of the paper.
