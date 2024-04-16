Please do not merge this PR but keep it open: its purpose is to provide data on working ocaml-camlp5 pairs.

It contains some github action scripts to inventory the pairs ocaml-camlp5 for which hol-light works.

For each camlp5 version, there is a yml script testing the ocaml versions meaningful for this camlp5 version.

Remarks:
- we only test "hol.ml"
- we sometimes need to install the following packages: libipc-system-simple-perl, libstring-shellquote-perl
- github accepts up to 256 jobs maximum

Working pairs found (this may not be exhaustive):

| ocaml  | camlp5                                                                 |
|--------|------------------------------------------------------------------------|
| 4.02.3 | 6.14, 6.15, 6.16, 6.17, 7.01, 7.03, 7.05, 7.06.10-g84ce6cc4, 7.08, 7.1 |
| 4.03.0 | 6.15, 6.16, 6.17, 7.01, 7.03, 7.05, 7.06.10-g84ce6cc4, 7.08, 7.1       |
| 4.04.2 | 7.01, 7.03, 7.05, 7.06.10-g84ce6cc4, 7.08, 7.1                         |
| 4.05.0 | 7.01, 7.03, 7.05, 7.06.10-g84ce6cc4, 7.08, 7.1                         |
| 4.06.1 | 7.05, 7.06.10-g84ce6cc4, 7.08, 7.11, 7.12, 7.13, 7.14                  |
| 4.07.1 | 7.06.10-g84ce6cc4, 7.08, 7.11, 7.12, 7.13, 7.14                        |
| 4.08.1 | 7.09, 7.11, 7.12, 7.13, 7.14, 8.00.03, 8.00.04                         |
| 4.09.1 | 7.11, 7.12, 7.13, 7.14, 8.00.03, 8.00.04                               |
| 4.10.2 | 7.14, 8.00.03, 8.00.04, 8.00.05, 8.02.00, 8.02.01                      |
| 4.11.2 | 7.14, 8.00.03, 8.00.04, 8.00.05, 8.02.00, 8.02.01                      |
| 4.12.1 | 7.14, 8.00.03, 8.00.04, 8.00.05, 8.02.00, 8.02.01                      |
| 4.13.1 | 8.00.03, 8.00.04, 8.00.05, 8.02.00, 8.02.01                            |
| 4.14.1 | 8.00.03, 8.00.04, 8.00.05, 8.02.00, 8.02.01                            |
| 5.0.0  | 8.02.01                                                                |
| 5.1.1  | 8.02.01                                                                |

Detailed results can be found in:

| camlp5  | results                                                       |
|---------|---------------------------------------------------------------|
| 8.02.01 | https://github.com/fblanqui/hol-light/actions/runs/8710772959 |
| 8.02.00 | https://github.com/fblanqui/hol-light/actions/runs/6954163355 |
| 8.01.00 | https://github.com/fblanqui/hol-light/actions/runs/6954163352 |
| 8.00.05 | https://github.com/fblanqui/hol-light/actions/runs/4185147934 |
| 8.00.04 | https://github.com/fblanqui/hol-light/actions/runs/4127325386 |
| 8.00.03 | https://github.com/fblanqui/hol-light/actions/runs/4127325387 |
| 8.00.02 | https://github.com/fblanqui/hol-light/actions/runs/4127325397 |
| other   | https://github.com/fblanqui/hol-light/actions/runs/3929583606 |
