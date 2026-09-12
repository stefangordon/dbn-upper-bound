# Finite barrier certificate

The certificate defines two piecewise-affine barriers, the supporting density
wall, and the 26 source boxes. Every rational is an exact canonical string.

- [data/barriers.json](data/barriers.json): 4817 main rows, 7849 reference rows,
  1620 wall segments, and 26 source boxes.
- [check.py](check.py): exact row, chain, domain, source-containment, and speed
  predicates corresponding to the Lean specification.
- [profiles.py](profiles.py): complete P8 profile inequalities with two enclosing
  arithmetic libraries.
- [check_support.py](check_support.py): exact identity between this certificate,
  the source evaluator's boxes, and the density evaluator's wall.

From this directory:

~~~sh
python verify.py
python verify.py --with-flint --with-mpmath
~~~

The first command needs only Python's standard library. The second also uses the
pinned packages in the root requirements file. Neither modifies certificate data
or stored reference outputs; an optional `--output NEW.json` writes a report.

## Schema

A segment has fields `tl,tr,qL,qR`. Its value is
`qL + (qR-qL)*(t-tl)/(tr-tl)`.
Each reference row includes one field certificate, with the exact probe,
density floor, optional signed jet ceiling, time cell, and density-wall lookup.
Each main row contains either a source-box index or a reference-field index.

The source certificates use `id,L,hlo,hhi,btl,btr`. A box includes its boundary.
A field record uses `signed,p,s,c,qM,mIdx,otl,otr,oIdx`, matching the Lean
`FieldCert` structure. The unsigned ceiling is zero because it is unused.

The supporting file [old-M3a-wall.json](data/old-M3a-wall.json) retains the
density wall's additional initial/bottom certificate data. Its 1620 affine
segments are proved identical to the normalized wall by `check_support.py`.
The filename is retained to keep that input's original hash; it is a
mathematical supporting certificate, not an earlier upper-bound premise.

## Meaning of a pass

Exact acceptance proves the finite conditions needed by the barrier theorem.
The P8 calculation proves inequalities for the explicit functions `U` and
`UY/U`; the density and jet comparisons connect them to `H_t` on paper.

No stored producer decision or optimizer flag supplies a hypothesis.
A pass here alone does not establish P2, P3, P4, P5, or P7. Their proofs and
computations are described in [the dependency map](../DEPENDENCIES.md).
Use the root `verify.py --regenerate` to replay all supporting calculations.

The Lean data generator reads `barriers.json` and resolves its source/field
references. Its `--check` mode compares all generated source files byte for
byte. The Lean checker independently verifies the resulting mathematical
predicates by kernel reduction.
