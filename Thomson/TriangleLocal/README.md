# `Thomson/TriangleLocal` — the triangle inequality near the touching types

**Reference.** Ours: `docs/history/T5a-TriLocal.md` and blueprint §12.5, Task 5a.  At each of
the five touching types the triangle polynomial vanishes to second order; a fourth-order
one-sided Taylor bound along rays (`Calculus/`) reduces positivity on the cube of radius `1/500`
to a bracket `Q/2 + K/6 − M‖δ‖⁴/24 ≥ 0`, which is checked on the six faces of the cube by a
quadtree of patches in interval arithmetic (`Patch.lean`, `Types/Face*.lean`).

| file | content |
|---|---|
| `Calculus/` | the ray derivatives of `triP`, Fréchet coefficients, polarisation, the assembly `triP_local_of_bracket_all` |
| `Patch.lean`, `Jet.lean`, `Ray.lean`, `Enclose.lean`, `Compute.lean`, `Polar.lean`, `Touch.lean` | the interval side: the bracket on a patch, jets and majorants of the ray polynomial, the data of one type |
| `CFData.lean` | GENERATED: the tensor of `F` for the true certificate, kernel-checked against its definition |
| `Types/Type0–4.lean`, `Types/Face*.lean` | GENERATED (`scripts/threepoint/trilocal_gen.py`): the shifted tensors, the data, and the 30 face coverings, `decide +kernel` |
| `Glue.lean`, `Final.lean` | the five types assembled: `triP_local_cert` |

The type-3 faces need up to 13 GB each: build with `scripts/kernel_build/build_all.sh`.
Namespace `Thomson.TriLocalCert` (historical).
