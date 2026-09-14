# `Thomson/Numerics` — verified arithmetic for the kernel

**Reference.** Interval arithmetic: Moore (1966); Taylor models: Makino–Berz (2003); the
reflection pattern (a computable checker plus a soundness theorem, run by `decide +kernel`) is the
standard one in Lean/Coq formalisations.  Everything here is independent of the Thomson problem.

| file | content |
|---|---|
| `Interval.lean` | `Itv`: closed intervals with integer endpoints at scale `10⁻⁴⁰`, outward-rounded `add/mul/…`, `Mem` soundness |
| `TaylorModel.lean` | `TM`: quadratic Taylor models on the normalised box, `loBound`, `geBound_sound` |
| `Poly.lean` | polynomials as coefficient lists (`reval`, `rder`, `rmul`) |
| `Tensor.lean`, `TensorEngine.lean` | `9×9×9` coefficient tensors, the Taylor shift, `toTM` (the interpreter-oriented form) |
| `PolyList.lean` | nested lists for the kernel: Horner's Taylor shift, box normalisation, `Mem3` |
| `ListTaylorModel.lean` | the Taylor model read off a nested list, `toTML_mem` |

`scripts/kernel_build/README.md` records what the kernel can and
cannot reduce and the measured speeds.  Namespace `Thomson.Tri5b` (historical; unchanged so that
no proof had to be touched).
