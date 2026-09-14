# `Thomson/Uniqueness` — the minimiser is unique

**Reference.** Ours: `docs/uniqueness.md` (steps U1–U7).  At a configuration of minimal energy
every pair and triangle slack of the three-point bound vanishes (U1–U2, `Tight.lean`), so every
distance is one of the four chords (U3, `PairZero.lean`, strict sweeps) and every triangle one of
the five types (U4, `Chords.lean`); the resulting edge colouring of `K₈` is classified by a
kernel search (U5, `Graph.lean`), the Gram matrix is that of the antiprism (U6, `Gram.lean`), and
equal Gram matrices give an isometry (U6, `Congruent.lean`, classical).  `Main.lean`, `Final.lean`
assemble `thomson_eight_unique_of_tasks`; `Thomson.Complete` discharges the hypotheses.

Namespace `Thomson.Unique` (historical).
