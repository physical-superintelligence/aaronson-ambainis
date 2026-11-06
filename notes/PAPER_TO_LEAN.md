# Paper to Lean

This note maps the numbered statements of the paper
(`paper/aaronson_ambainis_paper.pdf`) to the declarations of the Lean library
`AaronsonAmbainis`.

All names live in the namespace `AaronsonAmbainis`; a prefix such as `Bridge.`, `DetBij.`,
`DetLow.`, `Row.`, `Pack.`, `Dual.`, `Level.` or `Average.` is a sub-namespace. File paths are
relative to the directory `AaronsonAmbainis/`. A Lean *statement* is a definition of type
`Prop`; the Lean *proof* is the theorem of that type.

## Conventions

| Paper | Lean | Where |
|---|---|---|
| the cube `Q_n = {-1,1}^n`, and `{0,1}^n` in Corollary 1.2 | `Cube ι = ι → Bool` for a finite index type `ι`, with `false ↦ 0 ↦ +1` and `true ↦ 1 ↦ -1` | `Defs.lean` |
| `x^S` (flip the coordinates in `S`) | `flipSet x S` | `Defs.lean` |
| the antipode `x̄` | `antipode x` | `Defs.lean` |
| the difference set `Δ(x,y)` | `diffSet x y` | `Defs.lean` |
| `b_j(g)` | `bdry g j` | `Defs.lean` |
| `Z(g)` | `zone g` | `Defs.lean` |
| a 1-wing of `g` at `u` (Definition 2.2) | `IsWing g u A` | `Defs.lean` |
| a row of a Boolean function `g` at `x` (Definition 2.3, in the form with sensitive blocks that follows it) | `IsRow g x lam` | `Defs.lean` |
| a row of a real function `f` at every point, of cost at most `K` (Definition 2.3) | a family `a : Cube ι → ι → ℝ` with `0 ≤ a x j`, with `∑ j, a x j ≤ K`, and with `∑ j ∈ diffSet x y, a x j` at least the absolute value of `f x - f y` for all `x` and `y`; the three conditions are written out in each proposition | `Statements.lean`, `RowDefs.lean` |
| `I_j(g)` for Boolean `g` | `infl g j` | `Defs.lean` |
| `E[f]`, `Var(f)`, `Inf_j(f)` | `mean f`, `variance f`, `inflR f j` | `Defs.lean` |
| the mean absolute increment `L_j(f)`, and `L(f)` | `meanAbsIncr f j`, and the sum `∑ k, meanAbsIncr f k` | `Defs.lean` |
| the character `χ_S` | `chi S` | `Defs.lean` |
| `f` has degree at most `d` | `HasDegreeLE f d` | `Defs.lean` |
| the level function `g_t` and its rows `λ^{t,x}` | `Level.lev f t`, `Level.levRow f a t x` | `Level/Rows.lean` |
| the average `Av_j f` over one coordinate | `Average.avg j f` | `Average/Coordinate.lean` |

Five points of the formal language matter when the statements are read.

* In Lean `0⁻¹ = 0` and `x / 0 = 0`. For the inequalities in which the paper inverts a sum, the
  positivity of that sum is proved separately, so that these inequalities do not hold merely
  by this convention: in `Bridge/Positivity.lean` for Theorem 4.3, Proposition 5.2 and
  Theorem 5.4, and in `Level/AllPairs.lean` (`Level.pairSum_pos`) for Proposition 7.4.
* `HasDegreeLE` is defined through the expansion in the characters `chi S`. That this is the
  usual notion of degree (Fourier expansion, polynomials in `0/1` or in `±1` variables of bounded
  total degree) is proved in `Bridge/Fourier.lean`, `Bridge/ZeroOne.lean` and `Bridge/Poly.lean`.
* The two forms of a row of a real function, with `y` and `Δ(x,y)` in the propositions and with
  `S` and `x^S` in Definition 2.3, are compared in `Bridge.rows_iff_printed`
  (`Bridge/PaperTheorems.lean`).
* Outside `Conjecture.lean`, `Bridge.rpow_five_halves` and `Bridge.conj6_instance_conclusion`,
  the powers `3/2` and `5/2` of the paper are written with `Real.sqrt`: `ε^{5/2}` is `ε ^ 2 * Real.sqrt ε`.
  `Conjecture.lean` writes `ε^{5/2}` as the real power `ε ^ ((5 : ℝ) / 2)`, and
  `Bridge.rpow_five_halves` gives `ε ^ ((5 : ℝ) / 2) = ε ^ 2 * Real.sqrt ε`. The propositions of
  the chain avoid the powers `3/2` and `5/2` and state the inequalities without square roots;
  see "Where the Lean proof takes another route".
* Several lemmas take an earlier link of the chain as an explicit hypothesis, written as a first
  argument of type `Prop`: for example `Level.separated_sets (hTM : ThirdMomentInequality) …` and
  `Row.sum_abs_sub_unit_le (hM : MarkovEndpoint) …`. Each such hypothesis is a theorem of the
  library (`thirdMomentInequality`, `markovEndpoint`, `blockInequality`, `antipodalInequality`,
  `allPairsInequality`, `meanIncrementBound`, `influenceBound`, `DetLow.lowestUnit`,
  `DetLow.lowestBound`), and the statement of the paper is the lemma applied to it; the library
  has no separate declaration for the applied form. This concerns `DetBij.exists_lowest_Qmat`,
  `allPairs_core`, `Row.sum_abs_sub_unit_le`, `Pack.scaled_bound`, `Level.level_allPairs`,
  `Level.thirdMoment_lower`, `Level.separated_sets`, `Level.exists_abs_cube_le`,
  `Level.variance_cube_le`, `Level.exists_meanAbsIncr_ge_sqrt`, `Average.sum_meanAbsIncr_pos`,
  `Average.exists_inflR_ge_sqrt`, `Average.influence_cost`, `Average.influence_of_incr` and
  `Row.disjoint_blocks_of_block`.

## Section 1: the main results

| Paper | Lean statement | Lean proof | Where |
|---|---|---|---|
| Theorem 1.1 (main theorem) | `MainTheorem` | `mainTheorem` (through `mainTheorem_of_influence`) | `Statements.lean`, `Chain.lean`, `MainTheorem.lean` |
| Theorem 1.1, as printed (`n ≥ 1`, `d ≥ 1`, the power `5/2`) | `Bridge.MainTheoremPrinted` | `mainTheorem` with `Bridge.mainTheorem_iff_printed` | `Bridge/PaperTheorems.lean`, `Chain.lean` |
| Theorem 1.1, stated with Mathlib only | `ExplicitBoundPM` | `aaronson_ambainis_pm` | `Conjecture.lean`, `Main.lean` |
| Corollary 1.2, bound `(8√15 / (125 π^4)) · ε^{5/2} / d^6` | `ExplicitBound` | `aaronson_ambainis_explicit` | `Conjecture.lean`, `Main.lean` |
| Corollary 1.2, bound `(ε/d)^7` (the conjecture) | `PrintedConjecture` | `aaronson_ambainis` | `Conjecture.lean`, `Main.lean` |
| Theorem 1.3 (mean absolute increments; it is Theorem 7.10) | `Bridge.MeanIncrementPrinted` | `meanIncrementBound` with `Bridge.meanIncrement_iff_printed` | `Bridge/PaperTheorems.lean`, `Chain.lean` |
| Theorem 1.4 (influences; it is Theorem 8.3) | `Bridge.InfluencePrinted` | `influenceBound` with `Bridge.influence_iff_printed` | `Bridge/PaperTheorems.lean`, `Chain.lean` |
| Theorem 1.5 (two-sided inequality) | `Bridge.TwoSidedPrinted` | `twoSidedInequality` with `Bridge.twoSided_iff_printed` | `Bridge/PaperInequalities.lean`, `Chain.lean` |

`MainTheorem` is the inequality `3 Var(f)^5 ≤ 50000 π^8 d^12 Inf_j(f)^2`, and it assumes
`0 < variance f` where Theorem 1.1 assumes `n ≥ 1` and `d ≥ 1`; the two forms are equivalent
(`Bridge.mainTheorem_iff_printed`).

The passage from `MainTheorem` to the three Mathlib-only statements is in
`Bridge/Capstone.lean` (`Bridge.explicitBoundPM`, `Bridge.explicitBound`,
`Bridge.printedConjecture`), with its steps in `Bridge/PrintedAA.lean`. The substitution in the
proof of Corollary 1.2 is `Bridge.zero_one_of_mainBound` for functions on the cube and
`Bridge.zo_of_mainBound` for polynomials; the forms with the power `5/2` come from
`Bridge.sqrt_form_iff` and `Bridge.rpow_five_halves`; the step to the exponent `7` is
`Bridge.ratio_pow_le`, used in `Bridge.zo_pow_of_mainTheorem`. `ExplicitBoundPM` encodes the bit
`true` as `1` and the bit `false` as `−1`, while `Defs.lean` sends `true` to `−1`. Negating every
bit carries the encoding of `ExplicitBoundPM` to the encoding of `Defs.lean`
(`Bridge.evPMt_eq`, `Bridge.negBits_flipBit`); `Bridge.pmt_sq_of_mainTheorem` and
`Bridge.pmt_sqrt_of_mainTheorem` follow from `Bridge.pm_sq_of_mainTheorem` and
`Bridge.pm_sqrt_of_mainTheorem` (the bounds in the encoding of `Defs.lean`) by `Bridge.evPMt_eq`
and `Bridge.negBits_flipBit`. The assertions `n ≥ 1` and `d ≥ 1` of Corollary 1.2 are
`Bridge.aa_hyps_force`, and `Var[p] ≤ 1/4` is `Bridge.variance_le_quarter`
(`Bridge/Affine.lean`); for polynomials, `d ≥ 1` and `ε ≤ 1/4` are `Bridge.zo_hyps_force`.

Corollary 1.2 states its two bounds for `Var[p]` and then for every `ε` with
`Var[p] ≥ ε > 0`. The Lean statements have the second form; the first is its case
`ε = Var[p]`.

## Section 2: notation and definitions

| Paper | Lean | Where |
|---|---|---|
| the unique expansion in the characters `χ_T`, and the degree | `Bridge.fourier_inversion`, `Bridge.fourier_unique`, `Bridge.hasDegreeLE_iff_fourier` | `Bridge/Fourier.lean` |
| `E[(h - c)^2] ≥ Var(h)` | `Level.variance_le_sq_dist` | `Level/Basic.lean` |
| `L_j(f)^2 ≤ 4 Inf_j(f)` | `Level.meanAbsIncr_sq_le` | `Level/Basic.lean` |
| Lemma 2.1 | `two_mul_bdry` | `TwoSided/Overlap.lean` |
| Definition 2.2 (wings) | `IsWing` | `Defs.lean` |
| Definition 2.3 (rows) | `IsRow` for Boolean functions; for real functions see "Conventions" | `Defs.lean` |
| Lemma 2.4 (i) | `Bridge.isRow_one` | `Bridge/Positivity.lean` |
| Lemma 2.4 (ii) | `Bridge.row_norm_ge_one` (the inequality for the norm of a row; `n ≥ 1` is not stated separately) | `Bridge/Positivity.lean` |
| Lemma 2.4 (iii) | `Level.isRow_levRow` (which also covers the case `f(x) = t`, by (i); it assumes a row of `f` at every point, and the paper one at `x`) | `Level/Rows.lean` |

## Section 3: the bijection theorem and the determinant inequality

| Paper | Lean | Where |
|---|---|---|
| Theorem 3.1 (bijection theorem) | `DetBij.exists_perm` (for the inverse permutation); `DetBij.exists_bijection` (the wording of the paper) | `DetBij/Perm.lean`, `DetBij/Bijection.lean` |
| Corollary 3.2 (determinant inequality) | statement `DetInequality`, proof `detInequality` | `Statements.lean`, `DetTheorem.lean` |
| Corollary 3.2, as printed (with the minimum `D_g(u, A_u; ℓ)`) | `Bridge.DetInequalityPrinted`, `Bridge.detInequality_iff_printed` | `Bridge/PaperInequalities.lean` |
| proof of Corollary 3.2 from Theorem 3.1 | `DetBij.detInequality_of_lowest`, through `DetBij.det_inequality_of_perm`; `DetBij.extWing` puts `A_x = ∅` outside the zone | `DetBij/Main.lean` |
| the agreement matrix `M` and its entries | `agMatrix`, `agMon`, on the type `Ones g` | `DetDefs.lean` |
| Lemma 3.3 | statement `LowestUnit`, proof `DetLow.lowestUnit` | `DetDefs.lean`, `DetLow/Unit.lean`, `DetLow/Main.lean` |
| Lemma 3.4 | `DetLow.agMatrix_det_ne_zero` | `DetLow/NonZero.lean` |
| Lemma 3.5 | `DetLow.det_factor` | `DetLow/RowOps.lean` |
| Lemma 3.6 (with Lemma 3.4) | statement `LowestBound`, proof `DetLow.lowestBound`; Steps 1 and 2 of the proof are `DetLow.degreeOf_det_le` and `DetLow.card_ones_eq` | `DetDefs.lean`, `DetLow/Main.lean`, `DetLow/Degree.lean`, `DetLow/Count.lean` |
| Lemma 3.7 (wing identity) | `DetBij.wing_sum` | `DetBij/Identity.lean` |
| Lemma 3.8 (i) | `DetBij.Pmat_mul_agMatrix` | `DetBij/Identity.lean` |
| Lemma 3.8 (ii) | `DetBij.constantCoeff_det_Pmat`, `DetBij.constantCoeff_det_Umat` | `DetBij/Identity.lean` |
| Lemma 3.8 (iii) | `DetBij.exists_lowest_Qmat` (a weaker form, which is what the proof of Theorem 3.1 uses) | `DetBij/Perm.lean` |

`DetInequality` is stated with an arbitrary lower bound `d u` for the sums `ℓ(G)` in place of
their minimum; `Bridge.detInequality_iff_printed` shows that this is the printed statement.
The theorems `DetBij.exists_perm` and `DetBij.exists_bijection` take `LowestUnit` and
`LowestBound` as hypotheses; both are proved in `DetLow`, and the bijection theorem without
hypothesis is `DetBij.exists_bijection DetLow.lowestUnit DetLow.lowestBound`.
`DetBij.exists_bijection` is not used in the proof of the main theorem.

## Section 4: the antipodal inequality

| Paper | Lean | Where |
|---|---|---|
| Lemma 4.1 (overlap) | `overlap`, `overlap_pos` | `TwoSided/Overlap.lean` |
| Lemma 4.2 (pointwise step) | `wing_of_row` (Steps 1 and 2), `lower_of_row` (Step 3), `wingSet` | `TwoSided/Antipodal.lean` |
| Theorem 4.3 (antipodal inequality) | statement `AntipodalInequality`, proof `antipodalInequality` (through `antipodal_of_det`); positivity of the inverted sums: `Bridge.antipodal_inner_pos` | `Statements.lean`, `Chain.lean`, `TwoSided/Antipodal.lean`, `Bridge/Positivity.lean` |

## Section 5: the all-pairs inequality and the two-sided inequality

| Paper | Lean | Where |
|---|---|---|
| Lemma 5.1 (gluing) | `glue`; part (i): `glue_flipSet`, `glue_antipode`, `glue_flipSet_singleton_of_mem`, `glue_flipSet_singleton_of_not_mem`; part (ii): `sum_sum_glue` | `TwoSided/Glue.lean` |
| Proposition 5.2 (all-pairs inequality) | statement `AllPairsInequality` (the inequality multiplied by `2`), proof `allPairsInequality` (through `allPairs_of_antipodal`); positivity: `Bridge.allPairs_inner_pos` | `AllPairsDefs.lean`, `Chain.lean`, `TwoSided/AllPairs.lean`, `Bridge/Positivity.lean` |
| Step 1 of the proof of Proposition 5.2 | `allPairsTerm` (the term `T_F(x)`), `allPairs_core` | `TwoSided/AllPairsCore.lean` |
| Lemma 5.3 (removing the weights) | `abstract_cs`; its Steps 1, 2 and 3 are `pair_cs`, `weight_choice` and a part of `cs_core`, and its conclusion uses `le_of_sq_le_mul` | `TwoSided/CauchySchwarz.lean` |
| Theorem 5.4 (two-sided inequality) | statement `TwoSidedInequality`, proof `twoSidedInequality` (through `twoSided_of_allPairs`); the assertion `‖λ^x‖ ≥ 1`: `Bridge.row_norm_ge_one` | `Statements.lean`, `Chain.lean`, `TwoSided/RemoveWeights.lean`, `Bridge/Positivity.lean` |

`abstract_cs` does not assume that the two index sets are non-empty, and it writes the
reciprocals of the costs with `⁻¹`. The first assertion of Lemma 5.3, that the costs are
positive, is therefore not part of it; where the lemma is applied the costs are positive by
`Bridge.row_norm_ge_one` and by `Level.rowSum_pos`.

`TwoSidedInequality` is stated for every `τ ≥ 0` that bounds all the influences `I_j(g)`, and for
every `g`, constant or not; `Bridge.twoSided_iff_printed` shows that it is equivalent to the
printed statement with `max_j I_j(g)`.

## Section 6: the row bound

| Paper | Lean | Where |
|---|---|---|
| Lemma 6.1 (Markov's inequality at an endpoint) | statement `MarkovEndpoint` (the second assertion of the lemma, on `[0,2]`), proof `markovEndpoint` | `RowDefs.lean`, `Row/Markov.lean` |
| Lemma 6.2 (extension) | `Row.abs_multilinear_le_one` | `Row/Extension.lean` |
| Lemma 6.3 (sensitivity lemma) | `Row.sum_abs_sub_unit_le`; the polynomial of the proof is `Row.phi` | `Row/Sensitivity.lean` |
| Lemma 6.4 (block inequality) | statement `BlockInequality`, proof `blockInequality` (through `blockInequality_of_markov`); the function `G` of the proof is `Row.gadget`, and its properties (a) to (d) are `Row.abs_gadget_le_one`, `Row.hasDegreeLE_gadget`, `Row.gadget_zero`, `Row.gadget_unit` | `RowDefs.lean`, `Row/Main.lean`, `Row/Block.lean`, `Row/Gadget.lean`, `Row/Degree.lean`, `Row/Chi.lean` |
| Lemma 6.5 (packing bound) | statement `PackingBound`, proof `packingBound` (through `Pack.scaled_bound`, `Pack.le_of_scaled` and `packingBound_of_block`) | `RowDefs.lean`, `Chain.lean`, `Pack/Scaled.lean`, `Pack/Packing.lean` |
| Proposition 6.7 (duality) | `Dual.exists_cover`; statement `CoverDuality`, proof `coverDuality` | `Dual/Cover.lean`, `RowDefs.lean` |
| Theorem 6.8 (row bound) | statement `RowBoundPM`, proof `rowBoundPM` (through `rowBoundPM_of_packing`) | `RowDefs.lean`, `Chain.lean`, `Dual/Row.lean` |
| Theorem 6.8, as printed | `Bridge.RowBoundPMPrinted`, `Bridge.rowBoundPM_iff_printed` | `Bridge/PaperTheorems.lean` |
| Remark 6.9 (the bound of Agarwal and Ben-David) | `RowBound`, a hypothesis that is never proved; its printed form is `Bridge.FbsDegPrinted` (`Bridge.rowBound_iff_printed`), and its Mathlib-only form is `FbsDegreeBound`; the rows of cost at most `π² d² / 2` that it gives: `rows_of_rowBound` | `Statements.lean`, `Bridge/PrintedRow.lean`, `Conjecture.lean`, `MainTheorem.lean` |
| Corollary 6.10 (sensitivity at every point) | statement `SensitivityBound`, proof `sensitivityBound` (through `sensitivity_of_block`); the consequence `L(f) ≤ 4 d²` is obtained with `Level.sum_meanAbsIncr_le` | `Statements.lean`, `Chain.lean`, `Row/DisjointBlocks.lean`, `Level/Basic.lean` |

`CoverDuality` has the two extra hypotheses `0 ≤ K` and `t ∅ ≤ 0`, which hold where it is used.

## Section 7: real functions and integration over the level

| Paper | Lean | Where |
|---|---|---|
| the level functions `g_t` and their rows `λ^{t,x}` | `Level.lev`, `Level.levRow`, `Level.isRow_levRow` | `Level/Rows.lean` |
| Lemma 7.1 (i) | `Level.sum_levRow` | `Level/AllPairs.lean` |
| Lemma 7.1 (ii) | `Level.pairSum_pos` | `Level/AllPairs.lean` |
| Lemma 7.2 (the all-pairs inequality at a level) | `Level.level_allPairs` (the inequality multiplied by `2`) | `Level/AllPairs.lean` |
| the formula for `b_j(g_t)` at the beginning of Section 7.2 | `Level.bdry_lev` | `Level/AllPairs.lean` |
| Lemma 7.3 (i) | `Level.integral_quad`, `Level.integral_posParts` | `Level/Integral.lean` |
| Lemma 7.3 (ii) | no statement of its own; it is proved inside `Level.level_integration`, with `Level.ind_eq_stp` and `Level.integral_stp` | `Level/Integral.lean` |
| Lemma 7.3 (iii) | `Level.sum_posPart_incr` | `Level/Integrated.lean` |
| the integration of an inequality that holds at every level (Section 7.2) | `Level.level_integration` | `Level/Integral.lean` |
| Proposition 7.4 (integrated all-pairs inequality) | statement `IntegratedAllPairsInequality`, proof `integratedAllPairsInequality` (through `integratedAllPairs_of_allPairs`, with `Level.integrated_core` and `Level.integrated_four_mul`); positivity of the sums `s_xy(w)`: `Level.pairSum_pos` | `Statements.lean`, `Chain.lean`, `Level/Integrated.lean`, `Level/AllPairs.lean` |
| Theorem 7.6 (third-moment inequality), first inequality | statement `ThirdMomentInequality`, proof `thirdMomentInequality` (through `thirdMoment_of_integratedAllPairs`, with `Level.thirdMoment_core`) | `Statements.lean`, `Chain.lean`, `Level/ThirdMoment.lean` |
| Theorem 7.6, second inequality | `Level.thirdMoment_lower` | `Level/ThirdMoment.lean` |
| Corollary 7.7 (separated sets) | `Level.separated_sets` (for `θ ≥ 0`) | `Level/ThirdMoment.lean` |
| Lemma 7.8 (median) | `Level.exists_median` | `Level/Median.lean` |
| Lemma 7.9 (second and third moments) | `Level.sum_sq_cube_le` | `Level/Median.lean` |
| Theorem 7.10 (mean absolute increments) | statement `MeanIncrementBound` (the inequality `Var(f)^3 ≤ 36 K^4 L_j(f)^2`), proof `meanIncrementBound` (through `meanIncrement_of_thirdMoment`); Steps 1 and 2 of the proof are `Level.exists_abs_cube_le` and `Level.variance_cube_le` | `Statements.lean`, `Chain.lean`, `Level/Increments.lean` |
| Theorem 7.10, as printed (rows as in Definition 2.3, `K > 0`, both forms of the bound) | `Bridge.MeanIncrementPrinted`, `Bridge.meanIncrement_iff_printed` | `Bridge/PaperTheorems.lean` |
| the assertions of Theorem 7.10 one by one: `n ≥ 1`; `K > 0`; the form with the power `3/2` | `Level.variance_eq_zero_of_isEmpty` (by contraposition); `Level.cost_pos`; `Level.exists_meanAbsIncr_ge_sqrt`, with `Level.cube_le_iff_mul_sqrt_le` | `Level/Basic.lean`, `Level/Increments.lean` |
| Corollary 7.11 | statement `MeanIncrementDegreeBound` (the inequality `Var(f)^3 ≤ 36 π^8 d^8 L_j(f)^2`), proof `meanIncrementDegreeBound` (through `meanIncrementDegree_of_meanIncrement`) | `Statements.lean`, `Chain.lean`, `MainTheorem.lean` |
| Corollary 7.11, as printed (`d ≥ 1`, the power `3/2`) | `Bridge.MeanIncrementDegreePrinted`, `Bridge.meanIncrementDegree_iff_printed` | `Bridge/PaperTheorems.lean` |
| Remark 7.12 (1) | `Level.exists_rows_cost` | `Level/Basic.lean` |
| Remark 7.12 (2) | `Level.abs_sub_le_rowSum` | `Level/Basic.lean` |

`ThirdMomentInequality`, like Theorem 7.6, is stated for every `M ≥ 0` that bounds all the
numbers `L_j(f)`.

## Section 8: averaging and the proof of the main theorem

| Paper | Lean | Where |
|---|---|---|
| Lemma 8.1 (i) | `Average.mean_avg`, `Average.variance_avg` | `Average/Coordinate.lean` |
| Lemma 8.1 (ii) | `Average.inflR_avg_le`, `Average.meanAbsIncr_avg_le` | `Average/Coordinate.lean` |
| Lemma 8.1 (iii) | `Average.meanAbsIncr_avg_self` | `Average/Coordinate.lean` |
| Lemma 8.1 (iv) | `Average.rows_avg` | `Average/Coordinate.lean` |
| Lemma 8.2 (averaging over a set of coordinates) | `Average.exists_avg_set` | `Average/Iterate.lean` |
| Theorem 8.3 (influences) | statement `InfluenceBound` (the inequality `3 Var(f)^5 ≤ 3125 L(f)^2 K^4 Inf_j(f)^2`), proof `influenceBound` (through `influence_of_meanIncrement`) | `Statements.lean`, `Chain.lean`, `Average/Influence.lean` |
| Theorem 8.3, as printed (rows as in Definition 2.3, `0 < L(f) ≤ K`, the three forms of the bound) | `Bridge.InfluencePrinted`, `Bridge.influence_iff_printed` | `Bridge/PaperTheorems.lean` |
| the assertions of Theorem 8.3 one by one: `0 < L(f)`; `L(f) ≤ K`; the form with the power `5/2`; the bound with `K^3` | `Average.sum_meanAbsIncr_pos`; `Level.sum_meanAbsIncr_le_cost`; `Average.exists_inflR_ge_sqrt`, with `Average.pow_le_iff_sqrt_mul_le`; `Average.influence_cost` (in the form `3 Var(f)^5 ≤ 3125 K^6 Inf_j(f)^2`) | `Average/Influence.lean`, `Level/Basic.lean` |
| proof of Theorem 1.1 (Theorem 8.3 with `K = π² d²`, Theorem 6.8 and Corollary 6.10) | `mainTheorem_of_influence`, through `Average.influence_of_incr` | `MainTheorem.lean`, `Average/Influence.lean` |
| Remark 8.4 (1): the constants with the bound of Agarwal and Ben-David | statement `MainTheoremImproved`, proof `mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved` (through `rows_of_rowBound` and `mainTheoremImproved_of_influence`); Mathlib-only form `aaronson_ambainis_of_fbsDegreeBound : FbsDegreeBound → ExplicitBoundImproved` | `Statements.lean`, `Chain.lean`, `MainTheorem.lean`, `Main.lean` |

## Statements of the paper with no Lean counterpart

* Sections 1.3 and 1.4 (motivation, consequences and earlier work), Section 1.5 (the overview
  of the proof) and Section 9 (remarks and open questions).
* Section 7.5 (the relation to the argument of Lovett and Zhang) and Appendix A (the timeline
  of the discovery).
* The observation after Definition 2.3 that, for a Boolean function, the definition amounts to
  the condition on sensitive blocks. `IsRow` is defined by that condition.
* The examples (Examples 2.5, 3.9, 4.4, 5.5 and 7.5).
* Remark 3.10 (the relation to Reimer's Butterfly Lemma).
* The first assertion of Lemma 6.1, Markov's inequality at the endpoint `1` of `[-1,1]`. Only
  the form on `[0,2]`, which is the one that is used, is stated in Lean.
* Lemma 6.6 (separation from the orthant). The Lean proof of Proposition 6.7 uses the
  Hahn–Banach separation theorem of Mathlib, `geometric_hahn_banach_compact_closed`, in its
  place.
* The consequence of Corollary 7.11 for the influences that is drawn after its proof. The
  library has the inequality `L_j(f)^2 ≤ 4 Inf_j(f)` that it uses
  (`Level.meanAbsIncr_sq_le`), but it states no bound for the influences obtained in this way.
* Remark 7.12 (3) (the statements are compatible with scaling).
* The averages `Av_R f` over a set of coordinates and the identity
  `Av_{R ∪ {j}} f = Av_j(Av_R f)` of Section 8.1. See the next section.
* Remark 8.4 (2), the further factor `2` from the inequality of Filmus, Hatami, Keller and
  Lifshitz, and Remark 8.5 (the exponents).

## Where the Lean proof takes another route

* The powers `3/2` and `5/2`. Theorems 7.10 and 8.3 of the paper state each bound in two forms,
  as an inequality without square roots and with the power `3/2` or `5/2` of the variance;
  Theorem 1.1 and Corollaries 1.2 and 7.11 are stated with the powers only. The propositions
  of the chain are the inequalities without square roots: `Var(f)^3 ≤ 36 K^4 L_j(f)^2`
  (`MeanIncrementBound`), `3 Var(f)^5 ≤ 3125 L(f)^2 K^4 Inf_j(f)^2` (`InfluenceBound`),
  `Var(f)^3 ≤ 36 π^8 d^8 L_j(f)^2` (`MeanIncrementDegreeBound`) and
  `3 Var(f)^5 ≤ 50000 π^8 d^12 Inf_j(f)^2` (`MainTheorem`). The forms with the powers are
  deduced from them at the end: `Bridge.meanIncrement_iff_printed`,
  `Bridge.influence_iff_printed`, `Bridge.meanIncrementDegree_iff_printed`,
  `Bridge.mainTheorem_iff_printed`, and, for the statements of `Conjecture.lean`,
  `Bridge.sqrt_form_iff` with `Bridge.rpow_five_halves`. In particular `MainTheorem` is
  obtained from the first form of Theorem 8.3, while the proof of Theorem 1.1 in the paper uses
  the form with the power `5/2`.
* Corollary 1.2. The paper applies Theorem 1.1 to `f = 2p - 1`, the library to `1 - 2p`
  (`Bridge.zero_one_of_mainBound`); the variance and the influences are the same. For the
  exponent `7` the paper compares the two bounds directly, with `√15 > 7/2` and `π^4 < 100`;
  the library deduces `(ε/d)^7 ≤ Inf_i[p]` from `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]^2`, with
  `3125 π^8 ε^9 ≤ 192` for `ε ≤ 1/4` (`Bridge.ratio_pow_le`).
* Theorem 3.1. The Lean proof constructs the inverse of the bijection of the paper
  (`DetBij.exists_perm`); `DetBij.exists_bijection` translates.
* Lemma 3.4. The paper uses the unique monomial of highest total degree in the determinant:
  the identity permutation contributes `(s₁ ⋯ sₙ)^|O|`, and every other permutation contributes
  a monomial of strictly smaller total degree. The Lean proof (`DetLow/NonZero.lean`) instead
  specializes the variables and uses strict diagonal dominance, via the theorem
  `det_ne_zero_of_sum_row_lt_diag` of Mathlib.
* Lemma 6.1. The paper proves Markov's inequality at an endpoint by interpolation at the
  points `cos(kπ/D)`. The Lean proof (`Row/Markov.lean`) deduces it from the theorem
  `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one` of Mathlib.
* Proposition 6.7. See Lemma 6.6 above.
* Corollary 6.10. The library first states the block inequality for pairwise disjoint blocks
  (`Row.disjoint_blocks_of_block`) and then takes the blocks `{j}`.
* Section 7.2. The paper integrates over the real line functions that vanish outside a
  bounded interval. `Level.level_integration` integrates over a bounded interval that contains
  all the levels which occur, and writes the indicator of `[p, q)` as a difference of two
  step functions (`Level.stp`).
* Factors `2` and `4`. `AllPairsInequality` and `Level.level_allPairs` are the printed
  inequalities multiplied by `2`, and `Level.integrated_four_mul` is the integrated
  inequality multiplied by `4`, so that `2^n` and `4^n` appear. In
  `IntegratedAllPairsInequality` the factor is `4 ^ (n - 1)` as printed; the exponent is a
  difference of natural numbers, and for `n = 0` it is `0` and both sides are `0`.
* Lemma 8.2. The paper defines the average `Av_R f` over a set `R` of coordinates by a
  formula, shows that it is obtained by averaging over one coordinate at a time, and proves
  the lemma by induction on `R`. The library makes the same induction, but it does not name
  the function: `Average.exists_avg_set` asserts that there is a function with the four
  properties of the lemma, obtained by applying `Average.avg` once for each coordinate of `R`.
* Proof of Theorem 1.1. The paper treats the case `Var(f) = 0` first. `MainTheorem` assumes
  `0 < variance f`, and the case of variance zero is in
  `Bridge.mainTheoremPrinted_of_mainTheorem`.
* Remark 8.4 (1). In the paper the constants that the row bound of Agarwal and Ben-David
  gives are a remark, by citation of their theorem. In the library they are a theorem with a
  named hypothesis: `mainTheoremImproved_of_rowBound : RowBound → MainTheoremImproved` on the
  cube, and `aaronson_ambainis_of_fbsDegreeBound` for the statements of `Conjecture.lean`.
  The further factor `2` of Remark 8.4 (2) is in the paper only.

## Lean results that the paper does not state

| Lean | Content | Where |
|---|---|---|
| `Bridge.explicitBound_sq`, `Bridge.explicitBoundPM_sq`, `Bridge.explicitBoundImproved_sq_of_fbsDegreeBound` | the bounds for polynomials without square roots, written with the abbreviations `Bridge.Ex`, `Bridge.ev01`, `Bridge.evPMt` and `Bridge.flipBit` of `Bridge/PrintedAA.lean`: `192 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]^2`, `3 ε^5 ≤ 50000 π^8 d^12 Inf_i(f)^2`, and `3072 ε^5 ≤ 3125 π^8 d^12 Inf_i[p]^2` under the hypothesis `FbsDegreeBound` | `Bridge/Capstone.lean` |
| `Bridge.MainBound`, `Bridge.zo_of_mainBound`, `Bridge.pm_of_mainBound` | the passage to polynomials for a bound of the kind of the main theorem with an arbitrary constant | `Bridge/PrintedAA.lean` |
| `Average.influence_of_incr` | Theorem 8.3 with, in place of `L(f)`, a number that bounds at every point `x` the sum over `j` of the absolute increments of `f` at `x` in the coordinate `j` | `Average/Influence.lean` |
| `Bridge.TwoSidedMinCost`, `Bridge.twoSidedMinCost_of_twoSided` | the two-sided inequality with the least cost of a row at each point | `Bridge/PaperInequalities.lean` |
| `Bridge.AntipodalOnZone`, `Bridge.antipodal_iff_onZone` | the antipodal inequality with rows given only on `Z(g)` and its antipodes | `Bridge/Positivity.lean` |
| `Bridge.AllPairsNonconstant`, `Bridge.allPairs_iff_nonconstant` | the all-pairs inequality for non-constant `g`, as one sum over pairs | `Bridge/Positivity.lean` |
| `Bridge.PackingBoundNonempty`, `Bridge.packingBound_iff_nonempty` | the packing bound with the family indexed by the non-empty sets | `Bridge/PaperInequalities.lean` |
| `Row.disjoint_blocks_of_block` | the block inequality for pairwise disjoint blocks (the case `N = 1`, `m = 1` of Lemma 6.4) | `Row/DisjointBlocks.lean` |
| `Row.not_blockInequality_without_pos` | Lemma 6.4 fails if the hypothesis `m ≥ 1` is dropped | `Row/HypothesisCheck.lean` |
| `Dual.packingBound_iff_rowBoundPM`, `Dual.cover_iff_packing` | the packing bound and the row bound are equivalent | `Dual/Sanity.lean` |
| `Dual.rowBoundPM_of_rowBound`, `Dual.packingBound_of_rowBound` | the hypothesis `RowBound` implies the row bound and the packing bound that are proved here | `Dual/Sanity.lean` |
| `Bridge.rowBound_iff_printedML`, `Bridge.rowBound_iff_fin` | two further forms of the hypothesis `RowBound` | `Bridge/PrintedRow.lean`, `Bridge/Transport.lean` |
| `DetLow.exists_lowest_le_bdry`, `DetLow.exists_monomial_weight_le` | two corollaries of `DetLow.lowestBound` | `DetLow/Corollary.lean` |
| `Bridge.conj6_instance`, `Bridge.problemPM_instance` | the hypotheses of the Mathlib-only statements can be satisfied (the statements are not vacuous) | `Bridge/Instance.lean` |
