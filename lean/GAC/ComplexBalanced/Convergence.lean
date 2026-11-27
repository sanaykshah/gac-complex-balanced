import GAC.ComplexBalanced.Dissipation

/-!
# The LaSalle-type step for complex-balanced systems (part of Lemma G)

New file. The proof of `dissip_eq_zero_of_mapClusterPt_of_nonpos` is adapted from
`GAC.dissip_eq_zero_of_mapClusterPt` in `lean/GAC/DetailedBalance.lean`
(BitMiracle-AI/detailed-balance-gac v1.0, Apache-2.0). Modification: the detailed-balance
hypothesis is replaced by the only two facts the proof uses, positivity of `xs` and
`dissip ≤ 0` on the positive orthant, so the lemma applies under complex balance.
-/

open Filter Topology GAC.Persistence

noncomputable section

namespace GAC

variable {d : ℕ} {N : ReactionNetwork d} {κ : Reaction N → ℝ} {xs : Fin d → ℝ}

/-- If `dissip ≤ 0` on the positive orthant and a trajectory stays uniformly away from the
boundary with bounded speed, then `dissip = 0` at every positive cluster point of the trajectory.
(Adapted from `GAC.dissip_eq_zero_of_mapClusterPt`; see the module docstring.) -/
lemma dissip_eq_zero_of_mapClusterPt_of_nonpos (hxs : PositiveState xs)
    (hnonpos : ∀ w : Fin d → ℝ, PositiveState w → dissip N κ xs w ≤ 0)
    {x0 : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : ℝ → Fin d → ℝ}
    (hx : IsGlobalForwardSolution N κ x0 x)
    (hbd : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹)
    {B : ℝ} (hB : 0 < B) (hspeed : ∀ t : ℝ, 0 ≤ t → ‖massAction N κ (x t)‖ ≤ B)
    {z : Fin d → ℝ} (hzpos : PositiveState z) (hz : MapClusterPt z atTop x) :
    dissip N κ xs z = 0 := by
  have hpos : ∀ t : ℝ, 0 ≤ t → PositiveState (x t) :=
    fun t ht i => hε.trans_le (hbd t ht i).1
  set W : ℝ → ℝ := fun s => lyap xs (x s) with hWdef
  have hW : ∀ s : ℝ, 0 ≤ s → HasDerivAt W (dissip N κ xs (x s)) s :=
    fun s hs => hasDerivAt_lyap (hx.2 s hs) (hpos s hs)
  have hanti : ∀ a b : ℝ, 0 ≤ a → a ≤ b → W b ≤ W a := by
    intro a b ha hab
    rcases hab.eq_or_lt with h | hlt
    · rw [h]
    · have := sub_le_of_hasDerivAt_le hlt (fun s hs => hW s (ha.trans hs.1))
        (fun s hs => hnonpos _ (hpos s (ha.trans hs.1.le)))
      linarith
  by_contra hne
  have hneg : dissip N κ xs z < 0 := lt_of_le_of_ne (hnonpos z hzpos) hne
  set η : ℝ := -dissip N κ xs z / 2 with hη
  have hηpos : 0 < η := by linarith
  have hev : ∀ᶠ w in 𝓝 z, dissip N κ xs w < -η :=
    (continuousAt_dissip κ xs hzpos).eventually (Iio_mem_nhds (by linarith))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set δ : ℝ := r / (2 * B) with hδdef
  have hδ : 0 < δ := by positivity
  have hne' : (W '' Set.Ici 0).Nonempty := ⟨W 0, 0, le_refl (0 : ℝ), rfl⟩
  have hbdd : BddBelow (W '' Set.Ici 0) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨s, hs, rfl⟩
    exact lyap_nonneg hxs (hpos s hs)
  set c : ℝ := sInf (W '' Set.Ici 0) with hcdef
  have hlt : c < c + η * δ := by nlinarith
  obtain ⟨_, ⟨T, hT, rfl⟩, hTlt⟩ := exists_lt_of_csInf_lt hne' hlt
  have hT0 : (0 : ℝ) ≤ T := hT
  have hfreq := (mapClusterPt_iff_frequently.mp hz) (Metric.ball z (r / 2))
    (Metric.ball_mem_nhds z (by positivity))
  obtain ⟨t, htT, htz⟩ := frequently_atTop.mp hfreq T
  have ht0 : 0 ≤ t := hT0.trans htT
  have hmove : ∀ s ∈ Set.Icc t (t + δ), ‖x s - x t‖ ≤ B * (s - t) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (f := x)
      (f' := fun s => massAction N κ (x s))
      (fun s hs => (hx.2 s (ht0.trans hs.1)).hasDerivWithinAt)
      (fun s hs => hspeed s (ht0.trans hs.1))
  have hBδ : B * δ = r / 2 := by rw [hδdef]; field_simp
  have hnear : ∀ s ∈ Set.Icc t (t + δ), dist (x s) z < r := by
    intro s hs
    have h1 := hmove s hs
    have h2 : B * (s - t) ≤ B * δ :=
      mul_le_mul_of_nonneg_left (by linarith [hs.2]) hB.le
    have h3 : dist (x t) z < r / 2 := htz
    calc dist (x s) z ≤ dist (x s) (x t) + dist (x t) z := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [dist_eq_norm]; linarith
      _ = r := by ring
  have hdrop := sub_le_of_hasDerivAt_le (show t < t + δ by linarith)
    (fun s hs => hW s (ht0.trans hs.1))
    (fun s hs => (hball (hnear s ⟨hs.1.le, hs.2.le⟩)).le)
  have hWt : W t ≤ W T := hanti T t hT0 htT
  have hWc : c ≤ W (t + δ) := csInf_le hbdd ⟨t + δ, by simp only [Set.mem_Ici]; linarith, rfl⟩
  have : -η * (t + δ - t) = -(η * δ) := by ring
  linarith

/-- The LaSalle-type step under complex balance: `dissip = 0` at every positive cluster point
of a persistent trajectory with bounded speed. -/
theorem IsComplexBalanced.dissip_eq_zero_of_mapClusterPt (hκ : ∀ e, 0 < κ e)
    (hcb : IsComplexBalanced N κ xs)
    {x0 : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) {x : ℝ → Fin d → ℝ}
    (hx : IsGlobalForwardSolution N κ x0 x)
    (hbd : ∀ t : ℝ, 0 ≤ t → ∀ i : Fin d, ε ≤ x t i ∧ x t i ≤ ε⁻¹)
    {B : ℝ} (hB : 0 < B) (hspeed : ∀ t : ℝ, 0 ≤ t → ‖massAction N κ (x t)‖ ≤ B)
    {z : Fin d → ℝ} (hzpos : PositiveState z) (hz : MapClusterPt z atTop x) :
    dissip N κ xs z = 0 :=
  dissip_eq_zero_of_mapClusterPt_of_nonpos hcb.pos (fun _ hw => hcb.dissip_nonpos hκ hw)
    hε hx hbd hB hspeed hzpos hz

end GAC
