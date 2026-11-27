import GAC.ComplexBalanced.Dissipation
import GAC.ComplexBalanced.WeakReversibility

/-!
# Global convergence for complex-balanced systems (Lemma G)

New file. Two proofs here are adapted from `lean/GAC/DetailedBalance.lean`
(BitMiracle-AI/detailed-balance-gac v1.0, Apache-2.0):

* `dissip_eq_zero_of_mapClusterPt_of_nonpos` from `GAC.dissip_eq_zero_of_mapClusterPt`.
  Modification: the detailed-balance hypothesis is replaced by the only two facts the proof
  uses, positivity of `xs` and `dissip ≤ 0` on the positive orthant.
* `IsComplexBalanced.global_convergence` from `GAC.detailed_balanced_global_convergence`.
  Modification: each use of detailed balance is replaced by its complex-balanced counterpart
  (Lemmas C, D, E, F and the LaSalle step below).
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

/-- Under complex balance, two positive equilibria in the same compatibility class are equal.
(Complex-balanced counterpart of `GAC.eq_of_equilibria`.) -/
lemma IsComplexBalanced.eq_of_equilibria (hκ : ∀ e, 0 < κ e) (hcb : IsComplexBalanced N κ xs)
    {a b : Fin d → ℝ} (ha : PositiveState a) (hb : PositiveState b)
    (hfa : massAction N κ a = 0) (hfb : massAction N κ b = 0)
    (hab : a - b ∈ stoichSubspace N) : a = b :=
  eq_of_gap_zero ha hb
    (hcb.gap_zero_of_dissip_eq_zero hκ ha (dissip_eq_zero_of_massAction_eq_zero hfa))
    (hcb.gap_zero_of_dissip_eq_zero hκ hb (dissip_eq_zero_of_massAction_eq_zero hfb)) hab

/-- **Lemma G.** Global convergence of complex-balanced mass-action systems.
(Adapted from `GAC.detailed_balanced_global_convergence`; see the module docstring.) -/
theorem IsComplexBalanced.global_convergence
    (N : ReactionNetwork d) (κ : Reaction N → ℝ) (hκ : ∀ e, 0 < κ e)
    {xs : Fin d → ℝ} (hcb : IsComplexBalanced N κ xs)
    (x0 : Fin d → ℝ) (hx0 : PositiveState x0) :
    ∃ xbar : Fin d → ℝ,
      PositiveState xbar ∧ massAction N κ xbar = 0 ∧ xbar - x0 ∈ stoichSubspace N ∧
      (∀ z : Fin d → ℝ, PositiveState z → massAction N κ z = 0 →
        z - x0 ∈ stoichSubspace N → z = xbar) ∧
      (∃ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x) ∧
      ∀ x : ℝ → (Fin d → ℝ), IsGlobalForwardSolution N κ x0 x →
        Tendsto x atTop (𝓝 xbar) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · -- With no species the state space is a single point.
    refine ⟨x0, fun i => i.elim0, Subsingleton.elim _ _,
      by rw [sub_self]; exact Submodule.zero_mem _,
      fun z _ _ _ => Subsingleton.elim _ _, ⟨fun _ => x0, rfl, fun t _ => ?_⟩, fun x _ => ?_⟩
    · convert hasDerivAt_const t x0
    · have : x = fun _ => x0 := funext fun _ => Subsingleton.elim _ _
      rw [this]
      exact tendsto_const_nhds
  -- Boundedness and persistence, via Lemma F.
  obtain ⟨ε, hε, -, ⟨x₁, hx₁⟩, hbd⟩ :=
    bounded_persistent_of_weaklyReversible d N κ hd (hcb.weaklyReversible hκ) hκ x0 hx0
  set S := stoichSubspace N with hSdef
  set K : Set (Fin d → ℝ) := (Set.univ.pi fun _ => Set.Icc ε ε⁻¹) ∩ {z | z - x0 ∈ S} with hKdef
  have hK : IsCompact K :=
    (isCompact_univ_pi fun _ => isCompact_Icc).inter_right
      ((S.closed_of_finiteDimensional).preimage (continuous_id.sub continuous_const))
  have hmemK : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ t : ℝ, 0 ≤ t → x t ∈ K :=
    fun x hx t ht => ⟨fun i _ => hbd x hx t ht i, sol_mem_class hx ht⟩
  have hKpos : ∀ z ∈ K, PositiveState z := fun z hz i => hε.trans_le (hz.1 i (Set.mem_univ i)).1
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn (continuous_massAction N κ).continuousOn
  have hspeed : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ t : ℝ, 0 ≤ t →
      ‖massAction N κ (x t)‖ ≤ |M| + 1 :=
    fun x hx t ht => (hM _ (hmemK x hx t ht)).trans (by linarith [le_abs_self M])
  -- Cluster points are equilibria (LaSalle step, Lemmas D and E).
  have hcl : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ z ∈ K, MapClusterPt z atTop x →
      massAction N κ z = 0 := by
    intro x hx z hzK hz
    have hD := hcb.dissip_eq_zero_of_mapClusterPt hκ hε hx (hbd x hx) (by positivity)
      (hspeed x hx) (hKpos z hzK) hz
    exact hcb.massAction_eq_zero_of_gap (hKpos z hzK)
      (hcb.gap_zero_of_dissip_eq_zero hκ (hKpos z hzK) hD)
  have hev : ∀ x, IsGlobalForwardSolution N κ x0 x → ∀ᶠ t in atTop, x t ∈ K :=
    fun x hx => eventually_atTop.mpr ⟨0, fun t ht => hmemK x hx t ht⟩
  obtain ⟨xbar, hbarK, hbar⟩ :=
    hK.exists_mapClusterPt (f := atTop) (u := x₁) (le_principal_iff.mpr (hev x₁ hx₁))
  have hbar_eq := hcl x₁ hx₁ xbar hbarK hbar
  -- Uniqueness of the positive equilibrium in the class.
  have huniq : ∀ z : Fin d → ℝ, PositiveState z → massAction N κ z = 0 → z - x0 ∈ S →
      z = xbar := fun z hz hfz hzS =>
    hcb.eq_of_equilibria hκ hz (hKpos _ hbarK) hfz hbar_eq
      (by simpa using S.sub_mem hzS hbarK.2)
  refine ⟨xbar, hKpos _ hbarK, hbar_eq, hbarK.2, huniq, ⟨x₁, hx₁⟩, fun x hx => ?_⟩
  exact hK.tendsto_nhds_of_unique_mapClusterPt (hev x hx) fun z hzK hz =>
    huniq z (hKpos z hzK) (hcl x hx z hzK hz) hzK.2

end GAC
