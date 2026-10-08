import LogarithmExtension.NormalizedJetIdeal
import OAI.NumberTheory.PiExponent.Jets.JetPowerIdealCoprime
import OAI.NumberTheory.PiExponent.Jets.AffineJetCoefficientInterface

/-!
# Simultaneous packets and the global-section interface

Chinese remaindering provides arbitrary packets without a degree bound.
The final theorem transfers global section surjectivity to packets, but does
not assume or assert that the required global restriction map is surjective.
-/

noncomputable section
namespace LogarithmExtension.JetPackets

open OAI OAI.PiExponent OAI.PiExponentApprox
open NormalizedJetIdeal
open scoped BigOperators

variable {m : ℕ}

theorem powerIdeal_pairwise_isCoprime {J : Type*}
    (y : J → ℂ) (c : J → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (G : Fin m → Polynomial ℂ) (hG : ∀ i, (G i).eval 0 = 0)
    (e : Fin (m+1) → ℕ) (he : ∀ i, 0 < e i) :
    Pairwise (fun i j => IsCoprime (powerIdeal (y i) (c i) G e) (powerIdeal (y j) (c j) G e)) := by
  intro i j hij
  have hp : IsCoprime (WeightedBezout.pointIdeal (center (y i) (c i)))
      (WeightedBezout.pointIdeal (center (y j) (c j))) := by
    apply Ideal.isCoprime_of_isMaximal
    intro heq
    exact hij (hcent (JetPowerIdealCoprime.pointIdeal_injective heq))
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply Ideal.radical_eq_top.mp
  rw [Ideal.radical_sup, radical_powerIdeal (y i) (c i) G hG e he,
    radical_powerIdeal (y j) (c j) G hG e he, hp.sup_eq, Ideal.radical_top]

theorem formalJet_packet_eq_of_sub_mem_pow
    (y : ℂ) (c : Fin m → ℂ) (T : Fin m → ℕ) (e : Fin (m+1) → ℕ)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 ≤ v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (P Q : FramePolynomial m)
    (hPQ : P - Q ∈ powerIdeal y c (CompactJetPolynomial.logPolynomials T) e ^ n) :
    JetGeometry.rationalCoefficientPacket v (n*R) (NormalizedLogJet.formalJet y c P) =
      JetGeometry.rationalCoefficientPacket v (n*R) (NormalizedLogJet.formalJet y c Q) := by
  apply (FormalLogTruncation.rationalCoefficientPacket_eq_iff v hv (n*R) _ _).mpr
  simpa only [map_sub] using formalJet_mem_weighted_of_mem_pow y c T e v hv hT R he n
    (P-Q) hPQ

/-- Simultaneous interpolation with NO weighted-degree claim. -/
theorem formalJet_packets_surjective {J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ) :
    Function.Surjective (fun P : FramePolynomial m => fun j =>
      JetGeometry.rationalCoefficientPacket v (n*R) (NormalizedLogJet.formalJet (y j) (c j) P)) := by
  classical
  intro packets
  choose P hP using fun j => formalJet_packet_surjective (y j) (hy j) (c j) v hv (n*R) (packets j)
  have hcop : Pairwise (fun i j => IsCoprime
      (powerIdeal (y i) (c i) (CompactJetPolynomial.logPolynomials T) e ^ n)
      (powerIdeal (y j) (c j) (CompactJetPolynomial.logPolynomials T) e ^ n)) := by
    intro i j hij
    exact (powerIdeal_pairwise_isCoprime y c hcent _
      (CompactJetPolynomial.logPolynomials_eval_zero T) e hepos hij).pow
  obtain ⟨Q, hQ⟩ := Ideal.exists_forall_sub_mem_ideal hcop P
  refine ⟨Q, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n Q (P j) (hQ j)).trans (hP j)

theorem packets_surjective_of_polynomialIdeal_quotient {α J : Type*} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (f : α → FramePolynomial m)
    (hf : Function.Surjective (fun a => Ideal.Quotient.mk (polynomialIdeal y c T e ^ n) (f a))) :
    Function.Surjective (fun a j =>
      JetGeometry.rationalCoefficientPacket v (n*R) (NormalizedLogJet.formalJet (y j) (c j) (f a))) := by
  intro packets
  obtain ⟨P, hP⟩ := formalJet_packets_surjective y hy c hcent T e hepos v hv hT R he n packets
  obtain ⟨a, ha⟩ := hf (Ideal.Quotient.mk _ P)
  have hdiff : f a - P ∈ polynomialIdeal y c T e ^ n := Ideal.Quotient.eq.mp ha
  refine ⟨a, ?_⟩
  funext j
  exact (formalJet_packet_eq_of_sub_mem_pow (y j) (c j) T e v (fun i => (hv i).le)
    hT R he n (f a) P (polynomialIdeal_pow_le y c T e n j hdiff)).trans (congrFun hP j)

open AlgebraicGeometry CategoryTheory
open PiExponentSeshadri.Geometry PiExponentSeshadri.IdealPullback
open AffineJetCoefficientInterface BlowupJetSurjectivity

/-- Global jet-restriction surjectivity implies simultaneous logarithmic
packets. Establishing `hjet` with a weighted degree bound remains necessary. -/
theorem surjective_of_jetRestriction {X : Scheme} {J : Type} [Fintype J]
    (y : J → ℂ) (hy : ∀ j, y j ≠ 0) (c : J → Fin m → ℂ)
    (hcent : Function.Injective (fun j => (Fin.cases (y j) (c j) : Fin (m+1) → ℂ)))
    (T : Fin m → ℕ) (e : Fin (m+1) → ℕ) (hepos : ∀ i, 0 < e i)
    (v : Fin (m+1) → ℚ) (hv : ∀ i, 0 < v i)
    (hT : ∀ i, v i.succ ≤ (T i : ℚ) * v 0)
    (R : ℚ) (he : ∀ i, R ≤ (e i : ℚ) * v i) (n : ℕ)
    (j : Spec (CommRingCat.of (FramePolynomial m)) ⟶ X) [IsOpenImmersion j]
    (I : X.IdealSheafData) (A : LineBundle X) (frame : Frame j A)
    (hI : I.comap j = specIdeal (polynomialIdeal y c T e))
    (hs : ((I^n).support : Set X) ⊆ j.opensRange)
    (hjet : Function.Surjective (jetRestriction I A n)) :
    Function.Surjective (fun s : Sections A n => fun k =>
      JetGeometry.rationalCoefficientPacket v (n*R)
        (NormalizedLogJet.formalJet (y k) (c k) (coefficient j A n frame s))) := by
  apply packets_surjective_of_polynomialIdeal_quotient y hy c hcent T e hepos
    v hv hT R he n (coefficient j A n frame)
  exact AffineJetPolynomial.polynomialQuotient_surjective_of_jetRestriction
    I A n j frame (polynomialIdeal y c T e) hI hs hjet

#print axioms formalJet_packets_surjective
#print axioms surjective_of_jetRestriction

end LogarithmExtension.JetPackets
