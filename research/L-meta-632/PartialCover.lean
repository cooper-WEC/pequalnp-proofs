import Mathlib.Data.Fintype.BigOperators
import PEqualNP.Defs.AndCountCircuit

namespace PartialCover632

open PEqualNP.AndCount PEqualNP.AndCount.AndCountCircuit

-- Fuel stability and monotonicity from the project proof of L-meta-562.
private lemma sideTrue_congr {n k : ℕ} (U B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (h : ∀ j, j < i → v1 j = v2 j) :
    sideTrue U B F i v1 = sideTrue U B F i v2 := by
  unfold sideTrue
  refine decide_eq_decide.mpr ?_
  constructor
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [← h j hji]⟩
  · rintro (hv | ⟨j, hjF, hji, hvj⟩)
    · exact Or.inl hv
    · exact Or.inr ⟨j, hjF, hji, by rwa [h j hji]⟩

private lemma gateValFuel_indep {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n)) :
    ∀ (m : ℕ) (i : Fin C.size), i.val < m →
      ∀ (d1 d2 : ℕ), i.val < d1 → i.val < d2 →
        C.gateValFuel U d1 i = C.gateValFuel U d2 i := by
  intro m
  induction m with
  | zero =>
    intro i hi
    exact absurd hi (Nat.not_lt_zero _)
  | succ m ih =>
    intro i hi d1 d2 hd1 hd2
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d1 ≠ 0) with ⟨k1, rfl⟩
    rcases Nat.exists_eq_succ_of_ne_zero (by omega : d2 ≠ 0) with ⟨k2, rfl⟩
    simp only [gateValFuel]
    have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U k1 j = C.gateValFuel U k2 j := by
      intro j hji
      exact ih j (by omega) k1 k2 (by omega) (by omega)
    rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
        sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma gateVal_unfold {n : ℕ} (C : AndCountCircuit n) (U : Finset (Fin n))
    (i : Fin C.size) :
    C.gateVal U i =
      (sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U) &&
       sideTrue U (C.rightVars i) (C.rightGates i) i (C.gateVal U)) := by
  have heq : C.gateVal U i = C.gateValFuel U (i.val + 1) i :=
    gateValFuel_indep C U C.size i i.isLt C.size (i.val + 1) i.isLt (Nat.lt_succ_self _)
  rw [heq]
  simp only [gateValFuel]
  have hlt : ∀ j : Fin C.size, j < i → C.gateValFuel U i.val j = C.gateVal U j := by
    intro j hji
    exact gateValFuel_indep C U C.size j j.isLt i.val C.size hji j.isLt
  rw [sideTrue_congr U (C.leftVars i) (C.leftGates i) i _ _ hlt,
      sideTrue_congr U (C.rightVars i) (C.rightGates i) i _ _ hlt]

private lemma sideTrue_mono_U {n k : ℕ} {U V : Finset (Fin n)} (hUV : U ⊆ V)
    (B : Finset (Fin n)) (F : Finset (Fin k)) (i : Fin k)
    (v1 v2 : Fin k → Bool) (hv : ∀ j, j < i → v1 j = true → v2 j = true)
    (hs : sideTrue U B F i v1 = true) :
    sideTrue V B F i v2 = true := by
  unfold sideTrue at hs ⊢
  rw [decide_eq_true_eq] at hs ⊢
  rcases hs with ⟨v, hvB, hvU⟩ | ⟨j, hjF, hji, hvj⟩
  · exact Or.inl ⟨v, hvB, hUV hvU⟩
  · exact Or.inr ⟨j, hjF, hji, hv j hji hvj⟩

private lemma gateValFuel_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) :
    ∀ (d : ℕ) (i : Fin C.size), C.gateValFuel U d i = true → C.gateValFuel V d i = true := by
  intro d
  induction d with
  | zero =>
    intro i hi
    simp [gateValFuel] at hi
  | succ d ih =>
    intro i hi
    simp only [gateValFuel, Bool.and_eq_true] at hi ⊢
    exact ⟨sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.1,
           sideTrue_mono_U hUV _ _ _ _ _ (fun j _ hj => ih j hj) hi.2⟩

private lemma gateVal_mono_U {n : ℕ} (C : AndCountCircuit n) {U V : Finset (Fin n)}
    (hUV : U ⊆ V) (i : Fin C.size) (h : C.gateVal U i = true) : C.gateVal V i = true :=
  gateValFuel_mono_U C hUV C.size i h

variable {n : ℕ}

def MaxIndependent (G : SimpleGraph (Fin n)) (I : Finset (Fin n)) : Prop :=
  (∀ v ∈ I, ∀ w ∈ I, ¬ G.Adj v w) ∧ (∀ u, u ∉ I → ∃ v ∈ I, G.Adj u v)

def Passes (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) : Prop :=
  ∀ I, MaxIndependent G I → C.eval I = false ∧ ∀ u, u ∉ I → C.eval (insert u I) = true

def Cover (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ v w, G.Adj v w → v ∈ T ∨ w ∈ T

private lemma empty_side {k : ℕ} (U B : Finset (Fin n)) (i : Fin k) (f : Fin k → Bool) :
    sideTrue U B ∅ i f = true ↔ ∃ v ∈ B, v ∈ U := by simp [sideTrue]

private lemma star_gate (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T U : Finset (Fin n)) (j : Fin T.card) :
    (starCircuit G T).gateVal U j = true ↔ T.orderEmbOfFin rfl j ∈ U ∧
      ∃ w ∈ U, G.Adj (T.orderEmbOfFin rfl j) w := by
  rw [gateVal_unfold (starCircuit G T) U j, Bool.and_eq_true]
  let f : Fin T.card → Bool := (starCircuit G T).gateVal U
  change (sideTrue U {T.orderEmbOfFin rfl j} ∅ j f = true ∧
    sideTrue U (Finset.univ.filter (fun w => G.Adj (T.orderEmbOfFin rfl j) w)) ∅ j f = true) ↔ _
  rw [empty_side, empty_side]
  simp only [Finset.mem_singleton, exists_eq_left, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_congr_right fun _ => exists_congr fun _ => and_comm

private lemma star_eval (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (T U : Finset (Fin n)) :
    (starCircuit G T).eval U = true ↔ ∃ v ∈ T, v ∈ U ∧ ∃ w ∈ U, G.Adj v w := by
  rw [AndCountCircuit.eval, decide_eq_true_eq]
  change ((∃ v ∈ (∅ : Finset (Fin n)), v ∈ U) ∨ ∃ j ∈ Finset.univ, (starCircuit G T).gateVal U j = true) ↔ _
  simp only [Finset.notMem_empty, false_and, exists_false, false_or, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨_,T.orderEmbOfFin_mem rfl j,(star_gate G T U j).mp hj⟩
  · rintro ⟨v, hv, hU, w, hw, he⟩
    have hr : v ∈ Set.range (T.orderEmbOfFin rfl) := by simpa using hv
    obtain ⟨j, rfl⟩ := hr
    exact ⟨j,(star_gate G T U j).mpr ⟨hU,w,hw,he⟩⟩

theorem upper (G : SimpleGraph (Fin n)) :
    ∃ C : AndCountCircuit n, C.WellFormed ∧ Passes C G ∧
      ∀ T, Cover G T → C.size ≤ T.card := by
  classical
  have covers : ∃ k : ℕ, ∃ T : Finset (Fin n), Cover G T ∧ T.card = k :=
    ⟨_, Finset.univ, fun v _ _ => Or.inl (Finset.mem_univ v), rfl⟩
  obtain ⟨T,hT,hk⟩ := Nat.find_spec covers
  refine ⟨starCircuit G T, by intro i; constructor <;> intro j hj <;> exact False.elim (Finset.notMem_empty _ hj), ?_, ?_⟩
  · intro I hI
    constructor
    · apply Bool.eq_false_iff.mpr
      rintro he
      obtain ⟨v,_,hv,w,hw,hvw⟩ := (star_eval G T I).mp he
      exact hI.1 v hv w hw hvw
    · intro u hu
      obtain ⟨v,hv,he⟩ := hI.2 u hu
      apply (star_eval G T _).mpr
      rcases hT u v he with ht|ht
      · exact ⟨u,ht,Finset.mem_insert_self ..,v,Finset.mem_insert_of_mem hv,he⟩
      · exact ⟨v,ht,Finset.mem_insert_of_mem hv,u,Finset.mem_insert_self ..,he.symm⟩
  · intro S hS
    change T.card ≤ S.card
    rw [hk]
    exact Nat.find_min' covers ⟨S,hS,rfl⟩

private def code (C : AndCountCircuit n) (U : Finset (Fin n)) (i : Fin C.size) : Bool :=
  sideTrue U (C.leftVars i) (C.leftGates i) i (C.gateVal U)

private lemma split_side (C : AndCountCircuit n) (U V : Finset (Fin n))
    (B : Finset (Fin n)) (F : Finset (Fin C.size)) (i : Fin C.size)
    (ih : ∀ j < i, C.gateVal (U ∪ V) j = true →
      C.gateVal U j = true ∨ C.gateVal V j = true) :
    sideTrue (U ∪ V) B F i (C.gateVal (U ∪ V)) = true →
      sideTrue U B F i (C.gateVal U) = true ∨ sideTrue V B F i (C.gateVal V) = true := by
  simp only [sideTrue, decide_eq_true_eq]
  rintro (⟨v,hv,hm⟩ | ⟨j,hj,hl,ht⟩)
  · rcases Finset.mem_union.mp hm with h|h
    · exact Or.inl (Or.inl ⟨v,hv,h⟩)
    · exact Or.inr (Or.inl ⟨v,hv,h⟩)
  · rcases ih j hl ht with h|h
    · exact Or.inl (Or.inr ⟨j,hj,hl,h⟩)
    · exact Or.inr (Or.inr ⟨j,hj,hl,h⟩)

private lemma split_gate (C : AndCountCircuit n) (U V : Finset (Fin n))
    (same : code C U = code C V) (i : Fin C.size) :
    C.gateVal (U ∪ V) i = true → C.gateVal U i = true ∨ C.gateVal V i = true := by
  induction i using Fin.strong_induction_on with
  | h i ih =>
    rw [gateVal_unfold C (U ∪ V), gateVal_unfold C U, gateVal_unfold C V]
    simp only [Bool.and_eq_true]
    rintro ⟨hl,hr⟩
    have hl' := split_side C U V _ _ i ih hl
    have eq := congrFun same i
    unfold code at eq
    rw [← eq] at hl'
    have left := hl'.elim id id
    rcases split_side C U V _ _ i ih hr with h|h
    · exact Or.inl ⟨left,h⟩
    · exact Or.inr ⟨eq ▸ left,h⟩

private lemma eval_mono (C : AndCountCircuit n) {U V : Finset (Fin n)} (h : U ⊆ V)
    (he : C.eval U = true) : C.eval V = true := by
  simp only [eval, decide_eq_true_eq] at he ⊢
  rcases he with ⟨v,hv,hu⟩|⟨i,hi,hu⟩
  · exact Or.inl ⟨v,hv,h hu⟩
  · exact Or.inr ⟨i,hi,gateVal_mono_U C h i hu⟩

theorem counting_bound (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (hC : Passes C G)
    (family : Finset (Finset (Fin n))) (hf : ∀ I ∈ family, MaxIndependent G I) :
    family.card ≤ 2 ^ C.size := by
  classical
  have inj : Function.Injective (fun I : ↥family => code C I.val) := by
    intro I J same
    have noUnion : C.eval (I.val ∪ J.val) ≠ true := by
      intro hu
      rw [AndCountCircuit.eval, decide_eq_true_eq] at hu
      have noI := (hC I.val (hf I.val I.property)).1
      have noJ := (hC J.val (hf J.val J.property)).1
      simp only [eval, decide_eq_false_iff_not] at noI noJ
      rcases hu with ⟨v,hv,hm⟩ | ⟨i,hi,hg⟩
      · rcases Finset.mem_union.mp hm with h|h
        · exact noI (Or.inl ⟨v,hv,h⟩)
        · exact noJ (Or.inl ⟨v,hv,h⟩)
      · rcases split_gate C I.val J.val same i hg with h|h
        · exact noI (Or.inr ⟨i,hi,h⟩)
        · exact noJ (Or.inr ⟨i,hi,h⟩)
    apply Subtype.ext
    ext v
    constructor
    · intro h
      by_contra hn
      exact noUnion (eval_mono C (Finset.insert_subset (Finset.mem_union_left _ h)
        Finset.subset_union_right) ((hC _ (hf _ J.property)).2 v hn))
    · intro h
      by_contra hn
      exact noUnion (eval_mono C (Finset.insert_subset (Finset.mem_union_right _ h)
        Finset.subset_union_left) ((hC _ (hf _ I.property)).2 v hn))
  simpa using Fintype.card_le_of_injective _ inj

end PartialCover632

namespace PartialCover632

open PEqualNP.AndCount

def matching (m : ℕ) : SimpleGraph (Fin (2 * m)) where
  Adj v w := v.val / 2 = w.val / 2 ∧ v ≠ w
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.2 rfl⟩

private def endpoint {m : ℕ} (i : Fin m) (b : Bool) : Fin (2 * m) :=
  ⟨2 * i.val + b.toNat, by cases b <;> simp; omega⟩

private lemma pairIndex {m : ℕ} (i : Fin m) (b : Bool) :
    (endpoint i b).val / 2 = i.val := by
  cases b <;> simp [endpoint]
  omega

private lemma endpoint_inj {m : ℕ} {i j : Fin m} {a b : Bool}
    (h : endpoint i a = endpoint j b) : i = j ∧ a = b := by
  have h1 := congrArg (fun v : Fin (2*m) => v.val / 2) h
  simp only [pairIndex] at h1
  have e : i = j := Fin.ext h1
  subst j
  refine ⟨rfl, ?_⟩
  have h2 := congrArg Fin.val h
  cases a <;> cases b <;> simp_all [endpoint, Bool.toNat]

private lemma some_endpoint {m : ℕ} (v : Fin (2*m)) :
    ∃ (i : Fin m) (b : Bool), v = endpoint i b := by
  refine ⟨⟨v.val / 2, by omega⟩, decide (v.val % 2 = 1), Fin.ext ?_⟩
  by_cases h : v.val % 2 = 1 <;> simp [endpoint,h,Bool.toNat] <;> omega

private def selection {m : ℕ} (b : Fin m → Bool) : Finset (Fin (2*m)) :=
  Finset.univ.image (fun i => endpoint i (b i))

private lemma in_selection {m : ℕ} (b : Fin m → Bool) (i : Fin m) (a : Bool) :
    endpoint i a ∈ selection b ↔ b i = a := by
  constructor
  · intro h
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp h
    obtain ⟨rfl,eq⟩ := endpoint_inj he
    exact eq
  · rintro rfl
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

private lemma selection_max {m : ℕ} (b : Fin m → Bool) :
    MaxIndependent (matching m) (selection b) := by
  constructor
  · intro v hv w hw he
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
    have eq : i = j := Fin.ext (by simpa only [pairIndex] using he.1)
    subst j
    exact he.2 rfl
  · intro v hv
    obtain ⟨i,a,rfl⟩ := some_endpoint v
    refine ⟨endpoint i (b i), (in_selection b i _).mpr rfl, ?_⟩
    exact ⟨by simp only [pairIndex], fun eq => hv (eq ▸ (in_selection b i _).mpr rfl)⟩

theorem matching_lower (m : ℕ) (C : AndCountCircuit (2*m)) (h : Passes C (matching m)) :
    m ≤ C.size := by
  classical
  let family := Finset.univ.image (@selection m)
  have bound := counting_bound C (matching m) h family (by
    intro I hI
    obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hI
    exact selection_max b)
  have hinj : Function.Injective (@selection m) := by
    intro b c he
    funext i
    have hm := (in_selection b i _).mpr rfl
    rw [he] at hm
    exact ((in_selection c i _).mp hm).symm
  have card : family.card = 2^m := by
    simp [family,Finset.card_image_of_injective _ hinj]
  rw [card] at bound
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp bound

private lemma matching_cover (m : ℕ) : Cover (matching m) (selection (fun _ => false)) := by
  intro v w he
  obtain ⟨i,a,rfl⟩ := some_endpoint v
  obtain ⟨j,b,rfl⟩ := some_endpoint w
  have eq : i = j := Fin.ext (by simpa only [pairIndex] using he.1)
  subst j
  cases a <;> cases b <;> simp only [in_selection, true_or, or_true, or_self]
  exact False.elim (he.2 rfl)

theorem matching_exact (m : ℕ) :
    (∃ C : AndCountCircuit (2*m), C.WellFormed ∧ Passes C (matching m) ∧ C.size = m) ∧
    (∀ C : AndCountCircuit (2*m), Passes C (matching m) → m ≤ C.size) := by
  refine ⟨?_,matching_lower m⟩
  obtain ⟨C,wf,h,bound⟩ := upper (matching m)
  refine ⟨C,wf,h,Nat.le_antisymm ?_ (matching_lower m C h)⟩
  exact (bound _ (matching_cover m)).trans (by
    simpa only [selection,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_image_le (f := fun i : Fin m => endpoint i false)
        (s := (Finset.univ : Finset (Fin m)))))

theorem lower_of_many (C : AndCountCircuit n) (G : SimpleGraph (Fin n)) (h : Passes C G)
    (k : ℕ) (family : Finset (Finset (Fin n))) (hf : ∀ I ∈ family, MaxIndependent G I)
    (many : 2^k < family.card) : k+1 ≤ C.size := by
  by_contra! hsmall
  have hk : C.size ≤ k := by omega
  have := (counting_bound C G h family hf).trans (Nat.pow_le_pow_right (by decide) hk)
  omega

end PartialCover632

namespace PartialCover632

open PEqualNP.AndCount

def windmill (m : ℕ) : SimpleGraph (Fin (2*m+1)) where
  Adj u v := u ≠ v ∧ (u = 0 ∨ v = 0 ∨
    ∃ a b : Fin (2*m), u = a.succ ∧ v = b.succ ∧ (matching m).Adj a b)
  symm := ⟨by
    intro u v h
    refine ⟨h.1.symm,?_⟩
    rcases h.2 with h|h|⟨a,b,ha,hb,he⟩
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨b,a,hb,ha,he.symm⟩)⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

private lemma rim_adj {m : ℕ} {a b : Fin (2*m)} :
    (windmill m).Adj a.succ b.succ ↔ (matching m).Adj a b := by
  constructor
  · rintro ⟨_,h⟩
    rcases h with h|h|⟨v,w,hv,hw,he⟩
    · exact False.elim (Fin.succ_ne_zero a h)
    · exact False.elim (Fin.succ_ne_zero b h)
    · simpa only [← Fin.succ_inj.mp hv, ← Fin.succ_inj.mp hw] using he
  · intro h
    exact ⟨fun e => h.ne (Fin.succ_inj.mp e), Or.inr (Or.inr ⟨a,b,rfl,rfl,h⟩)⟩

private def rim {m : ℕ} (b : Fin m → Bool) : Finset (Fin (2*m+1)) :=
  (selection b).map (Fin.succEmb _)

private lemma hub_free {m : ℕ} (b : Fin m → Bool) : 0 ∉ rim b := by
  simp [rim,Finset.mem_map]

private lemma mem_rim {m : ℕ} (b : Fin m → Bool) (a : Fin (2*m)) :
    a.succ ∈ rim b ↔ a ∈ selection b := by simp [rim,Finset.mem_map]

private lemma rim_max {m : ℕ} (hm : 0 < m) (b : Fin m → Bool) : MaxIndependent (windmill m) (rim b) := by
  have H := selection_max b
  constructor
  · intro v hv w hw he
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hw
    exact H.1 v ((mem_rim b v).mp hv) w ((mem_rim b w).mp hw) (rim_adj.mp he)
  · intro u
    refine Fin.cases ?_ (fun v => ?_) u
    · intro _
      let i : Fin m := ⟨0,hm⟩
      let v := endpoint i (b i)
      exact ⟨v.succ,(mem_rim b v).mpr ((in_selection b i _).mpr rfl),
        (Fin.succ_ne_zero v).symm,Or.inl rfl⟩
    · intro hn
      obtain ⟨w,hw,he⟩ := H.2 v (fun h => hn ((mem_rim b v).mpr h))
      exact ⟨w.succ,(mem_rim b w).mpr hw,rim_adj.mpr he⟩

private lemma hub_max (m : ℕ) : MaxIndependent (windmill m) {0} := by
  constructor
  · intro v hv w hw he
    exact he.ne ((Finset.mem_singleton.mp hv).trans (Finset.mem_singleton.mp hw).symm)
  · intro v hv
    exact ⟨0,Finset.mem_singleton_self _,fun h => hv (Finset.mem_singleton.mpr h),Or.inr (Or.inl rfl)⟩

theorem windmill_exact (m : ℕ) (hm : 0 < m) :
    (∃ C : AndCountCircuit (2*m+1), C.WellFormed ∧ Passes C (windmill m) ∧ C.size = m+1) ∧
    ∀ C : AndCountCircuit (2*m+1), Passes C (windmill m) → m+1 ≤ C.size := by
  classical
  let rims := Finset.univ.image (@rim m)
  have miss : ({0} : Finset (Fin (2*m+1))) ∉ rims := by
    intro h
    obtain ⟨b,_,eq⟩ := Finset.mem_image.mp h
    exact hub_free b (eq ▸ Finset.mem_singleton_self 0)
  have inj : Function.Injective (@rim m) := by
    intro b c eq
    funext i
    have h := (mem_rim b _).mpr ((in_selection b i _).mpr rfl)
    rw [eq] at h
    exact ((in_selection c i _).mp ((mem_rim c _).mp h)).symm
  have lower (C : AndCountCircuit (2*m+1)) (h : Passes C (windmill m)) : m+1 ≤ C.size := by
    apply lower_of_many C _ h m (insert {0} rims)
    · intro I hi
      rcases Finset.mem_insert.mp hi with rfl|hr
      · exact hub_max m
      · obtain ⟨b,_,rfl⟩ := Finset.mem_image.mp hr
        exact rim_max hm b
    · rw [Finset.card_insert_of_notMem miss]
      simp [rims,Finset.card_image_of_injective _ inj]
  refine ⟨?_,lower⟩
  obtain ⟨C,wf,h,bound⟩ := upper (windmill m)
  refine ⟨C,wf,h,Nat.le_antisymm ?_ (lower C h)⟩
  let b : Fin m → Bool := fun _ => false
  have cov : Cover (windmill m) (insert 0 (rim b)) := by
    intro v w he
    rcases he.2 with rfl|rfl|⟨a,d,rfl,rfl,hadj⟩
    · exact Or.inl (Finset.mem_insert_self ..)
    · exact Or.inr (Finset.mem_insert_self ..)
    · rcases matching_cover m a d hadj with h|h
      · exact Or.inl (Finset.mem_insert_of_mem ((mem_rim b a).mpr h))
      · exact Or.inr (Finset.mem_insert_of_mem ((mem_rim b d).mpr h))
  refine (bound _ cov).trans ?_
  rw [Finset.card_insert_of_notMem (hub_free b)]
  simp only [rim,Finset.card_map]
  apply Nat.add_le_add_right
  simpa only [selection,Finset.card_univ,Fintype.card_fin] using
    (Finset.card_image_le (f := fun i : Fin m => endpoint i (b i))
        (s := (Finset.univ : Finset (Fin m))))

end PartialCover632
