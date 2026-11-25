import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6130_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

-- The proof works on 8 of the 16 rows: (0,3) (1,3) (2,1) (2,2) (2,3) (3,0) (3,2) (3,3).
-- A wire is an 8 bit mask, bit q its value on row q. The graph is 47 on these rows.

def stepC (pool : List ℕ) : List ℕ :=
  255 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

theorem mem_stepC (P : List ℕ) (x : ℕ) :
    x ∈ stepC P ↔ x = 255 ∨ x = 0 ∨ x ∈ P ∨ ∃ a ∈ P, ∃ b ∈ P, x = a &&& b ∨ x = a ||| b := by
  simp [stepC]

theorem stepC_mono {P Q : List ℕ} (h : ∀ y ∈ P, y ∈ Q) {x : ℕ} (hx : x ∈ stepC P) :
    x ∈ stepC Q := by
  rw [mem_stepC] at hx ⊢
  rcases hx with h1 | h1 | h1 | ⟨a, ha, b, hb, h1⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl h1)
  · exact Or.inr (Or.inr (Or.inl (h _ h1)))
  · exact Or.inr (Or.inr (Or.inr ⟨a, h _ ha, b, h _ hb, h1⟩))

theorem self_mem_stepC {P : List ℕ} {x : ℕ} (hx : x ∈ P) : x ∈ stepC P :=
  (mem_stepC P x).2 (Or.inr (Or.inr (Or.inl hx)))

theorem stepC_lt {P : List ℕ} (hP : ∀ y ∈ P, y < 256) {x : ℕ} (hx : x ∈ stepC P) : x < 256 := by
  rw [mem_stepC] at hx
  rcases hx with rfl | rfl | h1 | ⟨a, ha, b, hb, rfl | rfl⟩
  · norm_num
  · norm_num
  · exact hP _ h1
  · exact Nat.and_lt_two_pow a (n := 8) (hP _ hb)
  · exact Nat.or_lt_two_pow (n := 8) (hP _ ha) (hP _ hb)

-- circuits to chains of masks

def Inv (pool : List ℕ) (ws : Fin 8 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 8, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem testBit_255 : ∀ p : Fin 8, (255 : ℕ).testBit p = true := by decide

theorem gate_vec (pool : List ℕ) (ws : Fin 8 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ stepC pool, ∀ p : Fin 8,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨255, by simp [stepC], fun p => by simp [GateOp.eval, testBit_255 p]⟩
    · exact ⟨0, by simp [stepC], fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    refine ⟨ma, by simp [stepC, hma], fun p => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval, ha p]
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    obtain ⟨mb, hmb, hb⟩ := h b
    rcases hop with rfl | rfl
    · refine ⟨ma &&& mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem inv_step (pool pool' : List ℕ) (ws : Fin 8 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 8 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 8, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  intro i
  obtain ⟨m, hm, hmb⟩ := hI i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

def Chain : List ℕ → List ℕ → Prop
  | _, [] => True
  | P, c :: L => c ∈ stepC P ∧ Chain (P ++ [c]) L

theorem to_chain : ∀ (gs : List Gate) (pool : List ℕ) (ws : Fin 8 → List Bool) (L o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    (∀ p, (ws p).length = L) → Inv pool ws →
    ∃ Lc : List ℕ, Lc.length = gs.length ∧ Chain pool Lc ∧ ∃ m ∈ pool ++ Lc, ∀ p : Fin 8,
      m.testBit p = (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p)).getD o false
  | [], pool, ws, L, o, _, _, hI => by
    obtain ⟨m, hm, hmb⟩ := hI o
    exact ⟨[], rfl, trivial, m, by simpa using hm, fun p => by simpa using hmb p⟩
  | g :: gs, pool, ws, L, o, hg, hL, hI => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hI' := inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp)
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 := fun p => by simp [hL p]
    obtain ⟨Lc, hlen', hch, m, hm, hmb⟩ :=
      to_chain gs (pool ++ [c]) _ (L + 1) o (fun g' hg' => hg g' (by simp [hg'])) hL' hI'
    refine ⟨c :: Lc, by simp [hlen'], ⟨hc, hch⟩, m, by simpa using hm, fun p => ?_⟩
    rw [List.foldl_cons]
    exact hmb p

-- chains: monotone, bounded, and the first new value is one gate away

theorem chain_mono : ∀ (L P Q : List ℕ), (∀ y ∈ P, y ∈ Q) → Chain P L → Chain Q L
  | [], _, _, _, _ => trivial
  | c :: L, P, Q, h, hch => ⟨stepC_mono h hch.1, chain_mono L (P ++ [c]) (Q ++ [c])
      (fun y hy => by
        rcases List.mem_append.mp hy with hy | hy
        · exact List.mem_append_left _ (h y hy)
        · exact List.mem_append_right _ hy) hch.2⟩

theorem chain_lt : ∀ (L P : List ℕ), (∀ y ∈ P, y < 256) → Chain P L → ∀ x ∈ L, x < 256
  | [], _, _, _ => by simp
  | c :: L, P, hP, hch => by
    have hc' := stepC_lt hP hch.1
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc'
    · refine chain_lt L (P ++ [c]) (fun y hy => ?_) hch.2 x hx
      rcases List.mem_append.mp hy with hy | hy
      · exact hP y hy
      · rw [List.mem_singleton.mp hy]; exact hc'

theorem first_new : ∀ (L P : List ℕ), Chain P L → (∃ x ∈ L, x ∉ P) →
    ∃ x ∈ L, x ∉ P ∧ x ∈ stepC P
  | [], _, _, ⟨x, hx, _⟩ => by simp at hx
  | c :: L, P, hch, ⟨x, hx, hxP⟩ => by
    by_cases hcP : c ∈ P
    · have hx' : x ∈ L := by
        rcases List.mem_cons.mp hx with rfl | hx
        · exact absurd hcP hxP
        · exact hx
      have hxc : x ∉ P ++ [c] := by
        intro h
        rcases List.mem_append.mp h with h | h
        · exact hxP h
        · rw [List.mem_singleton.mp h] at hxP; exact hxP hcP
      obtain ⟨y, hy, hyP, hys⟩ := first_new L (P ++ [c]) hch.2 ⟨x, hx', hxc⟩
      refine ⟨y, List.mem_cons_of_mem _ hy, fun h => hyP (List.mem_append_left _ h), ?_⟩
      refine stepC_mono (fun z hz => ?_) hys
      rcases List.mem_append.mp hz with hz | hz
      · exact hz
      · rw [List.mem_singleton.mp hz]; exact hcP
    · exact ⟨c, by simp, hcP, hch.1⟩

-- the number of values of a chain not yet in the pool

def mu (P L : List ℕ) : ℕ := L.countP (fun x => decide (x ∉ P))

theorem mu_zero {P L : List ℕ} (h : mu P L = 0) : ∀ x ∈ L, x ∈ P := by
  intro x hx
  by_contra hxP
  have : 0 < mu P L := List.countP_pos_iff.mpr ⟨x, hx, by simpa using hxP⟩
  omega

theorem mu_two {P L : List ℕ} {x y : ℕ} (hx : x ∈ L) (hy : y ∈ L) (hxP : x ∉ P) (hyP : y ∉ P)
    (hxy : x ≠ y) : 2 ≤ mu P L := by
  unfold mu
  rw [List.countP_eq_length_filter]
  have hx' : x ∈ L.filter (fun x => decide (x ∉ P)) := List.mem_filter.mpr ⟨hx, by simpa using hxP⟩
  have hy' : y ∈ L.filter (fun x => decide (x ∉ P)) := List.mem_filter.mpr ⟨hy, by simpa using hyP⟩
  generalize L.filter (fun x => decide (x ∉ P)) = l at hx' hy'
  match l, hx', hy' with
  | [], hx', _ => simp at hx'
  | [a], hx', hy' =>
    simp only [List.mem_singleton] at hx' hy'
    exact absurd (hx'.trans hy'.symm) hxy
  | _ :: _ :: _, _, _ => simp

theorem mu_mono (P Q L : List ℕ) (h : ∀ y ∈ P, y ∈ Q) : mu Q L ≤ mu P L := by
  unfold mu
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq] at hx ⊢
  exact fun hp => hx (h x hp)

theorem mu_snoc : ∀ (L P : List ℕ) (c : ℕ), c ∈ L → c ∉ P → mu (P ++ [c]) L + 1 ≤ mu P L
  | [], _, _, h, _ => by simp at h
  | a :: L, P, c, h, hcP => by
    have hm := mu_mono P (P ++ [c]) L (fun y hy => List.mem_append_left _ hy)
    unfold mu at hm ⊢
    rw [List.countP_cons, List.countP_cons]
    by_cases hac : a = c
    · subst hac
      have h1 : decide (a ∉ P ++ [a]) = false := by simp
      have h2 : decide (a ∉ P) = true := by simp [hcP]
      rw [h1, h2]
      simp only [Bool.false_eq_true, if_false, if_true]
      omega
    · have hcL : c ∈ L := by
        rcases List.mem_cons.mp h with h | h
        · exact absurd h.symm hac
        · exact h
      have IH := mu_snoc L P c hcL hcP
      unfold mu at IH
      by_cases haP : a ∈ P
      · have h1 : decide (a ∉ P ++ [c]) = false := by simp [haP]
        have h2 : decide (a ∉ P) = false := by simp [haP]
        rw [h1, h2]
        simp only [Bool.false_eq_true, if_false]
        omega
      · have h1 : decide (a ∉ P ++ [c]) = true := by simp [haP, hac]
        have h2 : decide (a ∉ P) = true := by simp [haP]
        rw [h1, h2]
        simp only [if_true]
        omega

theorem obt_of_mu1 (P L : List ℕ) (T : ℕ) (hch : Chain P L) (hT : T ∈ P ++ L)
    (hmu : mu P L ≤ 1) : T ∈ stepC P := by
  by_cases hTP : T ∈ P
  · exact self_mem_stepC hTP
  · have hTL : T ∈ L := by
      rcases List.mem_append.mp hT with h | h
      · exact absurd h hTP
      · exact h
    obtain ⟨x, hx, hxP, hxs⟩ := first_new L P hch ⟨T, hTL, hTP⟩
    by_cases hxT : x = T
    · exact hxT ▸ hxs
    · have := mu_two hx hTL hxP hTP hxT
      omega

-- bit sets of masks

theorem testBit_shl (a x : ℕ) : (1 <<< a).testBit x = decide (a = x) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

def ext (c : ℕ) (Q : List ℕ) (s : ℕ) : ℕ :=
  Q.foldl (fun s y => s ||| (1 <<< (c &&& y)) ||| (1 <<< (c ||| y))) s

theorem ext_testBit (c x : ℕ) : ∀ (Q : List ℕ) (s : ℕ),
    (ext c Q s).testBit x = true ↔ s.testBit x = true ∨ ∃ y ∈ Q, x = c &&& y ∨ x = c ||| y
  | [], s => by simp [ext]
  | y :: Q, s => by
    have IH := ext_testBit c x Q (s ||| (1 <<< (c &&& y)) ||| (1 <<< (c ||| y)))
    unfold ext at IH ⊢
    rw [List.foldl_cons, IH]
    simp only [Nat.testBit_or, testBit_shl, Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (((h | h) | h) | ⟨z, hz, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨y, Or.inl rfl, Or.inl h.symm⟩
      · exact Or.inr ⟨y, Or.inl rfl, Or.inr h.symm⟩
      · exact Or.inr ⟨z, Or.inr hz, h⟩
    · rintro (h | ⟨z, rfl | hz, h⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · rcases h with h | h
        · exact Or.inl (Or.inl (Or.inr h.symm))
        · exact Or.inl (Or.inr h.symm)
      · exact Or.inr ⟨z, hz, h⟩

def obOf (P : List ℕ) : ℕ := P.foldl (fun s a => ext a P (s ||| (1 <<< a))) ((1 <<< 255) ||| (1 <<< 0))

theorem obOf_fold (P : List ℕ) (x : ℕ) : ∀ (R : List ℕ) (s : ℕ),
    (R.foldl (fun s a => ext a P (s ||| (1 <<< a))) s).testBit x = true ↔
      s.testBit x = true ∨ ∃ a ∈ R, x = a ∨ ∃ y ∈ P, x = a &&& y ∨ x = a ||| y
  | [], s => by simp
  | a :: R, s => by
    rw [List.foldl_cons, obOf_fold P x R, ext_testBit, Nat.testBit_or, testBit_shl]
    simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
    constructor
    · rintro (((h | h) | h) | ⟨b, hb, h⟩)
      · exact Or.inl h
      · exact Or.inr ⟨a, Or.inl rfl, Or.inl h.symm⟩
      · exact Or.inr ⟨a, Or.inl rfl, Or.inr h⟩
      · exact Or.inr ⟨b, Or.inr hb, h⟩
    · rintro (h | ⟨b, rfl | hb, h⟩)
      · exact Or.inl (Or.inl (Or.inl h))
      · rcases h with h | h
        · exact Or.inl (Or.inl (Or.inr h.symm))
        · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨b, hb, h⟩

theorem obOf_testBit (P : List ℕ) (x : ℕ) : (obOf P).testBit x = true ↔ x ∈ stepC P := by
  unfold obOf
  rw [obOf_fold, mem_stepC, Nat.testBit_or, testBit_shl, testBit_shl]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · rintro ((h | h) | ⟨a, ha, h | ⟨b, hb, h⟩⟩)
    · exact Or.inl h.symm
    · exact Or.inr (Or.inl h.symm)
    · exact Or.inr (Or.inr (Or.inl (h ▸ ha)))
    · exact Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, h⟩))
  · rintro (h | h | h | ⟨a, ha, b, hb, h⟩)
    · exact Or.inl (Or.inl h.symm)
    · exact Or.inl (Or.inr h.symm)
    · exact Or.inr ⟨x, h, Or.inl rfl⟩
    · exact Or.inr ⟨a, ha, Or.inr ⟨b, hb, h⟩⟩

theorem ob_step (P : List ℕ) (ob c : ℕ) (hob : ∀ x, ob.testBit x = true ↔ x ∈ stepC P) :
    ∀ x, (ext c (P ++ [c]) (ob ||| (1 <<< c))).testBit x = true ↔ x ∈ stepC (P ++ [c]) := by
  intro x
  rw [ext_testBit, Nat.testBit_or, Bool.or_eq_true, hob, testBit_shl, decide_eq_true_eq,
    mem_stepC, mem_stepC]
  simp only [List.mem_append, List.mem_singleton]
  constructor
  · rintro (((h | h | h | ⟨a, ha, b, hb, h⟩) | h) | ⟨y, hy, h⟩)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inr ⟨a, Or.inl ha, b, Or.inl hb, h⟩))
    · exact Or.inr (Or.inr (Or.inl (Or.inr h.symm)))
    · exact Or.inr (Or.inr (Or.inr ⟨c, Or.inr rfl, y, hy, h⟩))
  · rintro (h | h | (h | h) | ⟨a, ha, b, hb, h⟩)
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr (Or.inl h)))
    · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inl h))))
    · exact Or.inl (Or.inr h.symm)
    · rcases ha with ha | rfl
      · rcases hb with hb | rfl
        · exact Or.inl (Or.inl (Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb, h⟩))))
        · refine Or.inr ⟨a, Or.inl ha, ?_⟩
          rcases h with h | h
          · exact Or.inl (h.trans (Nat.land_comm _ _))
          · exact Or.inr (h.trans (Nat.lor_comm _ _))
      · exact Or.inr ⟨b, hb, h⟩

theorem land_self' (x : ℕ) : x &&& x = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_and]

theorem lor_self' (x : ℕ) : x ||| x = x := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp [Nat.testBit_or]

def cands (ob : ℕ) (P : List ℕ) : List ℕ :=
  (List.range 256).filter (fun c => ob.testBit c && !P.contains c)

theorem mem_cands {ob c : ℕ} {P : List ℕ} (h1 : c < 256) (h2 : ob.testBit c = true)
    (h3 : c ∉ P) : c ∈ cands ob P := by
  simp [cands, h1, h2, h3]

def mk (f : ℕ → Bool) : ℕ :=
  (List.range 256).foldl (fun s c => if f c then s ||| (1 <<< c) else s) 0

theorem fold_keep (f : ℕ → Bool) (x : ℕ) : ∀ (l : List ℕ) (s : ℕ), s.testBit x = true →
    (l.foldl (fun s c => if f c then s ||| (1 <<< c) else s) s).testBit x = true
  | [], _, h => h
  | c :: l, s, h => by
    rw [List.foldl_cons]
    apply fold_keep f x l
    split
    · rw [Nat.testBit_or, h, Bool.true_or]
    · exact h

theorem fold_set (f : ℕ → Bool) (x : ℕ) : ∀ (l : List ℕ) (s : ℕ), x ∈ l → f x = true →
    (l.foldl (fun s c => if f c then s ||| (1 <<< c) else s) s).testBit x = true
  | [], _, h, _ => by simp at h
  | c :: l, s, h, hf => by
    rw [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · apply fold_keep
      rw [if_pos hf, Nat.testBit_or, testBit_shl]
      simp
    · exact fold_set f x l _ h hf

theorem mk_testBit (f : ℕ → Bool) (x : ℕ) (hx : x < 256) (hf : f x = true) :
    (mk f).testBit x = true :=
  fold_set f x _ 0 (List.mem_range.mpr hx) hf

def hit3 (T ob : ℕ) (P : List ℕ) : Bool :=
  (P.filter (fun y => y &&& T == T)).any (fun y => ob &&& mk (fun c => c &&& y == T) != 0) ||
  (P.filter (fun y => y ||| T == T)).any (fun y => ob &&& mk (fun c => c ||| y == T) != 0)

theorem ne_zero_of_testBit {n i : ℕ} (h : n.testBit i = true) : n ≠ 0 := by
  rintro rfl
  simp at h

theorem hit3_of (T ob : ℕ) (P : List ℕ) (x y : ℕ) (hx : ob.testBit x = true) (hx256 : x < 256)
    (hy : y ∈ P) (h : x &&& y = T ∨ x ||| y = T) : hit3 T ob P = true := by
  unfold hit3
  rw [Bool.or_eq_true]
  rcases h with h | h
  · left
    rw [List.any_eq_true]
    refine ⟨y, List.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩
    · subst h
      have : y &&& (x &&& y) = x &&& y := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_and]
        cases x.testBit i <;> cases y.testBit i <;> rfl
      simp [this]
    · have hb : (ob &&& mk (fun c => c &&& y == T)).testBit x = true := by
        rw [Nat.testBit_and, hx, mk_testBit _ x hx256 (by simp [h])]
        rfl
      simpa using ne_zero_of_testBit hb
  · right
    rw [List.any_eq_true]
    refine ⟨y, List.mem_filter.mpr ⟨hy, ?_⟩, ?_⟩
    · subst h
      have : y ||| (x ||| y) = x ||| y := by
        apply Nat.eq_of_testBit_eq
        intro i
        simp only [Nat.testBit_or]
        cases x.testBit i <;> cases y.testBit i <;> rfl
      simp [this]
    · have hb : (ob &&& mk (fun c => c ||| y == T)).testBit x = true := by
        rw [Nat.testBit_and, hx, mk_testBit _ x hx256 (by simp [h])]
        rfl
      simpa using ne_zero_of_testBit hb

-- the search: values are added in increasing order unless the new value needs the last one

def search (T : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ → Bool
  | 0, _, _, _, P => P.contains T
  | 1, _, ob, _, _ => ob.testBit T
  | 2, _, ob, _, P => ob.testBit T || hit3 T ob P
  | k + 3, pob, ob, last, P => ob.testBit T ||
      (cands ob P).any (fun c => (Nat.ble last c || !pob.testBit c) &&
        search T (k + 2) ob (ext c (P ++ [c]) (ob ||| (1 <<< c))) c (P ++ [c]))

theorem complete (T : ℕ) : ∀ (k pob ob last : ℕ) (P L : List ℕ),
    (∀ x, ob.testBit x = true ↔ x ∈ stepC P) → (∀ x ∈ P, x < 256) → Chain P L →
    (∀ c ∈ L, c ∉ P → pob.testBit c = true → last ≤ c) → T ∈ P ++ L → mu P L ≤ k →
    search T k pob ob last P = true
  | 0, pob, ob, last, P, L, hob, hb, hch, hpob, hT, hmu => by
    have h0 := mu_zero (Nat.le_zero.mp hmu)
    have hTP : T ∈ P := by
      rcases List.mem_append.mp hT with h | h
      · exact h
      · exact h0 T h
    simp [search, hTP]
  | 1, pob, ob, last, P, L, hob, hb, hch, hpob, hT, hmu => by
    simp [search, (hob T).2 (obt_of_mu1 P L T hch hT hmu)]
  | 2, pob, ob, last, P, L, hob, hb, hch, hpob, hT, hmu => by
    by_cases hTs : T ∈ stepC P
    · simp [search, (hob T).2 hTs]
    · have hTP : T ∉ P := fun h => hTs (self_mem_stepC h)
      have hTL : T ∈ L := by
        rcases List.mem_append.mp hT with h | h
        · exact absurd h hTP
        · exact h
      obtain ⟨x, hx, hxP, hxs⟩ := first_new L P hch ⟨T, hTL, hTP⟩
      have hx256 : x < 256 := stepC_lt hb hxs
      have hsub : ∀ y ∈ P, y ∈ P ++ [x] := fun y hy => List.mem_append_left _ hy
      have hmu' := mu_snoc L P x hx hxP
      have hT' : T ∈ stepC (P ++ [x]) :=
        obt_of_mu1 (P ++ [x]) L T (chain_mono L P _ hsub hch)
          (List.mem_append_right _ hTL) (by omega)
      have hxT : x ≠ T := fun h => hTs (h ▸ hxs)
      have key : ∃ y ∈ P, x &&& y = T ∨ x ||| y = T := by
        rw [mem_stepC] at hT'
        simp only [List.mem_append, List.mem_singleton] at hT'
        rcases hT' with h | h | (h | h) | ⟨a, ha, b, hb', h⟩
        · exact absurd ((mem_stepC P T).2 (Or.inl h)) hTs
        · exact absurd ((mem_stepC P T).2 (Or.inr (Or.inl h))) hTs
        · exact absurd h hTP
        · exact absurd h.symm hxT
        · rcases ha with ha | rfl
          · rcases hb' with hb' | rfl
            · exact absurd ((mem_stepC P T).2 (Or.inr (Or.inr (Or.inr ⟨a, ha, b, hb', h⟩)))) hTs
            · refine ⟨a, ha, ?_⟩
              rcases h with h | h
              · exact Or.inl ((Nat.land_comm _ _).trans h.symm)
              · exact Or.inr ((Nat.lor_comm _ _).trans h.symm)
          · rcases hb' with hb' | rfl
            · rcases h with h | h
              · exact ⟨b, hb', Or.inl h.symm⟩
              · exact ⟨b, hb', Or.inr h.symm⟩
            · rcases h with h | h
              · rw [land_self'] at h; exact absurd h.symm hxT
              · rw [lor_self'] at h; exact absurd h.symm hxT
      obtain ⟨y, hy, hxy⟩ := key
      simp [search, hit3_of T ob P x y ((hob x).2 hxs) hx256 hy hxy]
  | k + 3, pob, ob, last, P, L, hob, hb, hch, hpob, hT, hmu => by
    by_cases hTs : T ∈ stepC P
    · simp [search, (hob T).2 hTs]
    · have hTP : T ∉ P := fun h => hTs (self_mem_stepC h)
      have hTL : T ∈ L := by
        rcases List.mem_append.mp hT with h | h
        · exact absurd h hTP
        · exact h
      have hex := first_new L P hch ⟨T, hTL, hTP⟩
      classical
      let c := Nat.find hex
      have hc : c ∈ L ∧ c ∉ P ∧ c ∈ stepC P := Nat.find_spec hex
      have hcmin : ∀ m, m ∈ L ∧ m ∉ P ∧ m ∈ stepC P → c ≤ m := fun m hm => Nat.find_min' hex hm
      have hc256 : c < 256 := stepC_lt hb hc.2.2
      have hsub : ∀ y ∈ P, y ∈ P ++ [c] := fun y hy => List.mem_append_left _ hy
      have hmu' := mu_snoc L P c hc.1 hc.2.1
      have hrec := complete T (k + 2) ob (ext c (P ++ [c]) (ob ||| (1 <<< c))) c (P ++ [c]) L
        (ob_step P ob c hob)
        (fun x hx => by
          rcases List.mem_append.mp hx with hx | hx
          · exact hb x hx
          · rw [List.mem_singleton.mp hx]; exact hc256)
        (chain_mono L P _ hsub hch)
        (fun m hm hmP hmo => hcmin m ⟨hm, fun h => hmP (List.mem_append_left _ h), (hob m).1 hmo⟩)
        (List.mem_append_right _ hTL) (by omega)
      have hcond : (Nat.ble last c || !pob.testBit c) = true := by
        cases hpc : pob.testBit c
        · simp
        · have := hpob c hc.1 hc.2.1 hpc
          simp [Nat.ble_eq, this]
      have hmem := mem_cands hc256 ((hob c).2 hc.2.2) hc.2.1
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨c, hmem, by rw [hcond, hrec]; rfl⟩

theorem split3 (T k pob ob last : ℕ) (P : List ℕ) (h1 : ob.testBit T = false)
    (h2 : ∀ c ∈ cands ob P,
      search T (k + 2) ob (ext c (P ++ [c]) (ob ||| (1 <<< c))) c (P ++ [c]) = false) :
    search T (k + 3) pob ob last P = false := by
  simp only [search, h1, Bool.false_or]
  rw [List.any_eq_false]
  intro c hc
  simp [h2 c hc]

-- the 8 rows

def ru (q : Fin 8) : Fin 4 := ⟨[0, 1, 2, 2, 2, 3, 3, 3].getD q.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩

def rv (q : Fin 8) : Fin 4 := ⟨[3, 3, 1, 2, 3, 0, 2, 3].getD q.val 0 % 4, Nat.mod_lt _ (by norm_num)⟩

def X (q : Fin 8) : List Bool := oneEach (ru q) (rv q)

theorem X_len (q : Fin 8) : (X q).length = 8 := by simp [X, oneEach]

def pool0 : List ℕ := [1, 2, 28, 224, 32, 4, 72, 147, 0]

theorem inv0 : Inv pool0 X := by
  intro i
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 8, (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by simp [pool0], fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

theorem rows_ok : ∀ q : Fin 8,
    (6143 : ℕ).testBit (4 * (ru q).val + (rv q).val) = (47 : ℕ).testBit q.val := by decide

theorem pool0_lt : ∀ x ∈ pool0, x < 256 := by decide

theorem root_false : search 47 4 0 (obOf pool0) 0 pool0 = false := by decide +kernel

theorem lower : ¬ RepSizeAtMost (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  rintro ⟨C, hC, hs, hrep⟩
  obtain ⟨Lc, hlen, hch, m, hm, hmb⟩ := to_chain C.gates pool0 X 8 C.output hC X_len inv0
  have hLc := chain_lt Lc pool0 pool0_lt hch
  have hm256 : m < 256 := by
    rcases List.mem_append.mp hm with h | h
    · exact pool0_lt m h
    · exact hLc m h
  have hmT : m = 47 := by
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < 8
    · have h1 := hmb ⟨i, hi⟩
      have h2 := hrep (ru ⟨i, hi⟩) (rv ⟨i, hi⟩)
      have h3 := rows_ok ⟨i, hi⟩
      exact h1.trans (h2.trans h3)
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hm256 (by
          calc (256 : ℕ) = 2 ^ 8 := by norm_num
            _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by norm_num : (47 : ℕ) < 2 ^ 8)
          (Nat.pow_le_pow_right (by norm_num) (by omega)))]
  have hmu : mu pool0 Lc ≤ 4 := by
    have := List.countP_le_length (p := fun x => decide (x ∉ pool0)) (l := Lc)
    unfold mu
    have hs' : C.gates.length ≤ 4 := hs
    omega
  have := complete 47 4 0 (obOf pool0) 0 pool0 Lc (obOf_testBit pool0) pool0_lt hch
    (fun c _ _ _ => Nat.zero_le c) (hmT ▸ hm) hmu
  rw [root_false] at this
  exact absurd this (by decide)

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) 5 := by
  refine ⟨⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [8, 4]⟩, ⟨GateOp.or, [5, 6]⟩, ⟨GateOp.and, [2, 10]⟩,
    ⟨GateOp.or, [9, 11]⟩], 12⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;> simp

end PEqualNP.Outside.L_meta_6130_aux

theorem PEqualNP.Outside.L_meta_6130 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) 5 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (6143 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  exact ⟨PEqualNP.Outside.L_meta_6130_aux.upper, PEqualNP.Outside.L_meta_6130_aux.lower⟩
