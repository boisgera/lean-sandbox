
section block_1


  example (α : Type) (p q : α → Prop) : (∀ x : α, p x ∧ q x) → ∀ y : α, p y :=
    λ x_px_qx =>
      λ y => (x_px_qx y).left

  -------------------------------------------------------------------



  variable (α : Type) (P Q : α → Prop)


  example : (∀ x, P x ∧ Q x) ↔ (∀ x, P x) ∧ (∀ x, Q x) :=
    Iff.intro
      (λ x_to_pq => (And.intro
        (λ x => (And.left (x_to_pq x)))
        (λ x => (And.right (x_to_pq x)))
      ))
      (λ x_px_x_qx =>
        λ x => And.intro (x_px_x_qx.left x) (x_px_x_qx.right x))

  example : (∀ x, P x → Q x) → (∀ x, P x) → (∀ x, Q x) :=
    λ f =>
      λ g =>
        λ x => ((f x) (g x))

  example : (∀ x, P x) ∨ (∀ x, Q x) → ∀ x, P x ∨ Q x :=
    λ Px_Qx => λ x => Px_Qx.elim
        (λ Px => (Or.intro_left _ (Px x)))
        (λ Qx => (Or.intro_right _ (Qx x)))

  variable (α : Type) (P Q : α → Prop)
  variable (R : Prop)

  example : α → ((∀ _x : α, R) ↔ R) :=
    λ a =>
      Iff.intro
        (λ Rx => Rx a)
        (λ R => λ _x => R)

  open Classical

  example : (∀ x, P x ∨ R) ↔ (∀ x, P x) ∨ R :=
    Iff.intro
      (λ h₁ => (em R).elim
        (λ r => Or.intro_right _ r)
        (λ not_r =>
          have fxPx : (∀ x, P x) :=
            λ x => (h₁ x).elim (λ px => px) (λ r => absurd r not_r)
          Or.intro_left _ fxPx)
      )
      (λ h₂ => h₂.elim
        (λ px => λ x => Or.intro_left _ (px x))
        (λ r => λ _x => Or.intro_right _ r))

  example : (∀ x, R → P x) ↔ (R → ∀ x, P x) :=
    Iff.intro
      (λ h => (λ r x => h x r))
      (λ h => λ x => λ r => h r x)


end block_1

section barber

  theorem P_and_not_P_absurd {P: Prop}: ¬(P <-> ¬P) :=
    λ p_not_p =>
      have not_p : ¬P :=
        λ p => absurd p (p_not_p.mp p)
      absurd (p_not_p.mpr not_p) not_p


  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False :=
    let h_barber := h barber
    P_and_not_P_absurd h_barber

end barber


------------------------------------------------------------------------------------

section EX

example : ∃ x : Nat, x > 0 :=
  Exists.intro 1 (Nat.zero_lt_succ 0)

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  Exists.elim h
    λ x h_px_qx => Exists.intro x (And.intro h_px_qx.right h_px_qx.left)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨x, h⟩ => ⟨x, ⟨h.right, h.left⟩⟩

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨x, ⟨hl, hr⟩⟩ => ⟨x, ⟨hr, hl⟩⟩

example (h: ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨x, hx⟩ := h
  ⟨x, ⟨hx.right, hx.left⟩⟩

def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  let ⟨a', ha'⟩ := h1
  let ⟨b', hb'⟩ := h2
  -- TODO: prove that a + b is even with witness based on a' + b'
  ⟨
    a' + b',
    calc a + b
      _ = 2*a' + b := by rw[ha']
      _ = 2*a' + 2*b' := by rw[hb']
      _ = 2*(a'+b') := by rw[Nat.mul_add]
  ⟩


example (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  let ⟨a', ha'⟩ := h1
  let ⟨b', hb'⟩ := h2
  -- TODO: prove that a + b is even with witness based on a' + b'
  ⟨
    a' + b',
    show a + b = 2 * (a' + b') from calc a + b
      _ = 2*a' + b := ha' ▸ Eq.refl (a+b)
      _ = 2*a' + 2*b' := hb' ▸ Eq.refl (2 * a' + b)
      _ = 2*(a'+b') := Eq.symm (Nat.mul_add 2 a' b')
  ⟩

example (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  let ⟨a', ha'⟩ := h1
  let ⟨b', hb'⟩ := h2
  -- TODO: prove that a + b is even with witness based on a' + b'
  ⟨
    a' + b',
    -- what we have : a = 2 * a' and b = 2 * b'
    -- we also have 2 * (a' + b') by reflexivity
    let w₁ := Eq.refl (2 * (a' + b'))
    let w₂ : (2 * a' + 2 * b') = 2 * (a' + b') := (Nat.mul_add 2 a' b') ▸ w₁
    let w₃ : a + b = 2 * (a' + b') := hb' ▸ (ha' ▸ w₂)
    w₃
    -- target: a + b = 2 * (a' + b')
  ⟩


end EX

--------------------------------------------------------------------------

section EX2

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  (em (∃ x, p x)).elim
    (λ ex_px => ex_px)
    (λ not_ex_px =>
      have l : ∀ x, ¬ p x :=
        λ x => λ px => not_ex_px (Exists.intro x px)
    absurd l h)

example : (∃ _x : α, r) → r :=
  λ h => h.elim (λ _ w => w)

example (a : α) : r → (∃ _x : α, r) :=
  λ hr => Exists.intro a hr

example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro
    (λ h => h.elim λ x px_r => And.intro (Exists.intro x px_r.left) px_r.right)
    (λ h => h.left.elim (λ x px => Exists.intro x (And.intro px h.right)))

example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro
    (λ h => h.elim λ x px_qx => ((em (p x)).elim
      (λ hpx => Or.inl (Exists.intro x hpx))
      (λ not_hpx =>
        let qx : q x :=
          Or.elim px_qx (λ px => absurd px not_hpx) (λ qx => qx)
       Or.inr (Exists.intro x qx))
    ))
    (λ ex_px_or_ex_qx =>
      ex_px_or_ex_qx.elim
        (λ ⟨x, px⟩ =>
          ⟨x, Or.inl px⟩
        )
        (λ ⟨x, qx⟩ =>
          ⟨x, Or.inr qx⟩
        )
    )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro
    (λ ax_px =>
      (λ ex_not_px =>
        (ex_not_px.elim λ a not_pa => (absurd (ax_px a) not_pa)))
    )
    (λ not_ex_x_not_px =>
      λ x =>
        let px_or_not_px := (em (p x))
        px_or_not_px.elim
          (λ px => px)
          (λ not_px => absurd (Exists.intro x not_px) not_ex_x_not_px)
    )

-------------- Probably a much simpler proof exists here
theorem lemma₁ {α : Type} {p : α -> Prop} : ¬ (∀ x, ¬ p x) -> ¬¬(∃ x, p x) :=
  λ not_all_x_not_px =>
    (λ not_ex_x_px =>
      have all_x_not_px : ∀ (x : α), ¬ p x :=
        λ x =>
          (em (p x)).elim
            (λ px =>
              (not_ex_x_px ⟨x, px⟩).rec
            )
            (λ not_px => not_px)
      absurd all_x_not_px not_all_x_not_px
    )

theorem nnaa {A : Prop} : ¬¬A -> A :=
  (em A).elim
    (λ a => λ _ => a)
    (λ not_a => λ not_not_a => absurd not_a not_not_a)

example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro
    (λ ⟨x, px⟩ =>
      λ a_x_not_px => absurd px (a_x_not_px x))
    (λ all_x_not_px_false =>
      (nnaa (lemma₁ all_x_not_px_false))
    )
--------------------------------------------------------


example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro
    (λ not_ex_x_px =>
      λ x =>
        let px_or_not_px := em (p x)
        px_or_not_px.elim
          (λ px => absurd ⟨x, px⟩ not_ex_x_px)
          (λ not_px => not_px)
    )
    (λ all_x_not_px =>
      λ ⟨x, px⟩ =>
        absurd px (all_x_not_px x))

----------------------------------------------------------

theorem lemmaGGG {α : Type} {p : α -> Prop} : ¬(∃ x, ¬ p x) -> (∀ x, p x) :=
  λ not_ex_x_not_px =>
    λ x =>
      (em (p x)).elim
        (λ _1 => _1)
        (λ not_px => (not_ex_x_not_px ⟨x, not_px⟩).rec)

example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro
    (λ not_all_x_px =>
      (em (∃ x, ¬ p x)).elim
        (λ _1 => _1)
        (λ not_ex_x_not_px => absurd (lemmaGGG not_ex_x_not_px) not_all_x_px)
    )
    (λ ⟨x, not_px⟩ =>
      λ all_x_px =>
        absurd (all_x_px x) not_px)

-----------------------------------------------------------

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro
    (λ all_x_px_r =>
      λ ⟨x, px⟩ =>
        all_x_px_r x px)
    (λ ex_x_px_r =>
      λ x =>
        λ px =>
          ex_x_px_r ⟨x, px⟩
    )

example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro
    (λ ⟨x, px_r⟩ =>
      λ x_px =>
        px_r (x_px x)
    )
    (λ all_x_px_r =>
      (em r).elim
        (λ r_ => ⟨a, λ _ => r_⟩)
        (λ not_r_ =>
          have lem : ∃ (x : α), ¬ p x :=
            sorry
          let ⟨x, not_px⟩ := lem
          ⟨x, λ px => absurd px not_px⟩
    )
    )

example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro
    (λ ⟨x, r_px⟩ =>
      λ r => ⟨x, r_px r⟩)
    (λ r_ex_x_px =>
      (em r).elim
        (λ r_ =>
          let ⟨x_, px_⟩ := r_ex_x_px r_
          ⟨x_, λ _r => px_⟩
        )
        (λ not_r => ⟨a, λ r_ => absurd r_ not_r⟩)
    )


end EX2

section TACTICS

theorem test₀ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  ⟨hp, hq, hp⟩

theorem test₁ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p :=
  And.intro
    hp
    (And.intro
      hq
      hp
    )

theorem test₂ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

-- #print test₂

theorem test₃ (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro hq
  apply hp

example {p q : Prop} (hp : p) (hq : q): p ∧ q ∧ p := by
  apply And.intro hp
  apply And.intro
  case left => exact hq
  case right => exact hp

example {p q : Prop} (hp : p) (hq : q): p ∧ q ∧ p := by
  apply And.intro
  apply hp
  apply And.intro
  case right.left => exact hq
  case right.right => exact hp

example {p q : Prop} (hp : p) (hq : q): p ∧ q ∧ p := by
  apply And.intro
  case left => apply hp -- sorry
  case right => apply And.intro hq hp -- sorry

example {p q : Prop} : p -> q -> p ∧ q ∧ p := by
  intro hp
  intro hq
  apply And.intro
  . exact hp
  . apply And.intro
    . exact hq
    . exact hp

example {p q r : Prop} : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro h
    apply Or.elim (And.right h)
    . intro hq
      let p_q := And.intro (And.left h) hq
      apply Or.inl p_q
    . intro hr
      let hp := h.left
      apply Or.inr
      apply And.intro
      exact hp
      exact hr
  . intro h
    apply And.intro
    . apply Or.elim h
      . intro ⟨hp, _⟩
        exact hp
      . intro ⟨hp, _⟩
        exact hp
    . apply h.elim
      . intro h_pq
        apply Or.inl
        exact h_pq.right
      . intro h_pr
        apply Or.inr
        exact h_pr.right


example (α : Type) : α → α := by
  intro a
  exact a


example (α : Type) : ∀ x : α, x = x := by
  intro x
  exact Eq.refl x

example : ∀ a b c : Nat, a = b → a = c → c = b := by
  intro a b c
  intro h₁ h₂
  let h₃ := Eq.symm h₂
  exact (Eq.trans h₃ h₁)

example (α : Type) (p q : α → Prop) : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x := by
  intro ⟨x, ⟨px, qx⟩⟩
  exact ⟨x, ⟨qx, px⟩⟩

example (α : Type) (p q : α → Prop) : (∃ x, p x ∨ q x) → ∃ x, q x ∨ p x := by
  intro h
  match h with
  | ⟨x, Or.inl px⟩ => exact ⟨x, Or.inr px⟩
  | ⟨x, Or.inr qx⟩ => exact ⟨x, Or.inl qx⟩

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans h₁
  apply Eq.trans h₂
  assumption

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  assumption
  apply Eq.trans
  assumption
  assumption

example (x y z w : Nat) (h₁ : x = y) (h₂ : y = z) (h₃ : z = w) : x = w := by
  apply Eq.trans
  . assumption
  . apply Eq.trans
    . assumption
    . assumption


example (y : Nat) : (fun x : Nat => 0) y = 0 := -- WTF is this type?
  sorry


example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  match h with
  | ⟨x, px⟩ =>
    constructor
    apply Or.inl
    exact px

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  match h with
  | ⟨x, px⟩ =>
    apply Exists.intro
    apply Or.inl
    exact px

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  . intro h
    cases h with
    | intro hp hq_or_hr =>
      cases hq_or_hr
      . apply Or.inl
        constructor
        repeat assumption
      . apply Or.inr
        constructor; repeat assumption
  . intro h
    constructor
    . cases h with
      | inl k => exact k.left
      | inr l => exact l.left
    . cases h with
      | inl k =>
        cases k with
        | intro a b => constructor; assumption
      | inr k => apply Or.inr; exact k.right

example (p q : Prop) : p ∧ ¬ p → q := by
  intro hp
  cases hp with
  | intro p not_p => contradiction

example (x y : Nat) (p : Nat → Prop) (q : Prop) (h : q → x = y)
        (h' : p y) (hq : q) : p x := by
  rw [h]
  repeat assumption








end TACTICS
