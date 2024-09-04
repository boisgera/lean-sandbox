variable {A B C P Q R S T : Prop}


example : A ∧ (A -> B) -> B :=
  λ a_and_b_of_a =>
    let a := a_and_b_of_a.left
    let b_of_a := a_and_b_of_a.right
    show B from b_of_a a

theorem modus_ponens : (P -> Q) ∧ P -> Q :=
  λ QP_P => QP_P.left QP_P.right

theorem modus_tollens : (P -> Q) ∧ ¬Q -> ¬P :=
  λ h =>
    λ x =>
      h.right (h.left x)

theorem modus_tollens' : (P -> Q) ∧ (Q -> False) -> (P -> False) :=
  λ h =>
    λ x =>
      h.right (h.left x)

example : A ∧ (A -> B) -> B :=
  λ c => c.right c.left

theorem green : A -> B -> A :=
  λ a => λ _b => a

example : A -> B -> A ∧ B :=
  λ a =>
    λ b =>
      And.intro a b

example : A -> B -> A ∧ B :=
  λ a => λ b => ⟨a, b⟩

theorem c (a: A) (b: B) : A ∧ B := ⟨a, b⟩




theorem blue : (A -> B -> A) -> (B -> A) :=
  λ aba => λ ba => _

#print blue

theorem red : (A -> A -> B) -> (A -> B) :=
  λ baa => λ a => baa a a

theorem red' (f : A -> A -> B) (a : A) : B :=
  f a a

theorem and_comm' : (A ∧ B) → (B ∧ A) :=
  λ ab => And.intro (And.right ab) (And.left ab)

theorem add_comm'' (ab : A ∧ B) : (B ∧ A) :=
  have A_holds : A := ab.left
  have B_holds : B := ab.right
  show B ∧ A from And.intro B_holds A_holds


example : A -> A ∨ B :=
  λ a => Or.intro_left B a

example : B -> A ∨ B :=
  λ b => Or.intro_right A b

example (b : B) : A ∨ B :=
  Or.intro_right A b

example : (P ∨ Q) -> (Q ∨ P) :=
  λ p_or_q =>
    Or.elim p_or_q
      (λ p => Or.intro_right Q p)
      (λ q => Or.intro_left P q)

variable (p q : Prop)

theorem and_swap : p ∧ q ↔ q ∧ p :=
  let sw {a b : Prop} (x : a ∧ b) := And.intro x.right x.left
  Iff.intro sw sw

/-
Commutativity:

    p ∧ q ↔ q ∧ p
    p ∨ q ↔ q ∨ p

-/

var (p q r s t u v w : Prop)

example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ p_q => And.intro p_q.right p_q.left)
    (λ q_p => And.intro q_p.right q_p.left)


theorem or_comm' : P ∨ Q <-> Q ∨ P :=
  Iff.intro
    (λ p_or_q => Or.elim p_or_q
      (λ p => Or.intro_right Q p)
      (λ q => Or.intro_left P q)
    )
    (λ q_or_p => Or.elim q_or_p
      (λ q => Or.intro_right P q)
      (λ p => Or.intro_left Q p)
    )

theorem shjdhskjdhsjkdhsdjh : P ∨ Q <-> Q ∨ P :=
  Iff.intro
    (λ p_or_q => Or.elim p_or_q
      (λ p => Or.intro_right Q p)
      (λ q => Or.intro_left P q)
    )
    (λ q_or_p => Or.elim q_or_p
      (λ q => Or.intro_right P q)
      (λ p => Or.intro_left Q p)
    )

/-
Associativity:

    (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
    (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
-/

example : (P ∧ Q) ∧ R ↔ P ∧ (Q ∧ R) :=
  Iff.intro
    (λ pq_r =>
      let pq := pq_r.left
      let p := pq.left
      let q := pq.right
      let r := pq_r.right
      ⟨p, ⟨q, r⟩⟩
    )
    (λ p_qr =>
      let qr := p_qr.right
      let q := qr.left
      let r := qr.right
      let p := p_qr.left
      ⟨⟨p, q⟩, r⟩
    )

theorem or1 (pq_r : (P ∨ Q) ∨ R) : P ∨ (Q ∨ R) :=
  Or.elim pq_r
    (λ pq => Or.elim pq
      (λ p => Or.intro_left (Q ∨ R) p)
      (λ q => Or.intro_right P (Or.intro_left R q))
    )
    (λ r => Or.intro_right P (Or.intro_right Q r))

theorem or2 (p_qr : P ∨ (Q ∨ R)) : (P ∨ Q) ∨ R :=
  let qr_p := or_comm'.mp p_qr
  let rq_p := Or.elim qr_p
    (λ rq => Or.intro_left P (or_comm'.mp rq))
    (λ p => Or.intro_right (R ∨ Q) p)
  let r_qp := or1 rq_p
  let (r_pq : R ∨ (P ∨ Q)) := (Or.elim r_qp
    (λ r => Or.intro_left _ r)
    (λ qp => Or.intro_right _ (or_comm'.mp qp))
  )
  let pq_r := or_comm'.mp r_pq
  pq_r

example : (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
  Iff.intro or1 or2

/-

Distributivity:

    p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
    p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
-/

theorem and_or_distrib_mp : P ∧ (Q ∨ R) -> (P ∧ Q) ∨ (P ∧ R) :=
  λ p_qr =>
    let p := p_qr.left
    let qr := p_qr.right
    qr.elim
      (λ q =>
        let pq := And.intro p q
        Or.intro_left (P ∧ R) pq)
      (λ r =>
        let pr := And.intro p r
        Or.intro_right (P ∧ Q) pr)

theorem and_or_distrib_mpr :  ((P ∧ Q) ∨ (P ∧ R)) -> (P ∧ (Q ∨ R)) :=
  λ pq_pr =>
    pq_pr.elim
      (λ pq =>
        let p := pq.left
        let q := pq.right
        And.intro p (Or.intro_left _ q))
      (λ pr =>
        let p := pr.left
        let r := pr.right
        And.intro p (Or.intro_right _ r))

theorem and_or_distrib : P ∧ (Q ∨ R) <-> (P ∧ Q) ∨ (P ∧ R) :=
  Iff.intro and_or_distrib_mp and_or_distrib_mpr

/-
Other properties:

    (p → (q → r)) ↔ (p ∧ q → r)
    ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
    ¬(p ∨ q) ↔ ¬p ∧ ¬q
    ¬p ∨ ¬q → ¬(p ∧ q)
    ¬(p ∧ ¬p)
    p ∧ ¬q → ¬(p → q)
    ¬p → (p → q)
    (¬p ∨ q) → (p → q)
    p ∨ False ↔ p
    p ∧ False ↔ False
    ¬(p ↔ ¬p)
    (p → q) → (¬q → ¬p)
-/

theorem arrows_mp : (P → (Q → R)) -> (P ∧ Q → R) :=
  λ p_qr =>
    λ pq =>
      let p := pq.left
      let q := pq.right
      p_qr p q

theorem arrows_mpr : (P ∧ Q → R) -> (P → (Q → R)) :=
  λ pq_r =>
    λ p =>
      λ q =>
        pq_r (And.intro p q)

theorem arrows_mp' : ((P ∨ Q) → R) -> (P → R) ∧ (Q → R) :=
  λ pq_r =>
    And.intro
      (λ p => pq_r (Or.intro_left Q p))
      (λ q => pq_r (Or.intro_right P q))

theorem arrows_mpr' : (P → R) ∧ (Q → R) -> ((P ∨ Q) → R) :=
  λ pr_qr =>
    λ pq =>
      pq.elim
        (λ p => pr_qr.left p)
        (λ q => pr_qr.right q)

theorem K1 : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q :=
  Iff.intro
    (λ neg_p_q =>
      And.intro
        (λ p => neg_p_q (Or.intro_left Q p))
        (λ q => neg_p_q (Or.intro_right P q))
    )
    (λ neg_p_neg_q =>
      λ p_q =>
        Or.elim p_q
          (λ p => neg_p_neg_q.left p)
          (λ q => neg_p_neg_q.right q)
    )

theorem K2 : ¬P ∨ ¬Q → ¬(P ∧ Q) :=
  λ neg_p_or_neg_q =>
    λ p_and_q =>
      let p := p_and_q.left
      let q := p_and_q.right
      neg_p_or_neg_q.elim
        (λ neg_p => neg_p p)
        (λ neg_q => neg_q q)

theorem K3 : ¬(P ∧ ¬P) :=
  λ p_and_neg_p =>
    let p := p_and_neg_p.left
    let neg_p := p_and_neg_p.right
    neg_p p

theorem K4 : P ∧ ¬Q → ¬(P → Q) :=
  λ p_and_neg_q =>
    let p := p_and_neg_q.left
    let q_to_false := p_and_neg_q.right
    λ p_to_q =>
      q_to_false (p_to_q p)

theorem L1: False -> Q :=
  False.rec

theorem K5 : ¬P → (P → Q) :=
  λ neg_p =>
    λ p =>
      absurd p neg_p

theorem K5' : ¬P → (P → Q) :=
  λ p_to_false =>
    λ p =>
      (p_to_false p).rec

theorem K6 : (¬P ∨ Q) → (P → Q) :=
  λ neg_p_or_q =>
    λ p =>
      neg_p_or_q.elim
        (λ neg_p => absurd p neg_p)
        (λ q => q)

theorem K7 : P ∨ False ↔ P :=
  Iff.intro
    (λ p_or_false => p_or_false.elim (λ p => p) (λ false => false.rec))
    (λ p => Or.intro_left False p)

theorem K8 : P ∧ False ↔ False :=
  Iff.intro
    (λ p_and_false => p_and_false.right)
    (λ false => And.intro false.rec false)

theorem K9 : ¬(P ↔ ¬P) :=
  λ p_iff_neg_p =>
    let (neg_p : ¬P) := λ p =>
      absurd p (p_iff_neg_p.mp p)
    let p := p_iff_neg_p.mpr neg_p
    absurd p neg_p

theorem K10 : (P → Q) → (¬Q → ¬P) :=
  λ q_from_p =>
    λ false_from_q =>
      λ p => false_from_q (q_from_p p)


/-
These require classical reasoning:

    (p → r ∨ s) → ((p → r) ∨ (p → s))
    ¬(p ∧ q) → ¬p ∨ ¬q
    ¬(p → q) → p ∧ ¬q
    (p → q) → (¬p ∨ q)
    (¬q → ¬p) → (p → q)
    p ∨ ¬p
    (((p → q) → p) → p)

-/

open Classical

#check em
#check em P


theorem neg_neg : ¬¬P <-> P :=
  Iff.intro
    (λ neg_neg_p =>
      (em P).elim
        (λ p => p)
        (λ neg_p => absurd neg_p neg_neg_p)
    )
    (λ p =>
      λ false_from_p =>
        false_from_p p
    )

example : ¬P -> (P -> Q) :=
  λ not_p =>
    λ p => absurd p not_p

theorem C01: (P → R ∨ S) → ((P → R) ∨ (P → S)) :=
  λ r_or_s_from_p =>
    let p_or_not_p := em P
    p_or_not_p.elim
      (λ p =>
        let r_or_s := r_or_s_from_p p
        r_or_s.elim
          (λ r => Or.intro_left _ (λ _p => r))
          (λ s => Or.intro_right _ (λ _q => s))
      )
      (λ not_p =>
        Or.intro_left (P -> S) (λ p => absurd p not_p))

theorem C02: ¬(P ∧ Q) → ¬P ∨ ¬Q :=
  λ false_from_p_and_q =>
    let p_or_not_p := em P
    p_or_not_p.elim
      (λ p =>
        have not_q : ¬Q := (λ q => false_from_p_and_q (And.intro p q))
        Or.intro_right _ not_q)
      (λ not_p =>
        Or.intro_left _ not_p)

theorem C03: ¬(P → Q) → P ∧ ¬Q :=
  λ false_from_q_from_p =>
    (em P).elim
      (λ p =>
        have false_from_q : ¬Q :=
          λ q => false_from_q_from_p (λ _p => q)
        And.intro p false_from_q)
      (λ not_p =>
        have q_from_p : P -> Q :=
          λ p => absurd p not_p
        absurd q_from_p false_from_q_from_p)

theorem C04: (P → Q) → (¬P ∨ Q) :=
  λ q_from_p =>
    (em P).elim
      (λ p =>
        Or.intro_right _ (q_from_p p))
      (λ neg_p =>
        Or.intro_left _ neg_p)

theorem C05: (¬Q → ¬P) → (P → Q) :=
  λ not_q_not_p =>
    (em Q).elim
      (λ q => λ _p => q)
      (λ not_q => λ p => absurd p (not_q_not_p not_q))

theorem C06: P ∨ ¬P :=
  em P

theorem C07: (((P → Q) → P) → P) :=
  λ p_from_q_from_p =>
    (em P).elim
      (λ p => p)
      (λ neg_p =>
        sorry
      )
