import Mathlib
import PEqualNP.Defs

-- The signed live-wire model and gate compiler are adapted from L_meta_8724
-- and L_meta_1449. The embedded five-input certificate excludes nine binary
-- gates. Two single-vertex restrictions then give the seven-input bound.
namespace PEqualNP.Outside.L_meta_10610.Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

-- Build: the goal is reached from the available wires in k binary steps. Live: the same,
-- keeping only the wires still needed, so a search may range over small sets.
section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

-- The upper and lower halves represent opposite target labels on 16 pairs of assignments.
abbrev W := BitVec 32
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 16 := ((x >>> 16) ^^^ x).setWidth 16
def cuts (ws : List W) : BitVec 16 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 16) ++ (0 : BitVec 16)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 16) (w : W) : Prop :=
  w.getLsbD (16+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 16) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 16+i.val < 32 := by omega
  have hi' : i.val < 32 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 16) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 16)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

-- The search: pick two live wires, apply one of the four operations, and keep each operand
-- only if it is still needed; every live run is found, so a false search rules out a build.
def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

-- Wires held up to complement, and what one binary gate reaches from them.
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_mono {av av' : Finset W} (sub : av ⊆ av') {x : W} (h : holds av x) :
    holds av' x :=
  h.imp_right (Or.imp_right fun ⟨a,ha,e⟩ => ⟨a,sub ha,e⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 32 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 32)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

-- Running a circuit on the 32 rows at once, NOT gates cost nothing.
private def bit (k : Fin 32) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 32) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 32) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#32)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_mono (Finset.subset_insert _ _) (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
-- The input columns encode pairs of rows for the five-input threshold function.
def table (x : Fin 5 → Bool) : Bool := Nat.testBit 0xfffefee8 (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

def cliqueInputs : List W := [0x2c4b2082, 0x54954104, 0x99268208, 0xe2380410, 0x3c00820]

theorem spec_fffefee8 : ∀ j : Fin 32, Nat.testBit 0xfffefee8 (∑ i : Fin 5, if (cliqueInputs.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel

-- A live run mapped through a bitwise homomorphism is a build of the mapped goal; a wire
-- mapped to zero saves its gate.
def SignedBuild (k : ℕ) (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ build basicOps z k av ∨ build basicOps (~~~z) k av

theorem sb_zero {av : Finset W} {z : W} (h : holds av z) : SignedBuild 0 av z := by
  rcases h with h | h | ⟨a,ha,rfl | rfl⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl ha))
  · exact .inr (.inr (.inr (by simpa only [BitVec.not_not,build] using ha)))

theorem sb_wait {av : Finset W} {z : W} {k : ℕ} (h : SignedBuild k av z) :
    SignedBuild (k+1) av z :=
  h.imp_right (Or.imp_right (Or.imp .inl .inl))

theorem sb_le {av : Finset W} {z : W} {k l : ℕ} (hkl : k ≤ l) (h : SignedBuild k av z) :
    SignedBuild l av z := by
  induction hkl with
  | refl => exact h
  | step _ ih => exact sb_wait ih

theorem sb_step {av : Finset W} {t a b z : W} {k : ℕ} (ha : a ∈ av) (hb : b ∈ av)
    (hne : a ≠ b) (hz : z ∈ basicOps a b) (h : SignedBuild k (insert z av) t) :
    SignedBuild (k+1) av t :=
  h.imp_right (Or.imp_right (Or.imp (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩) (.inr ⟨a,ha,b,hb,hne,z,hz,·⟩)))

theorem sb_advance {av : Finset W} {z t : W} {k : ℕ} (hz : reachable av z)
    (next : ∀ av' : Finset W, av ⊆ av' → holds av' z → SignedBuild k av' t) :
    SignedBuild (k+1) av t := by
  rcases hz with h | ⟨a,ha,b,hb,hn,w,hw,ok⟩
  · exact sb_wait (next av (fun _ h => h) h)
  · exact sb_step ha hb hn hw (next (insert w av) (fun _ h => Finset.mem_insert_of_mem h) ok)

theorem mem_ops_reach {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hz : z ∈ basicOps x y) : reachable av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl
  · exact and_reach hx hy
  · exact or_reach hx hy
  · exact and_reach hx (holds_not hy)
  · exact and_reach hy (holds_not hx)

set_option maxRecDepth 5000 in
theorem mem_ops_zero {av : Finset W} {x y z : W} (hx : holds av x) (hy : holds av y)
    (hzero : x = 0 ∨ y = 0) (hz : z ∈ basicOps x y) : holds av z := by
  simp only [basicOps,ops,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hz
  have hc : holds av (0 : W) := .inl rfl
  have absorb (v : W) : v &&& (~~~(0 : W)) = v := by
    exact (congrArg (fun u : W => v &&& u) (BitVec.not_zero (n := 32))).trans BitVec.and_allOnes
  rcases hzero with rfl | rfl <;> rcases hz with rfl|rfl|rfl|rfl <;>
    first | rwa [absorb] | simp_all

theorem live_transport {f : W → W} (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild k av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact sb_zero (hav g (by simp [run]))
  | succ k ih =>
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_wait (ih skip hav)
      · apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) (hm a b z hz))
        intro av' sub ok
        apply ih tail
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hr
        · exact ok
        · exact holds_mono sub (hav u (by simp [he,hr]))

theorem live_transport_save {f : W → W}
    (hm : ∀ a b z, z ∈ basicOps a b → f z ∈ basicOps (f a) (f b))
    {g p : W} {k : ℕ} {s av : Finset W} (run : live basicOps g k s)
    (hp : p ∈ s) (hpg : p ≠ g) (hzero : f p = 0)
    (hav : ∀ w ∈ s, holds av (f w)) : SignedBuild (k-1) av (f g) := by
  induction k generalizing s av with
  | zero =>
      change s = {g} at run
      exact False.elim (hpg (by simpa [run] using hp))
  | succ k ih =>
      simp only [Nat.add_sub_cancel] at *
      rcases run with skip | ⟨a,ha,b,hb,hn,z,hz,hout,r,he,tail⟩
      · exact sb_le (Nat.sub_le _ _) (ih skip hp hav)
      · have mapped := hm a b z hz
        have inOld : ∀ u ∈ r, holds av (f u) := fun u hu => hav u (by simp [he,hu])
        by_cases touches : p = a ∨ p = b
        · have zz : f a = 0 ∨ f b = 0 := touches.elim (fun h => .inl (h ▸ hzero)) (fun h => .inr (h ▸ hzero))
          have collapsed := mem_ops_zero (hav a ha) (hav b hb) zz mapped
          apply live_transport hm tail
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact collapsed
          · exact inOld u hr
        · have pr : p ∈ r := by
            rw [he] at hp
            simpa [Finset.mem_insert, touches, not_or.mp touches |>.1, not_or.mp touches |>.2] using hp
          have pt : p ∈ insert z r := Finset.mem_insert_of_mem pr
          have pos : 0 < k := by
            by_contra! hk
            have eq : k = 0 := by omega
            subst k
            change insert z r = {g} at tail
            exact hpg (by simpa [tail] using pt)
          have cost : (k-1)+1 = k := by omega
          rw [← cost]
          apply sb_advance (mem_ops_reach (hav a ha) (hav b hb) mapped)
          intro av' sub ok
          apply ih tail pt
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hr
          · exact ok
          · exact holds_mono sub (inOld u hr)

def changes (w : W) (r : Fin 16) : Bool := w.getLsbD (16+r.val) != w.getLsbD r.val

theorem goal_changes : ∀ k : Fin 16, differs k goal ∧ differs k (~~~goal) := by
  unfold differs
  decide +kernel
end PEqualNP.Outside.L_meta_10610.Signed



namespace PEqualNP.Outside.L_meta_10610.Cert

open PEqualNP.Outside.L_meta_10610.Signed

-- Rows 0 through 5 are the empty assignment and five singletons.
-- Rows 6 through 15 are the ten pairs of vertices, on which the clique is true.
abbrev V := BitVec 16
def g : V := 65472
def inp : List V := [4802, 9540, 18824, 36368, 61472]
def ops (a b : V) : List V := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
def dops (a b : V) : Finset V := ((ops a b).toFinset.erase 0).erase (-1)

theorem dops_swap (a b : V) : dops a b = dops b a := by
  ext z
  simp [dops, ops, BitVec.and_comm a b, BitVec.or_comm a b, or_assoc, or_left_comm, or_comm]

def good (k : ℕ) (ws : List V) : Bool :=
  (ws.length ≤ k + 1) && (List.finRange 10).all fun p =>
    (List.finRange 6).all fun q => ws.any fun w => w.getLsbD (6 + p.val) != w.getLsbD q.val

theorem good_live {k : ℕ} {ws : List V} (hn : ws.Nodup)
    (h : live dops g k ws.toFinset) : good k ws = true := by
  rw [good, Bool.and_eq_true]
  constructor
  · simpa [List.toFinset_card_of_nodup hn] using live_card h
  · simp only [List.all_eq_true, List.any_eq_true, bne_iff_ne]
    intro p _ q _
    have target : g.getLsbD (6 + p.val) ≠ g.getLsbD q.val := by
      revert p q
      decide +kernel
    obtain ⟨w, hw, hbit⟩ := live_separates
      (fun t : V => t.getLsbD (6 + p.val) ≠ t.getLsbD q.val) target
      (fun a b z hz hd => by
        have hmem := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
        simp only [ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hmem
        by_contra! fail
        obtain ⟨ha, hb⟩ := fail
        apply hd
        have hp : 6 + p.val < 16 := by omega
        have hq : q.val < 16 := by omega
        rcases hmem with rfl | rfl | rfl | rfl <;>
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hp, hq, decide_true, Bool.true_and, ha, hb]) h
    exact ⟨w, List.mem_toFinset.mp hw, hbit⟩


def posBits (w : V) := w.extractLsb' 6 10
def blockBits (w : V) (q : Nat) : BitVec 10 :=
  if w.getLsbD q then ~~~(posBits w) else posBits w
def glue {n : Nat} (a : BitVec 10) (b : BitVec n) : BitVec (10+n) := a ++ b
theorem glueBit {n : Nat} (a : BitVec 10) (b : BitVec n) (j : Nat) : (glue a b).getLsbD j = if j<n then b.getLsbD j else a.getLsbD (j-n) := BitVec.getLsbD_append
def wireBits (w : V) : BitVec 60 :=
  glue (blockBits w 5) (glue (blockBits w 4) (glue (blockBits w 3) (glue (blockBits w 2) (glue (blockBits w 1) (blockBits w 0)))))
def rowBits (ws : List V) : BitVec 60 := ws.foldr (fun w acc => wireBits w ||| acc) 0
def fastGood (k : Nat) (ws : List V) : Bool :=
  decide (ws.length ≤ k+1) && (rowBits ws == BitVec.allOnes 60)

theorem blockBits_bit (w : V) (i q : Nat) (hi : i < 10) :
    (blockBits w q).getLsbD i = (w.getLsbD (6+i) != w.getLsbD q) := by
  cases h : w.getLsbD q <;> simp [blockBits, posBits, h, BitVec.getLsbD_not, hi, BitVec.getLsbD_extractLsb', Nat.add_comm]

theorem blockBits_get (w : V) (i q : Nat) (hi : i < 10) (hq : q < 16) :
    (blockBits w q)[i] = (w[6+i]'(by omega) != w[q]) := by
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getLsbD_eq_getElem hq, BitVec.getLsbD_eq_getElem (show 6+i < 16 by omega)] using blockBits_bit w i q hi

theorem wireBits_bit (w : V) (p : Fin 10) (q : Fin 6) :
    (wireBits w).getLsbD (q.val*10 + p.val) = (w.getLsbD (6+p.val) != w.getLsbD q.val) := by
  have hp := p.isLt
  fin_cases q <;> fin_cases p <;> simp only [wireBits, glueBit] <;> norm_num [blockBits_bit] <;> apply blockBits_get <;> decide

theorem rowBits_bit (ws : List V) (w : V) (hw : w ∈ ws) (j : Nat)
    (h : (wireBits w).getLsbD j = true) : (rowBits ws).getLsbD j = true := by
  induction ws with
  | nil => simp at hw
  | cons a as ih =>
    rcases List.mem_cons.mp hw with rfl|hw
    · simp [rowBits, BitVec.getLsbD_or,h]
    · change (wireBits a ||| rowBits as).getLsbD j = true
      simp [BitVec.getLsbD_or,ih hw]

theorem fast_of_good {k ws} (h : good k ws = true) : fastGood k ws = true := by
  rw [good,Bool.and_eq_true] at h
  rcases h with ⟨len,sep⟩
  rw [fastGood,Bool.and_eq_true]
  refine ⟨len,beq_iff_eq.mpr ?_⟩
  apply BitVec.eq_of_getElem_eq
  intro i hi
  rw [← BitVec.getLsbD_eq_getElem hi]
  simp only [BitVec.getElem_allOnes]
  let p : Fin 10 := ⟨i%10,Nat.mod_lt _ (by decide)⟩
  let q : Fin 6 := ⟨i/10, by omega⟩
  have sep' : ∀ p : Fin 10, ∀ q : Fin 6, ∃ w ∈ ws, w.getLsbD (6+p.val) ≠ w.getLsbD q.val := by
    simpa [List.all_eq_true,List.any_eq_true,bne_iff_ne] using sep
  obtain ⟨w,hw,hpq⟩ := sep' p q
  apply rowBits_bit _ _ hw
  have eq : q.val*10+p.val = i := by dsimp [q,p]; omega
  rw [← eq, wireBits_bit]
  exact bne_iff_ne.mpr hpq


def choices (a b : V) (r : List V) : List (List V) := [r, a :: r, b :: r, a :: b :: r]

theorem recover {ws r : List V} {a b : V} {needed : Finset V}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ choices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [choices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [choices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [choices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [choices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_small {goal : V} {ws : List V} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc
def next (k : ℕ) (ws : List V) : List (List V) :=
  (pairs ws).flatMap fun (a,b,r) =>
    (ops a b).flatMap fun z =>
      if z = 0 ∨ z = -1 ∨ z ∈ ws then []
      else (choices a b r).filterMap fun rest =>
        if fastGood k (rest ++ [z]) then some (rest ++ [z]) else none

theorem next_complete {k : ℕ} {ws : List V} (hn : ws.Nodup)
    (h : live dops g (k+1) ws.toFinset) :
    ws = [g] ∨ ∃ t ∈ next k ws, live dops g k t.toFinset := by
  rcases first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hz',r,hrest,tail⟩
  · exact Or.inl (singleton_small hn done)
  obtain ⟨r', hp, perm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have choose {a b : V} (hp : (a,b,r') ∈ pairs ws) (perm : ws.Perm (a::b::r'))
      (hz : z ∈ dops a b) (hr : ws.toFinset = insert a (insert b r)) :
      ∃ t ∈ next k ws, live dops g k t.toFinset := by
    obtain ⟨kept, hm, hnod, hkept⟩ := recover perm hn hr
    have hzn : z ∉ kept := by
      intro h
      have hmem := List.mem_toFinset.mpr h
      rw [hkept] at hmem
      exact hz' (by simp [hrest, hmem])
    have ht : (kept ++ [z]).toFinset = insert z r := by
      ext u
      simp [← hkept, or_comm]
    have hl : live dops g k (kept ++ [z]).toFinset := ht ▸ tail
    have hd : (kept ++ [z]).Nodup := by
      exact List.nodup_append_comm.mpr
        (by simp [hnod, hzn])
    have hcheck := fast_of_good (good_live hd hl)
    have hmem := Finset.mem_erase.mp hz
    have hmem' := Finset.mem_erase.mp hmem.2
    have z1 : z ∉ ws := fun h => hz' (List.mem_toFinset.mpr h)
    refine ⟨kept ++ [z], List.mem_flatMap.mpr ⟨(a,b,r'),hp,?_⟩, hl⟩
    apply List.mem_flatMap.mpr
    refine ⟨z, List.mem_toFinset.mp hmem'.2, ?_⟩
    simp only [hmem.1, hmem'.1, z1, or_self, if_false]
    exact List.mem_filterMap.mpr ⟨kept, hm, by simp [hcheck]⟩
  right
  rcases hp with hp | hp
  · exact choose hp perm hz hrest
  · exact choose hp (perm.trans (List.Perm.swap ..)) (dops_swap a b ▸ hz)
      (by simpa [Finset.insert_comm] using hrest)

def negLookup : Array (BitVec 60) := #[
  0x0, 0x3ff, 0xffc00, 0xfffff,
  0x3ff00000, 0x3ff003ff, 0x3ffffc00, 0x3fffffff,
  0xffc0000000, 0xffc00003ff, 0xffc00ffc00, 0xffc00fffff,
  0xfffff00000, 0xfffff003ff, 0xfffffffc00, 0xffffffffff,
  0x3ff0000000000, 0x3ff00000003ff, 0x3ff00000ffc00, 0x3ff00000fffff,
  0x3ff003ff00000, 0x3ff003ff003ff, 0x3ff003ffffc00, 0x3ff003fffffff,
  0x3ffffc0000000, 0x3ffffc00003ff, 0x3ffffc00ffc00, 0x3ffffc00fffff,
  0x3fffffff00000, 0x3fffffff003ff, 0x3fffffffffc00, 0x3ffffffffffff,
  0xffc000000000000, 0xffc0000000003ff, 0xffc0000000ffc00, 0xffc0000000fffff,
  0xffc00003ff00000, 0xffc00003ff003ff, 0xffc00003ffffc00, 0xffc00003fffffff,
  0xffc00ffc0000000, 0xffc00ffc00003ff, 0xffc00ffc00ffc00, 0xffc00ffc00fffff,
  0xffc00fffff00000, 0xffc00fffff003ff, 0xffc00fffffffc00, 0xffc00ffffffffff,
  0xfffff0000000000, 0xfffff00000003ff, 0xfffff00000ffc00, 0xfffff00000fffff,
  0xfffff003ff00000, 0xfffff003ff003ff, 0xfffff003ffffc00, 0xfffff003fffffff,
  0xfffffffc0000000, 0xfffffffc00003ff, 0xfffffffc00ffc00, 0xfffffffc00fffff,
  0xffffffffff00000, 0xffffffffff003ff, 0xffffffffffffc00, 0xfffffffffffffff]

def negBlock (b : Nat → Bool) (q : Nat) : BitVec 10 := if b q then BitVec.allOnes 10 else 0

def negPack (b : Nat → Bool) : BitVec 60 :=
  glue (negBlock b 5)
    (glue (negBlock b 4)
      (glue (negBlock b 3) (glue (negBlock b 2) (glue (negBlock b 1) (negBlock b 0)))))

def repeated (p : BitVec 10) : BitVec 60 :=
  glue p (glue p (glue p (glue p (glue p p))))

def arithNeg (w : V) : BitVec 60 := negLookup[w.toNat % 64]!

def arithPos (w : V) : BitVec 60 :=
  BitVec.ofNat 60 ((w.toNat / 64) * 0x4010040100401)

def arithWire (w : V) : BitVec 60 := arithPos w ^^^ arithNeg w

theorem neg_lookup_ok : ∀ b : BitVec 6, negLookup[b.toNat]! = negPack b.getLsbD := by
  decide +kernel

theorem arithNeg_eq (w : V) : arithNeg w = negPack w.getLsbD := by
  change negLookup[(w.setWidth 6).toNat]! = _
  rw [neg_lookup_ok]
  simp [negPack, negBlock]

theorem pos_bits_nat (w : V) : (posBits w).toNat = w.toNat / 64 := by
  have h := w.isLt
  rw [posBits, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt]
  change w.toNat / 64 < 1024
  omega

theorem repeated_nat (p : BitVec 10) : (repeated p).toNat = p.toNat * 0x4010040100401 := by
  simp only [repeated, glue, BitVec.toNat_append_eq_mul_add]
  omega

theorem arithPos_eq (w : V) : arithPos w = repeated (posBits w) := by
  apply BitVec.eq_of_toNat_eq
  rw [arithPos, BitVec.toNat_ofNat, repeated_nat, pos_bits_nat]
  have h := w.isLt
  apply Nat.mod_eq_of_lt
  change w.toNat / 64 * 1127000493261825 < 1152921504606846976
  omega

theorem toggle_eq (w : V) (q : Nat) :
    posBits w ^^^ negBlock w.getLsbD q = blockBits w q := by
  cases h : w.getLsbD q
  · have hn : negBlock w.getLsbD q = 0 := by simp [negBlock, h]
    have hp : blockBits w q = posBits w := by simp [blockBits, h]
    rw [hn, hp]
    exact BitVec.xor_zero
  · have hn : negBlock w.getLsbD q = BitVec.allOnes 10 := by simp [negBlock, h]
    have hp : blockBits w q = ~~~posBits w := by simp [blockBits, h]
    rw [hn, hp]
    exact BitVec.xor_allOnes

theorem glueXor {n : Nat} (a b : BitVec 10) (c d : BitVec n) :
    glue a c ^^^ glue b d = glue (a ^^^ b) (c ^^^ d) :=
  BitVec.xor_append

def digitWidth : Nat → Nat
  | 0 => 10
  | k+1 => 10 + digitWidth k

def appendDigits : (k : Nat) → (Nat → BitVec 10) → BitVec (digitWidth k)
  | 0, f => f 0
  | k+1, f => glue (f (k+1)) (appendDigits k f)

theorem appendDigits_xor (k : Nat) (f h : Nat → BitVec 10) :
    appendDigits k f ^^^ appendDigits k h =
      appendDigits k (fun i => f i ^^^ h i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change glue (f (k+1)) (appendDigits k f) ^^^ glue (h (k+1)) (appendDigits k h) =
      glue (f (k+1) ^^^ h (k+1)) (appendDigits k (fun i => f i ^^^ h i))
    exact (glueXor ..).trans (congrArg (glue _) ih)

theorem arithWire_eq (w : V) : arithWire w = wireBits w := by
  rw [arithWire, arithPos_eq, arithNeg_eq]
  change appendDigits 5 (fun _ => posBits w) ^^^ appendDigits 5 (negBlock w.getLsbD) =
    appendDigits 5 (blockBits w)
  rw [appendDigits_xor]
  congr 1
  funext i
  exact toggle_eq w i

def arithRow (ws : List V) : BitVec 60 := ws.foldr (fun w acc => arithWire w ||| acc) 0

theorem arithRow_eq (ws : List V) : arithRow ws = rowBits ws := by
  simp only [arithRow, rowBits, arithWire_eq]

theorem rowBits_append (a b : List V) : rowBits (a ++ b) = rowBits a ||| rowBits b := by
  induction a with
  | nil => simp [rowBits]
  | cons x a ih =>
    change wireBits x ||| rowBits (a ++ b) = (wireBits x ||| rowBits a) ||| rowBits b
    rw [ih, BitVec.or_assoc]

theorem rowBits_cons (a : V) (r : List V) :
    rowBits (a :: r) = wireBits a ||| rowBits r := rfl

theorem rowBits_single (z : V) : rowBits [z] = wireBits z := by simp [rowBits]

def put (k : Nat) (r : List V) (z : V) (m : BitVec 60) : Option (List V) :=
  if (decide (r.length + 1 ≤ k + 1) && (m == BitVec.allOnes 60)) then
    some (r ++ [z])
  else none

def quickChoices (k : Nat) (a b : V) (r : List V) (z : V)
    (av bv rv : BitVec 60) : List (List V) :=
  let base := rv ||| arithWire z
  ([put k r z base, put k (a :: r) z (av ||| base),
    put k (b :: r) z (bv ||| base), put k (a :: b :: r) z (av ||| bv ||| base)] :
      List (Option (List V))).filterMap id

theorem quickChoices_eq (k : Nat) (a b : V) (r : List V) (z : V) :
    quickChoices k a b r z (arithWire a) (arithWire b) (arithRow r) =
      (choices a b r).filterMap (fun t =>
        if fastGood k (t ++ [z]) then some (t ++ [z]) else none) := by
  simp only [quickChoices, choices, List.filterMap_cons, List.filterMap_nil, id_eq,
    put, fastGood, List.length_append, List.length_singleton, rowBits_append,
    rowBits_cons, arithWire_eq, arithRow_eq, BitVec.or_assoc]
  simp [rowBits]

def quickNext (k : Nat) (ws : List V) : List (List V) :=
  (pairs ws).flatMap fun (a,b,r) =>
    let av := arithWire a
    let bv := arithWire b
    let rv := arithRow r
    (ops a b).flatMap fun z =>
      if z = 0 ∨ z = -1 ∨ z ∈ ws then [] else quickChoices k a b r z av bv rv

theorem quickNext_eq (k : Nat) (ws : List V) : quickNext k ws = next k ws := by
  simp only [quickNext, next, quickChoices_eq]

section

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_0 : Array Nat := #[ 0x17b9ac5a928398a418820,
    0x17ad49735883988518820,
    0x173dac5a0ea498a320820,
    0x15bd49720ed6188328820,
    0x172d077b58a4986520820,
    0x15b9077a92d6186428820,
    0x17b5cc52d2831ca410c20,
    0x17a9696b98831c8510c20,
    0x1735ec42cea324a311020,
    0x15a9e9438ed3308311420,
    0x1721676bd8a3246511020,
    0x15a1c753d2d3306411420,
    0x16bdcc520cb49ca220c20,
    0x153d696a0ce61c8228c20,
    0x16b9ec428cb3a4a219020,
    0x152de9434ce3b08219420 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_1 : Array Nat := #[ 0x1439676a8cf6246229020,
    0x142dc7534cf4b06221420,
    0x16a9067b98b49c4520c20,
    0x1535067ad2e61c4428c20,
    0x16a14673d8b3a44519020,
    0x1521a65bd2e3b04419420,
    0x14354672cef6244329020,
    0x1429a65b8ef4b04321420,
    0x17b98d5a547418a418440,
    0x17ad2a731a74188518440,
    0x173d8d59d09518a320440,
    0x15bd2a71d0c6988328440,
    0x172ce87b1a95186520440,
    0x15b8e87a54c6986428440,
    0x17b58e5256641ca410460,
    0x17a92b6b1c641c8510460 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_2 : Array Nat := #[ 0x17358f41d66524a310480,
    0x15a92f41dc66b083104a0,
    0x1720eb6b1e65246510480,
    0x15a0ee525e66b064104a0,
    0x16bd8e5190959ca220460,
    0x153d2b6990c71c8228460,
    0x16b98f419475a4a218480,
    0x152d2f419a773082184a0,
    0x1438eb6994c7a46228480,
    0x142cee519a97b062204a0,
    0x16a8c87b1c959c4520460,
    0x1534c87a56c71c4428460,
    0x16a0ca731e75a44518480,
    0x1520cd5a5e773044184a0,
    0x1434ca71d6c7a44328480,
    0x1428cd59dc97b043204a0 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_3 : Array Nat := #[ 0x17b1cd4ad47320a408c40,
    0x17a56a639a73208508c40,
    0x1731ed3ad09328a309040,
    0x15a5ea3b90c3348309440,
    0x171d6863da93286509040,
    0x159dc84bd4c3346409440,
    0x17b1ae4a9663a0a408860,
    0x17a54b635c63a08508860,
    0x1731af3a1664a8a308880,
    0x15a54f3a1c663483088a0,
    0x171d0b635e64a86508880,
    0x159d0e4a9e663464088a0,
    0x16b1ee329093aca209060,
    0x1525eb3350c3b88209460,
    0x16b1cf321474aca208c80,
    0x15256f321a76388208ca0 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_4 : Array Nat := #[ 0x141dcb3354c4bc6209480,
    0x141d6e329a963c62090a0,
    0x16994863dc93ac4509060,
    0x1519a84bd6c3b84409460,
    0x16990a639e74ac4508c80,
    0x15190d4ade76384408ca0,
    0x1419aa3b96c4bc4309480,
    0x14194d3adc963c43090a0,
    0x163dcd49ccb520a120c40,
    0x14bd6a61cce6a08128c40,
    0x1639ed3a4cb428a119040,
    0x14adea3b0ce4348119440,
    0x13b968624cf6a86129040,
    0x13adc84b0cf5346121440,
    0x163dae498ea5a0a120860,
    0x14bd4b618ed7208128860 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_5 : Array Nat := #[ 0x1639af399285a8a118880,
    0x14ad4f3998873481188a0,
    0x13b90b6192d7a86128880,
    0x13ad0e4998a7b461208a0,
    0x1635ee324ea42ca111060,
    0x14a9eb330ed4388111460,
    0x1635cf31d2852ca110c80,
    0x14a96f31d886b88110ca0,
    0x13a1cb3312d53c6111480,
    0x13a16e3258a6bc61110a0,
    0x133548624ef72c4129060,
    0x1329a84b0ef5b84121460,
    0x13350a61d2e7ac4128c80,
    0x13290d49d8b7b84120ca0,
    0x1321aa3b12e5bc4119480,
    0x13214d3a58b73c41190a0 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_6 : Array Nat := #[ 0x1624e67b9ab5202520c40,
    0x14b0e67ad4e6a02428c40,
    0x161d2673dab4282519040,
    0x149d865bd4e4342419440,
    0x13b12672d0f6a82329040,
    0x13a5865b90f5342321440,
    0x1624c77b5ca5a02520860,
    0x14b0c77a96d7202428860,
    0x161cc9735e85a82518880,
    0x149ccc5a9e873424188a0,
    0x13b0c97216d7a82328880,
    0x13a4cc5a1ca7b423208a0,
    0x1619276bdca42c2511060,
    0x14998753d6d4382411460,
    0x1618e96b9e852c2510c80,
    0x1498ec52de86b82410ca0 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock_7 : Array Nat := #[ 0x1399894396d53c2311480,
    0x13992c42dca6bc23110a0,
    0x1331276a90f72c2229060,
    0x1325875350f5b82221460,
    0x1330e96a14e7ac2228c80,
    0x1324ec521ab7b82220ca0,
    0x131d894354e5bc2219480,
    0x131d2c429ab73c22190a0 ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permutationBlock (b : Nat) : Array Nat :=
  if b < 4 then
    if b < 2 then
      if b < 1 then
        permutationBlock_0
      else
        permutationBlock_1
    else
      if b < 3 then
        permutationBlock_2
      else
        permutationBlock_3
  else
    if b < 6 then
      if b < 5 then
        permutationBlock_4
      else
        permutationBlock_5
    else
      if b < 7 then
        permutationBlock_6
      else
        permutationBlock_7
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def permCode (p : Nat) : Nat := ((permutationBlock (p / 16))[p % 16]?).getD 0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock0 (b : Nat) : Array (Nat × Nat) :=
  #[]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock1 (b : Nat) : Array (Nat × Nat) :=
  #[]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock2_0 : Array (Nat × Nat) := #[ (0x1fe30c9c837c6, 0x1),
    (0x1fe30edcc13c2, 0x1),
    (0x1ff30edcc12c2, 0x1),
    (0x1fdecee1013c2, 0x1),
    (0x1ffb8ed4412c2, 0x1),
    (0x1fe70c9c837c6, 0x1),
    (0x1fe30efcc13c2, 0x1),
    (0x1ff70edcc12c2, 0x1),
    (0x1f9e0cf9837c6, 0x1),
    (0x1ffb8efc412c2, 0x1),
    (0x1ff30edcc13c2, 0x1),
    (0x1fe70cfc837c6, 0x1),
    (0x1fdecefd013c2, 0x1),
    (0x1fd64cf9837c2, 0x1),
    (0x1fd20efdc17c2, 0x1),
    (0x1ffb8edc412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock2_1 : Array (Nat × Nat) := #[ (0x1fe20efdc13c2, 0x1),
    (0x1fd20efdc1fc2, 0x1),
    (0x1fe30cbc837c6, 0x1),
    (0x1fe70cbc837c6, 0x1),
    (0x1fe30edcc17c2, 0x1),
    (0x1fdecef1013c2, 0x1),
    (0x1fdeceed013c2, 0x1),
    (0x1fb60cf9837c6, 0x1),
    (0x1fe30ebc817c6, 0x1),
    (0x1fb60cfd837c6, 0x1),
    (0x1f920efdc17c2, 0x1),
    (0x1ff74e98817c2, 0x1),
    (0x1f9a0efdc17c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock2 (b : Nat) : Array (Nat × Nat) :=
  if b < 1 then
    certificateBlock2_0
  else
    certificateBlock2_1
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_0 : Array (Nat × Nat) := #[ (0x1fe30c988254412c2, 0x1),
    (0x1f820cf982d4412c2, 0x1),
    (0x1f820c7982d4412c2, 0x1),
    (0x1f928ce1025c412c2, 0x1),
    (0x1f9a8ce1025c412c2, 0x1),
    (0x1fc30cb88254412c2, 0x1),
    (0x1fe30cb88254412c2, 0x1),
    (0x1f630c9882d4412c2, 0x1),
    (0x1fe30c9882d4412c2, 0x1),
    (0x1fe30c9c8254412c2, 0x40000),
    (0x1fe70c988254412c2, 0x400da),
    (0x1fe30c98837c60040, 0x1003680000),
    (0x1feb0c988254412c2, 0x40118),
    (0x1fe30c98825c412c2, 0x40098),
    (0x1f020cf983fc60040, 0x1002840121),
    (0x1f820cf9827c412c2, 0x401f5) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_1 : Array (Nat × Nat) := #[ (0x1faa0cf98254412c2, 0x40233),
    (0x1f1208e107fce00c0, 0x10090001e9),
    (0x1fd20cf982d4412c2, 0x40209),
    (0x1f0208e107fce01c0, 0x1009000241),
    (0x1f920cf982d4412c2, 0x1),
    (0x1f0209e106dcc03c2, 0x400a8),
    (0x1f020cf983d4402c2, 0x40009),
    (0x1f820cf98354402c2, 0x4009b),
    (0x1f0208e107dcc03c2, 0x40128),
    (0x1f020df982d4402c2, 0x400c8),
    (0x1f820df98254402c2, 0x4011b),
    (0x1f420cf98294412c2, 0x1),
    (0x1fe30c988354402c2, 0x1),
    (0x1fe30d988254402c2, 0x1),
    (0x1f1208f106dcc13c2, 0x1),
    (0x1f520cf982d4412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_2 : Array (Nat × Nat) := #[ (0x1f7e6be1049880040, 0x1008f0019e),
    (0x1f0209ed26dcc0300, 0x40010),
    (0x1fe30c9c837c6, 0x1),
    (0x1fe30c9c837c612c2, 0x1),
    (0x1fe70c9c8254412c2, 0x40280),
    (0x1fe30c9c837c60040, 0x40280),
    (0x1fe3093c26dcc13c2, 0x1),
    (0x1fe30edcc13c2, 0x1),
    (0x1f2e2df982d4412c2, 0x1),
    (0x1fe70c98837c60040, 0x40280),
    (0x1fe30edcc6dcc13c2, 0x1),
    (0x1fe30c98837860040, 0x1),
    (0x1fe307e306dcc13c2, 0x1),
    (0x1e2e2cf982d4412c2, 0x1),
    (0x1fe70f9e8cf9837c6, 0x400030037000da),
    (0x1fe30c98837c600c0, 0x100d680000) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_3 : Array (Nat × Nat) := #[ (0x1fe30dbca254400c0, 0x100e600098),
    (0x1fe30fdecefdc13c2, 0x40181006000080),
    (0x1f820cf9837c602c0, 0x1010f000dd),
    (0x1f820efdc12c20780, 0x10125401dd),
    (0x1ffb0c988254412c2, 0x100e1803b0),
    (0x1fe00c988254412c2, 0x1),
    (0x1c988254412c201ce, 0x1),
    (0x1ffa0cf98254412c2, 0x10125404e3),
    (0x1fe30c980254412c2, 0x1),
    (0x1cf98254412c207de, 0x1),
    (0x1ff30edcc12c2, 0x1),
    (0x1feb0dbca254412c2, 0x1),
    (0x1fd64ef982d4412c2, 0x1),
    (0x1feb0c98825c412c2, 0x40518),
    (0x1f020cfd83fc60040, 0x40521),
    (0x1ff30edcc6dcc12c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_4 : Array (Nat × Nat) := #[ (0x1fe30dbca25c412c2, 0x1),
    (0x1f3e29e106dcc13c2, 0x1),
    (0x1f060cf983fc60040, 0x40521),
    (0x1fe30edcc13c212c2, 0x1),
    (0x1f020cf983f860040, 0x1),
    (0x1ff307f306dcc12c2, 0x1),
    (0x1dd64cf98254412c2, 0x1),
    (0x1dd64cf982d4412c2, 0x1),
    (0x1ffb8ff74edcc12c2, 0x40100008180200),
    (0x1f0209fd26dcc03c0, 0x1017240129),
    (0x1f020bfd649c807c0, 0x10187c023f),
    (0x1fef0c988254412c2, 0x100e60035a),
    (0x1f020cf983fc602c0, 0x101ab40121),
    (0x1f020bfd6498807c0, 0x1012f4023f),
    (0x1ffa0cf982d4412c2, 0x1012540660),
    (0x1fe30c988254412c0, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_5 : Array (Nat × Nat) := #[ (0x1cf982d4412c20fde, 0x1),
    (0x1fe30c988374400c2, 0x401f2),
    (0x1fe30db88254400c2, 0x40230),
    (0x1f020be1049c807c6, 0x4019e),
    (0x1f020be50498807c6, 0x4023c),
    (0x1fdecee1013c2, 0x1),
    (0x1f820dfda27c412c2, 0x1),
    (0x1fdecee106dcc13c2, 0x1),
    (0x1faa0cf9827c412c2, 0x40718),
    (0x1f1208ed07fce00c0, 0x40720),
    (0x1f820efdc17c212c2, 0x1),
    (0x1ffb8ed4412c2, 0x1),
    (0x1fef2db88254412c2, 0x1),
    (0x1fdecef106dcc12c2, 0x1),
    (0x1f1e08e107fce00c0, 0x40720),
    (0x1ffb8ed442d4412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_6 : Array (Nat × Nat) := #[ (0x1f1208e107f0e00c0, 0x1),
    (0x1ffb83fb82d4412c2, 0x1),
    (0x1db74c988254412c2, 0x1),
    (0x1cf983fb82d4412c2, 0x1),
    (0x1f820dfda254402c0, 0x101ecc01f5),
    (0x1fae0cf98254412c2, 0x101ecc043c),
    (0x1f020dfda2d4402c0, 0x1021200239),
    (0x1f0208e107fce03c0, 0x101f000241),
    (0x1fd60cf982d4412c2, 0x101e2405f2),
    (0x1f060be5049880786, 0x4023c),
    (0x1fd20efdc2d4412c2, 0x1),
    (0x1f1e08fd06dcc13c2, 0x408a0),
    (0x1f1e08e107fce01c0, 0x408a0),
    (0x1f020efdc1fc212c2, 0x1),
    (0x1f0208e107e0e01c0, 0x1),
    (0x1ffb837b8254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_7 : Array (Nat × Nat) := #[ (0x1c98837b8254412c2, 0x1),
    (0x1cf9837b8254412c2, 0x1),
    (0x1f2e0cf982d4412c2, 0x10212006ad),
    (0x1f9a8ce9025c412c2, 0x1),
    (0x1f9a8ce1037c600c0, 0x1003700902),
    (0x1f0209fd26dcc0340, 0x1027240129),
    (0x1fc20af546dcc13c2, 0x40181),
    (0x1fd20af546dcc12c2, 0x40209),
    (0x1fe30cbc8254412c2, 0x40900),
    (0x1f960cf982d4412c2, 0x409f2),
    (0x1f9a8ce1035c402c2, 0x401f4),
    (0x1fe30db88254402c2, 0x40230),
    (0x1f420cd882b5412c2, 0x1),
    (0x1f1608f506dcc13c2, 0x1),
    (0x1f020cf983fc600c0, 0x1028840121),
    (0x1fe30c98827c412c2, 0x40a18) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_8 : Array (Nat × Nat) := #[ (0x1f2e29e106dcc13c2, 0x400a8),
    (0x1fe30cf88254412c2, 0x1),
    (0x1f564ef982d4412c2, 0x40103),
    (0x1f9a0cf982d4412c2, 0x1),
    (0x1fbeade1025c412c2, 0x1),
    (0x1f8a0cf982d4412c2, 0x1),
    (0x1fa20cf9825c412c2, 0x40199),
    (0x1f820cf982d4413c2, 0x1),
    (0x1fe30d9882d4412c2, 0x1),
    (0x1fb20cf98254412c2, 0x1),
    (0x1fe30e9882d4412c2, 0x1),
    (0x1fc20cf9825c412c2, 0x1),
    (0x1fe30cb882d4412c2, 0x1),
    (0x1fe30cb8825c412c2, 0x40098),
    (0x1fe30cd882d4412c2, 0x1),
    (0x1f9a8cf9025c412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_9 : Array (Nat × Nat) := #[ (0x1feb0cb88254412c2, 0x40118),
    (0x1fe70cbc8254412c2, 0x40980),
    (0x1fc20cb982d4412c2, 0x1),
    (0x1f8a0cf982dc412c2, 0x1),
    (0x1fe70cb88254412c2, 0x40a5a),
    (0x1f2208f106dcc13c2, 0x400a9),
    (0x1f860cf982d4412c2, 0x402da),
    (0x1fe30cd8825c412c2, 0x40318),
    (0x1ff30cb88254412c2, 0x40390),
    (0x1fe10c988254412c2, 0x1),
    (0x1f820ef982d4412c2, 0x40103),
    (0x1f820cfd82d4412c2, 0x4055d),
    (0x1f820cf983fc60040, 0x100b68055d),
    (0x1faa0cf982d4412c2, 0x40ae0),
    (0x1f1208f107fce00c0, 0x102ba00ae9),
    (0x1f1e08f106dcc13c2, 0x40ae8) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_10 : Array (Nat × Nat) := #[ (0x1f0608e107fce01c0, 0x1009000aa3),
    (0x1f3208f106dcc13c2, 0x402c9),
    (0x1f0209fd26dcc0300, 0x100b240129),
    (0x1f1608f106dcc13c2, 0x1),
    (0x1f120cf982d4413c2, 0x1),
    (0x1f1208f106ccc13c2, 0x1),
    (0x1f1208ed06dcc13c2, 0x401e9),
    (0x1fd20c7982d4412c2, 0x40209),
    (0x1f7e6be1049c80040, 0x40a9e),
    (0x1f7e6be5049880040, 0x40a9e),
    (0x1f0208e107ece01c0, 0x1),
    (0x1f1209ed26dcc0300, 0x10004000d1),
    (0x1f920c7982d4412c2, 0x1),
    (0x1d564cf982d4412c2, 0x1),
    (0x1fe30edcc5bca37c6, 0x40080),
    (0x1f0209ed26dcc03c0, 0x40430) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_11 : Array (Nat × Nat) := #[ (0x1f020efdc1ac20780, 0x102c480221),
    (0x1f7a0cf982d4412c2, 0x40b60),
    (0x1f0209ed26dcc0340, 0x40910),
    (0x1f1a0cf982d4412c2, 0x1),
    (0x1f9a8cf1025c412c2, 0x1),
    (0x1fe004988254412c2, 0x1),
    (0x1f520cf98284412c2, 0x1),
    (0x1f060be10498807c6, 0x1),
    (0x1f0e08ed06dcc13c2, 0x1),
    (0x1f060be50498807c6, 0x4023c),
    (0x1faa0cf982fc412c2, 0x40898),
    (0x1ffb8e5442d4412c2, 0x40200),
    (0x1fdecee1013c212c2, 0x1),
    (0x1f560cf982d4412c2, 0x406e9),
    (0x1fe3092c26dcc13c2, 0x40030),
    (0x1f564cf983ac212c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_12 : Array (Nat × Nat) := #[ (0x1f160cf982d4412c2, 0x40a39),
    (0x1f7a6be1049880040, 0x1),
    (0x1f0209ed26ccc0300, 0x1),
    (0x1fe307f306dcc12c2, 0x1),
    (0x1fe30edcc6ccc12c2, 0x1),
    (0x1ffb87f746dcc12c2, 0x1),
    (0x1c798254412c20fde, 0x1),
    (0x1fe307fb86d4412c2, 0x1),
    (0x1f0e08e107fce01c0, 0x1009000721),
    (0x1f0208e107e4e01c0, 0x1),
    (0x1ffb8ed446d4412c2, 0x1),
    (0x1ffb87fb86d4412c2, 0x1),
    (0x1f620bfd64f880040, 0x101cf00741),
    (0x1f7b83fb8254412c2, 0x1),
    (0x1fe20bfd649880040, 0x101f6c081e),
    (0x1f7e6bf9049880040, 0x1012f00b1e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_13 : Array (Nat × Nat) := #[ (0x1fe30cf8837c60040, 0x101af00404),
    (0x1f3209ed26dcc0300, 0x100b240290),
    (0x1f564cf98284012c2, 0x40033),
    (0x1fe30bfc649880040, 0x100f68031e),
    (0x1f0203866254412c2, 0x1),
    (0x1eef2cb88254412c2, 0x1),
    (0x1fe30cb8837c60040, 0x1029680900),
    (0x1f520cf98294412c2, 0x1),
    (0x1f9a8ce9825cc12c2, 0x1),
    (0x1ff74fbeacf9837c6, 0x40b80),
    (0x1fe30f9a8efdc17c2, 0x401dd),
    (0x1af546dcc3fb812c2, 0x1),
    (0x1fb60cf98254412c2, 0x40b80),
    (0x1f020af5459ca0780, 0x40c25),
    (0x1fe30f988254402c2, 0x1),
    (0x1fe30ddc8254402c2, 0x40c18) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_14 : Array (Nat × Nat) := #[ (0x1f9a8de10754402c2, 0x1),
    (0x1f9a8af546cc012c2, 0x40be2),
    (0x1f020af545bca0780, 0x40b86),
    (0x1af545bca0f9807c6, 0x1),
    (0x1f020afd45bca0780, 0x1032180127),
    (0x1f020af54584a0780, 0x1),
    (0x1fb60cf9837c6, 0x1),
    (0x1f7a0af545bca0780, 0x1032180cb2),
    (0x1fe30bbc26dcc12c2, 0x1),
    (0x1f7a0af545bca37c6, 0x1),
    (0x1fb60cf9837c612c2, 0x1),
    (0x1f020bf906dcc02c2, 0x40b89),
    (0x1f9a88e107f4400c2, 0x40c20),
    (0x1fc20cf9837c600c0, 0x102e080a77),
    (0x1af5449881fda07c6, 0x1),
    (0x1fc20cf986d4412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_15 : Array (Nat × Nat) := #[ (0x1fce0cf982dc412c2, 0x40cbe),
    (0x1fb60cfd8254412c2, 0x40c80),
    (0x1cf982f5412c20fce, 0x1),
    (0x1f8a0c7182dc412c2, 0x1),
    (0x1fe30cb8827c412c2, 0x40a18),
    (0x1f8a0cf9827c412c2, 0x40d18),
    (0x1f1608e107fce00c0, 0x1009000d20),
    (0x1f920cf9827c412c2, 0x40def),
    (0x1fba0cf98254412c2, 0x407cb),
    (0x1f5208e107fce00c0, 0x101f600deb),
    (0x1fd20cf986d4412c2, 0x40209),
    (0x1fda0cf982dc412c2, 0x4078f),
    (0x1f9a8af106d4412c2, 0x1),
    (0x1f520cf982dc412c2, 0x1),
    (0x1f020dfda2f4400c0, 0x1036840239),
    (0x1fbeade10254400c0, 0x101ec80198) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3_16 : Array (Nat × Nat) := #[ (0x1f9a8cf106d4412c2, 0x1),
    (0x1f9a0cf982dc412c2, 0x1),
    (0x1fc20cf986dcc17c2, 0x40d02),
    (0x1f460cf982dc412c2, 0x40a3b),
    (0x1fc20cf982dc412c2, 0x1),
    (0x1fce0cb98254412c2, 0x40c5a),
    (0x1f8a0cf182dc412c2, 0x1),
    (0x1fe20cb98254412c2, 0x1),
    (0x1fe20cb88254412c2, 0x1),
    (0x1fc20cb88254412c2, 0x1),
    (0x1ffb8ef54edcc12c2, 0x40200),
    (0x1f020dfda2dc402c0, 0x1038c00239),
    (0x1f9a0cf9827c412c2, 0x40e18),
    (0x1fe20c998254412c2, 0x1),
    (0x1fe20cf88254412c2, 0x1),
    (0x1f1a8ce982dcc12c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock3 (b : Nat) : Array (Nat × Nat) :=
  if b < 8 then
    if b < 4 then
      if b < 2 then
        if b < 1 then
          certificateBlock3_0
        else
          certificateBlock3_1
      else
        if b < 3 then
          certificateBlock3_2
        else
          certificateBlock3_3
    else
      if b < 6 then
        if b < 5 then
          certificateBlock3_4
        else
          certificateBlock3_5
      else
        if b < 7 then
          certificateBlock3_6
        else
          certificateBlock3_7
  else
    if b < 12 then
      if b < 10 then
        if b < 9 then
          certificateBlock3_8
        else
          certificateBlock3_9
      else
        if b < 11 then
          certificateBlock3_10
        else
          certificateBlock3_11
    else
      if b < 14 then
        if b < 13 then
          certificateBlock3_12
        else
          certificateBlock3_13
      else
        if b < 15 then
          certificateBlock3_14
        else
          if b < 16 then
            certificateBlock3_15
          else
            certificateBlock3_16
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_0 : Array (Nat × Nat) := #[ (0x1f0608e104988254412c2, 0x4005a),
    (0x1f0208e10498837c60040, 0x4005a0016c005e),
    (0x1f0208e104988254412c2, 0x1),
    (0x1f0209e104988254402c2, 0x40048),
    (0x1fe30c988254412c2, 0x1),
    (0x1f2e29e104988254412c2, 0x1),
    (0x1f0608e504988254412c2, 0x400bc),
    (0x1f0608e10498837c60040, 0x1002f000be),
    (0x1f0208e106dcc13c212c2, 0x1),
    (0x1f0208e10498837860040, 0x1),
    (0x1fe307e304988254412c2, 0x1),
    (0x18e107e304988254412c2, 0x1),
    (0x1f2e29e104988254402c2, 0x1),
    (0x1e0209e105988254402c2, 0x40131),
    (0x1f0608e10498837860040, 0x4013c004f8005a),
    (0x1f0208e106ccc13c212c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_1 : Array (Nat × Nat) := #[ (0x1f0208e1039a8254412c2, 0x1),
    (0x19ed27e304988254412c2, 0x1),
    (0x1f0209cd24988254402c2, 0x1),
    (0x1f2209cd24988254412c2, 0x40049),
    (0x1f0209e1049c8254402c2, 0x1008c001c7),
    (0x1f0209e504988254402c2, 0x100d2002dd),
    (0x1f0609e104988254402c2, 0x10012003da),
    (0x1f020ae10498817c60040, 0x403f200bd401f1),
    (0x1f564ae10498812c20040, 0x100c300206),
    (0x1f564ae10498817c612c2, 0x1),
    (0x1f2629e104988254402c2, 0x40048),
    (0x1f0209ed24b88254400c2, 0x1),
    (0x1fe30c988254412c202c2, 0x1),
    (0x1f0209e104b88254402c2, 0x101120004b),
    (0x1f2209e104988254402c2, 0x1001200049),
    (0x1f0208e106dcc13c20040, 0x1011000441) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_2 : Array (Nat × Nat) := #[ (0x1fe30cf98c988254412c2, 0x1),
    (0x1f0e29e104988254402c2, 0x40048),
    (0x1f2e29e104988254400c2, 0x1),
    (0x1f9a8ce104e10254412c2, 0x1),
    (0x1fe30c988254412c20040, 0x40580014000480),
    (0x1fe30c98837c6254412c2, 0x40580),
    (0x1f020cf982d4412c202c2, 0x1),
    (0x1f020cf982d4412c20040, 0x4070001a240609),
    (0x1fe30dbcac988254412c2, 0x40712),
    (0x1f820cf98254412c202c2, 0x1),
    (0x1f0208e106dcc13c203c2, 0x1),
    (0x1f1208e106dcc12c200c0, 0x40880020200788),
    (0x1fef2fe30c988254412c2, 0x40890),
    (0x1fe30c988254412c200c2, 0x1),
    (0x1f0208e50498837c607c6, 0x1),
    (0x1f0208e106dcc13c201c0, 0x40980024800921) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_3 : Array (Nat × Nat) := #[ (0x1ffb8fe30c988254412c2, 0x409da),
    (0x1fe3092c24988254400c2, 0x1),
    (0x1f0608e10498837c60786, 0x1),
    (0x1f9a8ce105bca254412c2, 0x1),
    (0x1f0209ed24b88254402c2, 0x1),
    (0x1f0208e105bca25c400c0, 0x1028e00a39),
    (0x1fe3092c24988254402c2, 0x1),
    (0x1f0209e104988254403c2, 0x102a000548),
    (0x1f0209f104988254402c2, 0x102c2004c8),
    (0x1f1209e104988254402c2, 0x102e200548),
    (0x1f020ce1037c609880040, 0x1016080bbc02cf00a9e),
    (0x1f0208e105988254403c2, 0x103000064a),
    (0x1f0209e104d88254402c2, 0x10321806c8),
    (0x1f4209e104988254402c2, 0x1034180648),
    (0x1f0208e1077c609880040, 0x101c040d3c032f00c1e),
    (0x1f020ae104988154412c2, 0x1000300db7) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_4 : Array (Nat × Nat) := #[ (0x1f020ae105988254402c2, 0x1038300264),
    (0x1f020be104988254402c2, 0x103a300360),
    (0x1f1208e10488837c60040, 0x40eda0396c0dbe),
    (0x1f2629e104988254412c2, 0x40048),
    (0x1f2209e104988254412c2, 0x1001200049),
    (0x1f020de105988254402c2, 0x103a080a49),
    (0x1f0208e105bca250400c0, 0x40ee403b940058),
    (0x1f020ce1039a8254412c2, 0x40002),
    (0x1f820cf982d4412c2, 0x1),
    (0x1f2e29e105988254402c2, 0x1),
    (0x1f2209ed24b88254412c2, 0x1),
    (0x1f0209e105988354402c2, 0x40f1b),
    (0x1f0608e50498837c60040, 0x10016c005a03c78013c),
    (0x1f1208e106dcc13c212c2, 0x1),
    (0x1fe30c9887e30254412c2, 0x1),
    (0x1fe30c9884f98254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_5 : Array (Nat × Nat) := #[ (0x1f0208e106dcc134212c2, 0x40040),
    (0x1f0208e106dcc13c200c0, 0x103e800fa1),
    (0x1f0608e10498837c607c6, 0x1),
    (0x1fe30c9885bca254412c2, 0x1),
    (0x1f0208e106dcc13c202c2, 0x1),
    (0x1f0208e106dcc12c201c0, 0x1026000808020240040),
    (0x1f0208e10498837c60786, 0x1),
    (0x1f020cf983fc6254412c2, 0x40700),
    (0x1f0208e106dcc12c203c2, 0x40040),
    (0x1f2209ed24988254402c2, 0x1),
    (0x1f0208e105bca254400c0, 0x4034c00d340058),
    (0x1f0209e105988254402c2, 0x400b1),
    (0x1f2209c104988254412c2, 0x40049),
    (0x1f020ce105988254402c2, 0x40462),
    (0x1f2208ed24988254412c2, 0x40049),
    (0x1fe307ef24988254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_6 : Array (Nat × Nat) := #[ (0x1fef27e304988254412c2, 0x1),
    (0x1f0208e104988378607c6, 0x1),
    (0x1f1a08e10498837c60040, 0x104010083c01ef40fbe),
    (0x1f0208e107fce01800040, 0x4100404014089e0227c0980),
    (0x1f0208e106dcc130212c2, 0x40040),
    (0x1f0208e106dcc12c20300, 0x1042000490000440040),
    (0x1f0208e1049883fc60040, 0x101c00055a0196c065e),
    (0x1f8208e10498837c60040, 0x10160c04da01b6c06de),
    (0x1f020cf9837c608000040, 0x4058301c0005da01cf0108c),
    (0x1f0a08e10498837c60040, 0x4035a0090c045e),
    (0x1f0208e105b8a254400c0, 0x100b3002cd),
    (0x1f0208e106d8c13c20040, 0x403c000f040040),
    (0x1f524ae10498812c20040, 0x4000c00a300186),
    (0x1f0208e106dcc13820040, 0x40da60369c0040),
    (0x1f564ae10498812820040, 0x40e9203848000c),
    (0x1f0208e106dcc110002c2, 0x40b08042040040) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_7 : Array (Nat × Nat) := #[ (0x1f020cf982d0412c20040, 0x101c000ae0031800009),
    (0x1f020cf982d4412820040, 0x101c000b95034540009),
    (0x1fe30c988254412820040, 0x1016000c9202c480000),
    (0x1f0e28ed24988254412c2, 0x1),
    (0x1f0e29ed24988254402c2, 0x1),
    (0x1fe30f9a8cb98254412c2, 0x40000),
    (0x1f0e08e104988254412c2, 0x100d30035a),
    (0x1f0208e105b88254400c2, 0x100b4002d1),
    (0x1f2e29ed24988254400c2, 0x1001240048),
    (0x1fe30f9a8cf98254412c2, 0x40003000080000),
    (0x1f2208e504988254412c2, 0x100124045b),
    (0x1f0a08e504988254412c2, 0x1008d00243),
    (0x1f0209e905988254402c2, 0x1028c40353),
    (0x1f0608e5049c8254412c2, 0x40f1e),
    (0x1fe30c9c8254412c2, 0x40b6002c481198046001100),
    (0x1fe30c9c8254412c20040, 0x4128004800000002d800b12) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_8 : Array (Nat × Nat) := #[ (0x1fe30c9c8c988254412c2, 0x4135a),
    (0x1fe70c988254412c2, 0x40ce00324814600504813da),
    (0x1fe70c988254412c20040, 0x41480000001200033800c92),
    (0x1fe70fe30c988254412c2, 0x4155a),
    (0x1fe30c98837c60040, 0x105568148004f68135a04a001100059681580),
    (0x1fe30c98837c612c20040, 0x41412046001692),
    (0x1f2e2cf982d4412c202c2, 0x1000240589),
    (0x1fd64f2e2cf982d4412c2, 0x101a24181b05e241742),
    (0x1f820cf9837c6254402c2, 0x40583),
    (0x1ffb8f2e2cf982d4412c2, 0x101e5419950645418c8),
    (0x1fe30c98837c6254400c2, 0x40580),
    (0x1fe3092c24988254400c0, 0x41800060181a3001ac006b6),
    (0x1ffcefe30c988254412c2, 0x106c001a80),
    (0x1f820cf98254412c207c6, 0x1),
    (0x1f0208e106dcc13c201c2, 0x1),
    (0x1f820cf98254412c20780, 0x41980066601b8001e000798) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_9 : Array (Nat × Nat) := #[ (0x1fff6fe30c988254412c2, 0x1072101c00),
    (0x1fe30c988254412c201c6, 0x1),
    (0x1f0208e1049c837c601c6, 0x1),
    (0x1fe30db8ac988254412c2, 0x1),
    (0x1f1208e106dcc12c200c2, 0x1),
    (0x1feb2fe30c988254412c2, 0x1),
    (0x1f020cf982d4412c20042, 0x1),
    (0x1f020cf983fc62d4402c2, 0x40700),
    (0x1f1208e106dcc10c202c2, 0x40010),
    (0x1f020dfdacf982d4402c2, 0x40892),
    (0x1fe30a5444988124200c2, 0x40006),
    (0x1e020cf982d4412c202c2, 0x41680),
    (0x1feb0c988254412c2, 0x40c72034101e60076001d18),
    (0x1f020cfd82d4412c20040, 0x41f0007a240009031800d15),
    (0x1feb0fe30c988254412c2, 0x41fcc),
    (0x1fe30c98825c412c2, 0x40af202e1020f2080001398) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_10 : Array (Nat × Nat) := #[ (0x1f060cf982d4412c20040, 0x42100000241e8902b800b95),
    (0x1fe30c988254413c212c2, 0x42180),
    (0x1f020cf983fc60040, 0x108684210004e841fdd07c001d2108b742200),
    (0x1f020cf983fc612c20040, 0x4200907624232d),
    (0x1f020cf983fc61ac20040, 0x42092078b423ad),
    (0x1fae2cf98254412c202c2, 0x10000c0715),
    (0x1f3e28e106dcc13c203c2, 0x1001000709),
    (0x1ffb8fd64cf982d4412c2, 0x102400256c093802403),
    (0x1fe30dbcac988254400c2, 0x40712),
    (0x1fd64fae2cf98254412c2, 0x10120c181b0600c173c),
    (0x1f0209fd28e106dcc03c2, 0x40708),
    (0x1fe30c988254412c200c0, 0x4180005e002580012000680),
    (0x1f020cf982d4412c20fc6, 0x1),
    (0x1ffb8fae2cf98254412c2, 0x10200026c209854241b),
    (0x1fe30b7c64988254400c2, 0x40704),
    (0x1f0208e50498837c607c0, 0x4268009408273c020f40941) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_11 : Array (Nat × Nat) := #[ (0x1fffafe30c988254412c2, 0x10a0482798),
    (0x1fe30a544498812c201c6, 0x1),
    (0x1f1208e106dcc12c200cc, 0x1),
    (0x1f820cf98254417c612c2, 0x1),
    (0x1fe72fe30c988254412c2, 0x1),
    (0x1fe30c988254412c20042, 0x1),
    (0x1f820dfdacf98254402c2, 0x4088c),
    (0x1fe30c9882544124200c2, 0x40000),
    (0x1e820cf98254412c202c2, 0x42318),
    (0x1f820e820cf98254402c2, 0x423e3),
    (0x1feb8fe30c988254412c2, 0x1),
    (0x1f020cf9825441ac20042, 0x1),
    (0x1f020cf982d441fc612c2, 0x1),
    (0x1f0208e107fce6dcc03c2, 0x40980),
    (0x1fe3092424988254400c2, 0x40030),
    (0x1f0208e106dcc11c203c2, 0x40040) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_12 : Array (Nat × Nat) := #[ (0x1f1208e106dcc120200c0, 0x10220029100a2400010),
    (0x1f1208e106d0c12c200c0, 0x1022002a600a7840010),
    (0x1f820cf9827c412c2, 0x429f20a20c2bf50ac002af5),
    (0x1f1208ed06dcc12c200c0, 0x42c800b02000100a7842890),
    (0x1f820cf98254417c212c2, 0x42d00),
    (0x1faa0cf98254412c2, 0x42a6c0a40c2ee00b80c2db3),
    (0x1f1e08e106dcc12c200c0, 0x42f00000402c080a9802910),
    (0x1fe30db88c988254412c2, 0x42fe0),
    (0x1f1208e107fce00c0, 0x10bfc02f000b7002d200b2002ae90c3c03000),
    (0x1f1208e107fce12c200c0, 0x42e100ac203128),
    (0x1f1208e107fce6dcc00c0, 0x42ee80afa431f0),
    (0x1fef2c988254412c200c2, 0x1000000890),
    (0x1f7e68e50498837c607c6, 0x10016c08a1),
    (0x1ff74fef2c988254412c2, 0x101400321c0c81018da),
    (0x1f0208e507fce498807c6, 0x4089f),
    (0x1f820cf98254412c202c0, 0x432000640032800140c0780) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_13 : Array (Nat × Nat) := #[ (0x1f0208f106dcc12c20fce, 0x1),
    (0x1ffb8fef2c988254412c2, 0x10180033da0cc482418),
    (0x1f0608e107fce49880786, 0x4089e),
    (0x1f0208e106dcc13c203c0, 0x424800ce003420024840640),
    (0x1f820cf98254412c207da, 0x1),
    (0x1fe30c988254413c612c2, 0x1),
    (0x1fe30c9cac988254412c2, 0x1),
    (0x1ec30c988254412c200c2, 0x43118),
    (0x1fe30ec30c988254400c2, 0x431e0),
    (0x1f0208f106dcc1fce12c2, 0x1),
    (0x1fe30dbb8c988254412c2, 0x1),
    (0x1f0208e1049c831c607c6, 0x4005e),
    (0x1f020bfd68e50498807c6, 0x40982),
    (0x1f0608e10498831c60786, 0x4005a),
    (0x1fe3092004988254400c2, 0x10a4002906026400030),
    (0x1f0208e106c0c13c201c0, 0x10260034e00d3840040) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_14 : Array (Nat × Nat) := #[ (0x1fd20cf982d4412c2, 0x434c20a46c2e920d4002d89),
    (0x1f1e08e106dcc13c201c0, 0x436000010035800d3802910),
    (0x1f020cf982d441fc212c2, 0x43680),
    (0x1f0208e107fce01c0, 0x10da8436000b70036a00d8042dc10df003700),
    (0x1f0208e107fce13c201c0, 0x435200d4843840),
    (0x1f0208e107fce37c601c0, 0x42ea20ba8c38c0),
    (0x1f020cf982d4412c202c0, 0x43300098003900018240815),
    (0x1f0208e106dcc13c20fce, 0x1),
    (0x1fef292c24988254400c2, 0x1000c00990),
    (0x1f7e68e10498837c60786, 0x1001680983),
    (0x1fe30a544498813c612c2, 0x1),
    (0x192c26c304988254400c2, 0x43830),
    (0x1fe306c304988254400c2, 0x438e0),
    (0x1f820cf98254417da12c2, 0x1),
    (0x1f9a8ce1025c412c2, 0x1),
    (0x1f564ae1049c812c20040, 0x1006183986000300e12) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_15 : Array (Nat × Nat) := #[ (0x1f9a8ce10254413c212c2, 0x1),
    (0x1fe30cb88254412c2, 0x1),
    (0x1f564ae50498812c20040, 0x100a30000c0e6180e92),
    (0x1fe30cb88c988254412c2, 0x1),
    (0x1fe30de30c988254412c2, 0x1),
    (0x1f2e29e1049c8254412c2, 0x40e60),
    (0x1f2e29e504988254412c2, 0x40ee0),
    (0x1f9a8f2e2cf982d4412c2, 0x10083c3a0f),
    (0x1f020cf985bca2d4402c2, 0x1),
    (0x1f2e29ed24b88254402c2, 0x10012c0dcc),
    (0x1fd64f9a8cf982d4412c2, 0x1028003ae0),
    (0x1f820cf985bca254402c2, 0x1),
    (0x1f1208e106dcc37c600c0, 0x408800eee03b51),
    (0x1f2e28e50498837c607c6, 0x4005b),
    (0x1f9a8ce10254412c200c0, 0x10e80005020f0080200),
    (0x1f9a8ce107fce254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_16 : Array (Nat × Nat) := #[ (0x1f020cf982d4412c200c2, 0x1),
    (0x1f020af544d8812c207c6, 0x1),
    (0x1f0208e106dcc13c20340, 0x10ea003ca0028840640),
    (0x1fe30dfdac988254412c2, 0x1),
    (0x1f420af54498812c203c6, 0x1),
    (0x1f020af54498816c200c2, 0x1),
    (0x1f820cf984b88254412c2, 0x1),
    (0x1f020af544d8817c612c2, 0x1),
    (0x1f0208e105bca25c400c2, 0x1),
    (0x1fe30cb98c988254412c2, 0x1),
    (0x1f2e29e10498825440042, 0x1),
    (0x1f0209c104b88254402c2, 0x103730004b),
    (0x1f564ae104988154412c2, 0x1),
    (0x1fe30c988254417c612c2, 0x1),
    (0x1fe30cbcac988254412c2, 0x1),
    (0x1f9a8ce10254412c200c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_17 : Array (Nat × Nat) := #[ (0x1fe30c98837c6254402c2, 0x40580),
    (0x1f020cf982d4410c202c2, 0x40009),
    (0x1fe30dbcac988254402c2, 0x40712),
    (0x1f9a8ce10254410c202c2, 0x40002),
    (0x1f1208e106dcc124200c0, 0x1022003d900f4280010),
    (0x1fe30ec30c988254402c2, 0x1),
    (0x1f0208e105b0a25c400c0, 0x43e5c0f9740058),
    (0x1f9a8ce1039a8254412c2, 0x1),
    (0x1f920cf982d4412c2, 0x1),
    (0x1f0e08e105bca25c400c0, 0x1001603e980f9700ee4),
    (0x1f020af544d8817c212c2, 0x1),
    (0x1f2a09ed24b88254412c2, 0x40ee7),
    (0x1fe30dbcacf98254412c2, 0x100c003f12),
    (0x1f0208e106dcc37c603c2, 0x1),
    (0x1f020cf982d4412c200c0, 0x10fc003f89018240309),
    (0x1f0208e106dcc13c207c6, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_18 : Array (Nat × Nat) := #[ (0x1f0208e105bca37c601c0, 0x409800ee803ba1),
    (0x1f2e28e10498837c60786, 0x4005a),
    (0x1f9a8ce10c988254412c2, 0x1),
    (0x1f564ae10498813c612c2, 0x1),
    (0x1f2209e104988254400c2, 0x1001200049),
    (0x1fe30a544498817c612c2, 0x1),
    (0x1f820cf984f98254412c2, 0x1),
    (0x1fe30b7c64988254402c2, 0x40704),
    (0x1fe3092424988254402c2, 0x40030),
    (0x1f0208e106dcc124201c0, 0x1026003d900f6440040),
    (0x1fe306c304988254402c2, 0x1),
    (0x1f9a8ce1049c8254412c2, 0x101408401e),
    (0x1f3209ed24988254412c2, 0x41190),
    (0x1f3e29e104988254412c2, 0x42010),
    (0x1f9a8ce10498837c60040, 0x4205a0476c401e),
    (0x1f2e29e104988254400c0, 0x440c8008c00236) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_19 : Array (Nat × Nat) := #[ (0x1fe30c988254412c207c6, 0x1),
    (0x1f9a8ce105b8a254412c2, 0x1),
    (0x1f9a8ce104b88254412c2, 0x1018084130),
    (0x1f6e29e104988254412c2, 0x41d8d),
    (0x1f1209ed24b88254412c2, 0x41409),
    (0x1f020cf9849883fc60040, 0x4143d0776c413f),
    (0x1f0209ed24b88254402c0, 0x441b000d2c0a45),
    (0x1fe30a544498812c207c6, 0x1),
    (0x1f820cf984bca254412c2, 0x1),
    (0x1fe30ce98c988254412c2, 0x1),
    (0x1f4609ed24b88254412c2, 0x442120f5943b24),
    (0x1f6609ed24988254412c2, 0x42e0d0f7843b9e),
    (0x1f1208e107fce254400c0, 0x10b9304263),
    (0x1f564ae10498812c207c6, 0x1),
    (0x1f9a8ce104bca254412c2, 0x1),
    (0x1faa09ed24b88254412c2, 0x42e030f79c3b98) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_20 : Array (Nat × Nat) := #[ (0x1f0208e107fce12c201c0, 0x10b8402e11),
    (0x1f5648e10498832c207c6, 0x1),
    (0x1f9a8ce104f98254412c2, 0x1),
    (0x1f4209ed24b88254412c2, 0x1),
    (0x1f6209ed24988254412c2, 0x1),
    (0x1fe30f9a8cf982d4412c2, 0x40080010080400),
    (0x1f0a08e105bca254400c0, 0x4034c10acc00b8),
    (0x1f1208e105bca254400c0, 0x102200083210d2c0470),
    (0x1fe30c988254410c202c2, 0x40000),
    (0x1fa209ed24b88254412c2, 0x1),
    (0x1f1a08e504988254412c2, 0x4430810cc807bd),
    (0x1f1e08e104988254412c2, 0x40808020c8083c),
    (0x1f6608e504988254412c2, 0x40806020c0093c),
    (0x1fe30c9882d4412c2, 0x1),
    (0x1f2e29e104b88254412c2, 0x1),
    (0x1f8209ed24b88254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_21 : Array (Nat × Nat) := #[ (0x1f0209e104b88254400c2, 0x100f20004b),
    (0x1f0a08e5049c8254412c2, 0x1008d043bf),
    (0x1f2608e504988254412c2, 0x100d240a3c),
    (0x1f2208e50498837c60040, 0x1028f043c1),
    (0x1f0608e106dcc13c212c2, 0x1),
    (0x1f0e08e504988254412c2, 0x10e6d042bc),
    (0x1f0a08e50498837c60040, 0x110af043bf),
    (0x1f4208e106dcc13c212c2, 0x1),
    (0x1f0e08e10498837c60040, 0x110af00a3e),
    (0x1fe30cb884b88254412c2, 0x1),
    (0x1f0a08e10498837860040, 0x1),
    (0x1fe307e304b88254412c2, 0x1),
    (0x1d5648e504988254412c2, 0x1),
    (0x1f4209cd24988254412c2, 0x1),
    (0x1f2e28ed24b88254412c2, 0x1),
    (0x1fe30f9a8cf9825c412c2, 0x40201008000680) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_22 : Array (Nat × Nat) := #[ (0x1f8208e105bca254400c0, 0x444b8111940276),
    (0x1f8208e504988254412c2, 0x10140c06db),
    (0x1f8a8ce105bca254412c2, 0x1),
    (0x1feb0f9a8cf98254412c2, 0x4030300c080600),
    (0x1f0208e105bca2d4400c0, 0x445d0115ac0370),
    (0x1f0208e10498837c60340, 0x444bc00dcc035e),
    (0x1f4209e104988254412c2, 0x1018340648),
    (0x1f8209ed24f98254412c2, 0x1),
    (0x1f0608e105bca254400c0, 0x4034c0e6d40458),
    (0x1f2208e105bca254400c0, 0x440cc119340240),
    (0x1f4208e105bca254400c0, 0x10e81c3c4c11b3406d8),
    (0x1f0209ed249c8254402c0, 0x447b100d2c4757),
    (0x1f0208e106fcc12c20340, 0x10ea684890120440640),
    (0x1f4208ed04988254412c2, 0x4050d11b344473),
    (0x1f3608e104988254412c2, 0x43c100f12444bc),
    (0x1f6209e104988254412c2, 0x44813019200361) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_23 : Array (Nat × Nat) := #[ (0x1fa608e504988254412c2, 0x44885112d83cbc),
    (0x1f0209e924b88254402c2, 0x4004b),
    (0x1f020ee30c988254402c2, 0x1),
    (0x1ee30c988254412c202c2, 0x1),
    (0x1fa30cf98c988254412c2, 0x1),
    (0x1f2629e104988254400c2, 0x40048),
    (0x1f2229e104988254412c2, 0x40048),
    (0x1f2208e524988254412c2, 0x40049),
    (0x1f0209e524b88254402c2, 0x4004b),
    (0x1f3208e104988254412c2, 0x10124004c9),
    (0x1f2208e105b88254400c2, 0x100d40494d),
    (0x1f0208e105b8a25c400c0, 0x44950125440058),
    (0x1f2a08e904b88254412c2, 0x1028c00a32),
    (0x1fa20cf984b88254412c2, 0x1),
    (0x1f0e08ed049c8254412c2, 0x1126c83e9e),
    (0x1f0e08e105bca254400c0, 0x449b203b900a38) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_24 : Array (Nat × Nat) := #[ (0x1f020af54498817c212c2, 0x1),
    (0x1f0208e105b0a254400c0, 0x1),
    (0x1f9a88e1039a8254412c2, 0x1),
    (0x1c9888e1039a8254412c2, 0x1),
    (0x1f0209ed24988254402c0, 0x440c900d2c0355),
    (0x1f0208e105fca254400c0, 0x10fc184a4c121340658),
    (0x1f4609e104988254412c2, 0x4480d01920455a),
    (0x1f8a08e504988254412c2, 0x44a03116c83fdb),
    (0x1ee3092c24988254402c2, 0x1),
    (0x1f9e8ce1049c8254412c2, 0x4209e),
    (0x1f8208e5049c8254412c2, 0x10140c4a9e),
    (0x1f8608e504988254412c2, 0x10480c4b3c),
    (0x1f8208e50498837c60040, 0x4148312cf04a9e),
    (0x1f2208e106dcc13c212c2, 0x4201102fc04001),
    (0x1f8608e10498837c60040, 0x4128312cf04b3e),
    (0x1fe30c9c849c8254412c2, 0x4131e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_25 : Array (Nat × Nat) := #[ (0x1f8208e10498837860040, 0x41583),
    (0x1fe307e3049c8254412c2, 0x4161e),
    (0x1b9a88e504988254412c2, 0x416bc),
    (0x1fe70f9e8cf98254412c2, 0x10120c0502014001700),
    (0x1f020c9888e1037c600c0, 0x105e004bdc013784bdd),
    (0x1f020dbca8e10254400c0, 0x1060004c4c131340558),
    (0x1f2208ed04988254412c2, 0x4004911934465b),
    (0x1f2e08e104988254412c2, 0x440c91033040da),
    (0x1fc209e104988254412c2, 0x44c1d130ac1a48),
    (0x1f0608e104988254412c0, 0x44cf2),
    (0x1c9888e10254412c20fce, 0x41b00),
    (0x1fba8ce104b88254412c2, 0x41e30),
    (0x1f220ce104b88254412c2, 0x1018084d30),
    (0x1f1208f104b88254412c2, 0x1136201ecb),
    (0x1f0208e5049883fc60040, 0x41f00136f04d3f),
    (0x1f0208e106fcc13c212c2, 0x41d91035c04121) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_26 : Array (Nat × Nat) := #[ (0x1f0608e1049883fc60040, 0x42100136f04dbe),
    (0x1f020edcc8e1013c212c2, 0x42180),
    (0x1f0208e1049883f860040, 0x42200),
    (0x1fe707e704988254412c2, 0x4229e),
    (0x18e107e704988254412c2, 0x4233c),
    (0x18e507e704988254412c2, 0x423bc),
    (0x1f2609e104988254412c2, 0x4004800d24475a),
    (0x1f2e08e504988254412c2, 0x440c911ed041bc),
    (0x1f5209e104988254412c2, 0x44c2512e4025c8),
    (0x1f820cf982d4412c20040, 0x44e0012c004d80),
    (0x1f820cf983fc62d4412c2, 0x44e00),
    (0x1f820cf982d4412c202c2, 0x1),
    (0x1f0208f106dcc13c203c2, 0x1),
    (0x1f1208f106dcc12c200c0, 0x44f0013a204e89),
    (0x1f820dfdacf982d4412c2, 0x44f0c),
    (0x1fe30c988a54412c200c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_27 : Array (Nat × Nat) := #[ (0x1f0208e5049c837c607c6, 0x1),
    (0x1f1208e106dcc13c201c0, 0x1140c00040024804f81),
    (0x1f820efdccf982d4412c2, 0x45054),
    (0x1fe30c98892c2254400c2, 0x1),
    (0x1f0608e50498837c60786, 0x1),
    (0x1f0208f106dcc13c20300, 0x1144005080004844d21),
    (0x1fd64f820cf982d4412c2, 0x45160),
    (0x1f1208e106dcc13c202c2, 0x1),
    (0x1f420af544d8812c20040, 0x110a18428b),
    (0x1f820cf985bca2d4412c2, 0x1),
    (0x1f0208e905bca25c402c2, 0x1),
    (0x1f9a8ce10654412c202c2, 0x1),
    (0x1f0a08e105bca25c400c0, 0x40058028e05199),
    (0x1f820cf986dcc2d4412c2, 0x1),
    (0x1f2209ed24b88254400c2, 0x1),
    (0x1f9a8ce1052c2254402c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_28 : Array (Nat × Nat) := #[ (0x1f0a08e9049c8254412c2, 0x1002c8523e),
    (0x1f0a08e90498837c60040, 0x439c20e70c523e),
    (0x1f2209e924b88254412c2, 0x400b0),
    (0x1f0a08e904b88254412c2, 0x10112c00b2),
    (0x1f0e08e5049c8254412c2, 0x10e6d0519e),
    (0x1f2208ed24b88254412c2, 0x400b0),
    (0x1f8208e1049883fc60040, 0x113800125a07b6c1ede),
    (0x1f8608e5049c8254412c2, 0x10480c509e),
    (0x1f0208e106fcc12c20300, 0x1144681210018440640),
    (0x1f1208f106dcc13c2, 0x1),
    (0x1f0a08e905bca25c412c2, 0x1),
    (0x1f0608e5049c837c60040, 0x1002fc00be002f0529e),
    (0x1f1208f106dcc13c212c2, 0x1),
    (0x1f820c7982d4412c2, 0x1),
    (0x1f0608e50498837860040, 0x114a7800bc),
    (0x1f820cf98c7982d4412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_29 : Array (Nat × Nat) := #[ (0x1f2209cd24b88254412c2, 0x400b0),
    (0x1f1208e106dcc13c20040, 0x10288043a0),
    (0x1f2209ed24b88254402c2, 0x4004b),
    (0x1f820cf9837c62d4412c2, 0x10000c0583),
    (0x1f0208f106dcc13c202c2, 0x1),
    (0x1f020cf982d441ac20040, 0x4070012a304d2d),
    (0x1f1208e106dcc13c203c2, 0x40040),
    (0x1f820cf983fc6254412c2, 0x44e00),
    (0x1f0208f106dcc12c203c2, 0x400a1),
    (0x1f0208f106dcc12c20300, 0x1144004b080184400a1),
    (0x1f1208e106dcc13c200c0, 0x40880024805300),
    (0x1f0608e50498837c607c6, 0x4005b),
    (0x1f1208e106dcc12c201c0, 0x1140c0080813a2400a0),
    (0x1f0208e50498837c60786, 0x1),
    (0x1f1208e106ccc13c212c2, 0x1),
    (0x1fe30c9887ef2254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_30 : Array (Nat × Nat) := #[ (0x1fef2c9887e30254412c2, 0x40890),
    (0x1f0208e504988378607c6, 0x4005b),
    (0x1f820cf983820254412c2, 0x1),
    (0x1f0208e106ccc13c201c0, 0x10260053a014e840040),
    (0x192c27e304988254400c2, 0x1),
    (0x1f1a08e50498837c60040, 0x4540413af0531f),
    (0x1f1e08e10498837c60040, 0x4548413af0093e),
    (0x1f0608e107fce01800040, 0x115210540513c785000),
    (0x1f1208e106dcc130212c2, 0x400a0),
    (0x1f6608e50498837c60040, 0x4548103ef0083e13e8053bc),
    (0x1f0208e107fce01c00040, 0x4548415214500014004551e),
    (0x1fe30c9887fb8254412c2, 0x4555a),
    (0x1f1208e106dcc12c20300, 0x455800124000880144000a0),
    (0x1f060cf9837c608000040, 0x104a0c2100138f0559e),
    (0x1f020cfd837c608000040, 0x10520c1f00138f0511e),
    (0x1f1208e106dcc12c203c2, 0x400a0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_31 : Array (Nat × Nat) := #[ (0x1ce10b9a85bca254412c2, 0x1),
    (0x1f0209cd24b88254402c2, 0x4004b),
    (0x1f0208e105b4a25c400c0, 0x45638158e40058),
    (0x192c27e304988254402c2, 0x1),
    (0x1f1208e106dcc134212c2, 0x400a0),
    (0x1f2608e50498837c60040, 0x10116c035c14680563c),
    (0x1f0608e106dcc13c20040, 0x100100522000f000da6),
    (0x1f2209c524988254412c2, 0x40049),
    (0x1f2208e106dcc12c20300, 0x115668049001a4406c0),
    (0x1f020cf982d4413c212c2, 0x1),
    (0x19e107e304988254412c2, 0x1),
    (0x1f420af54498817c612c2, 0x1),
    (0x1f0a08e105bca254400c2, 0x1),
    (0x1f2209c104988254402c2, 0x40049),
    (0x1fe30c9884e10254412c2, 0x1),
    (0x1f2209e524988254402c2, 0x40049) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_32 : Array (Nat × Nat) := #[ (0x1f0609e504988254402c2, 0x100d204955),
    (0x18e507e304988254412c2, 0x456bc),
    (0x1f020cf9837c61ac20040, 0x101c004012104b456ad),
    (0x1f564f2e2cf982d4412c2, 0x4068905e245721),
    (0x1f020cf9837c62d4402c2, 0x1),
    (0x1f2e28e106dcc13c202c2, 0x1001001081),
    (0x1f2e28e106dcc13c203c2, 0x40040),
    (0x1ffb8f564cf982d4412c2, 0x40f801618c57e0),
    (0x1fe30c9885bca254400c2, 0x1),
    (0x1fe30c9887fce254412c2, 0x41b00),
    (0x1f020cf982d4412c207c6, 0x1),
    (0x1fe30edcc5bca254412c2, 0x1060605700),
    (0x1f0209ed28e106dcc03c2, 0x1),
    (0x1f020cf982d4412c20780, 0x1160605880020540fe9),
    (0x1f0608e10498837c601c6, 0x1),
    (0x1f9a8f564cf982d4412c2, 0x1010245960) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_33 : Array (Nat × Nat) := #[ (0x1fe30c9885bca254402c2, 0x1),
    (0x1f0209ed24b88254400c0, 0x459b000d2c0451),
    (0x1f0208e105bca274400c0, 0x45a3a11d4c0358),
    (0x1f0208e106dcc12c20340, 0x1164003c1000c440040),
    (0x1f2a08e504988254412c2, 0x4034f168d059bc),
    (0x1fe70f9a8cf98254412c2, 0x10000c000201400575a),
    (0x1f0209e104988254402c0, 0x44ce0),
    (0x1f2e28e106dcc12c203c2, 0x1),
    (0x1f020cf982d4417c612c2, 0x1),
    (0x1f0208e106dcc13c200c2, 0x1),
    (0x1f020cf983fc6254402c2, 0x40700),
    (0x1f0208e106dcc11c202c2, 0x40040),
    (0x1f3e28e106dcc13c202c2, 0x1002805101),
    (0x1e0208e106dcc13c202c2, 0x456a0),
    (0x1f020e820cf98254402c2, 0x42363),
    (0x1f0e08ed04988254412c2, 0x1126c849bc) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_34 : Array (Nat × Nat) := #[ (0x1f1608e106dcc13c212c2, 0x1),
    (0x1f3e28e106dcc12c203c2, 0x40709),
    (0x1ffcefe304988254412c2, 0x45a80),
    (0x1f0208e104988254412c0, 0x1),
    (0x1f020cf98254412c20fc6, 0x1),
    (0x1f0208e10498837c607c0, 0x4268009a081bbc020f40840),
    (0x1f0208e106dcc12c200cc, 0x1),
    (0x1f020cf9825441fc612c2, 0x1),
    (0x1f0208e106dcc12c201c2, 0x40040),
    (0x1f0208e106dcc130200c0, 0x45b2016c840040),
    (0x1f0208e106d0c13c200c0, 0x45be016f840040),
    (0x1f520cf982d4412c2, 0x1),
    (0x1f0e08e106dcc13c200c0, 0x1001005c0016f805b20),
    (0x1f020cf982d4417c212c2, 0x1),
    (0x1f0e08e106dcc13c212c2, 0x45be0),
    (0x1ec3092c24988254400c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_35 : Array (Nat × Nat) := #[ (0x1f1208e106dcc1fce12c2, 0x1),
    (0x1f0608e107fce498807c6, 0x4089e),
    (0x1f0608e10498831c607c6, 0x4005a),
    (0x1f0208e106d0c13c201c0, 0x1026005ce0173840040),
    (0x1f0208e106d0c12c201c0, 0x409800a9802a61),
    (0x1f0208e106c0c12c201c0, 0x45500),
    (0x1f1e08e106dcc12c201c0, 0x10d8005d080a4400920),
    (0x1f020cf9825441fc212c2, 0x43680),
    (0x1f1e08e106dcc13c212c2, 0x42e10173803520),
    (0x1f020cf98254417da12c2, 0x1),
    (0x1f7a68e10498837c60786, 0x45521),
    (0x1f0208e107fce49880786, 0x1),
    (0x1f0208e10498831c60786, 0x1),
    (0x1fe30c9885b88254412c2, 0x1020105de0),
    (0x1fc208e106dcc13c212c2, 0x45e01),
    (0x1f0208f108e107fce00c0, 0x45e680da805df1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_36 : Array (Nat × Nat) := #[ (0x1f0208e106dcc13c202c0, 0x1098205ea003e840640),
    (0x1f1208e106dcc12c20fce, 0x1),
    (0x1f0208e106dcc12c203c0, 0x457800ce003288020240040),
    (0x1f020cf98254412c207da, 0x1),
    (0x1fe30c98849ca254412c2, 0x1),
    (0x1f020cf983ac6254412c2, 0x1),
    (0x1fe30c98849c8254412c2, 0x1012005f1e),
    (0x1f020cf983ac2254412c2, 0x45f80),
    (0x1fe30c988498837c60040, 0x421da17ea85f1e),
    (0x1fe30c9885b8a254412c2, 0x1),
    (0x1f8a09ed24b88254412c2, 0x1),
    (0x1fe30c9884b88254412c2, 0x40300),
    (0x1f020af54498816c200c0, 0x10fc18601e018f4043f),
    (0x1f420af54498812c207c6, 0x1),
    (0x1fe30c9884bca254412c2, 0x1),
    (0x1f020cf983bc6254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_37 : Array (Nat × Nat) := #[ (0x1f6208e504988254412c2, 0x4031300d840fbc),
    (0x1fa208e504988254412c2, 0x44a0500d9c603c),
    (0x1f820f564cf982d4412c2, 0x40009043800003),
    (0x1c9887fb87e30254412c2, 0x1),
    (0x1c9887e305bca254412c2, 0x1),
    (0x1f0208e106ccc13c202c2, 0x1),
    (0x1f0208e106ccc130212c2, 0x1),
    (0x1f020c7983fc6254412c2, 0x1),
    (0x1f0208e106ccc12c203c2, 0x1),
    (0x1f0608e104988378607c6, 0x4005a),
    (0x1f0208e106ccc12c201c0, 0x45500),
    (0x1f6208e50498837c60040, 0x41001024f05322),
    (0x1f2209cd24988254402c2, 0x40049),
    (0x1f0208e105b4a254400c0, 0x1),
    (0x1f1a08e10498837860040, 0x46084),
    (0x1f0208e107f8e01800040, 0x4608418214551e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_38 : Array (Nat × Nat) := #[ (0x1f0208e106ccc12c20300, 0x46100),
    (0x1f020cf98378608000040, 0x4158308800611e),
    (0x1fe307e704988254412c2, 0x4619e),
    (0x1fe707e304988254412c2, 0x4625a),
    (0x1fe307e30498837c60040, 0x4625a18678161e),
    (0x1fe307fb85bca254412c2, 0x462b0),
    (0x1ffb87e305bca254412c2, 0x46298),
    (0x1fe307ff64988254412c2, 0x41c84),
    (0x1fff67e304988254412c2, 0x46304),
    (0x1f0208e104988378601c6, 0x1),
    (0x1fe307e724988254412c2, 0x1),
    (0x1fe727e304988254412c2, 0x1),
    (0x1f020d7dacf98254402c2, 0x1),
    (0x1f020dfdac798254402c2, 0x1),
    (0x1fe307e305b88254412c2, 0x463b0),
    (0x1f0208e107ece6dcc00c0, 0x463c018f0438f0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_39 : Array (Nat × Nat) := #[ (0x1f7a68e10498837c607c6, 0x1),
    (0x1ff747ef24988254412c2, 0x4629e),
    (0x1f0208e107f8e498807c6, 0x1),
    (0x1f7a68e104988378607c6, 0x1),
    (0x1ec307e304988254400c2, 0x1),
    (0x1f7e68e104988378607c6, 0x1),
    (0x1f0208e106ccc12c20fce, 0x1),
    (0x1f0208e107fce130212c2, 0x1),
    (0x1f0208e106ccc1fce12c2, 0x1),
    (0x1f0e08e106dcc12c201c0, 0x11900008080b0240fa0),
    (0x1f0208e107fce01c000c0, 0x42f000bc0464001900464b0),
    (0x1f020be10498807c60040, 0x1040005b800a8002980),
    (0x1f1a08e10480837c60040, 0x104010295a0a36c5b3e),
    (0x1fe30db885b88254412c2, 0x46530),
    (0x1f7e6be1049880040, 0x11976860801956854800b6f05e1e150002a9e),
    (0x1f7e6be10498837c60040, 0x463da0ba782b9e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_40 : Array (Nat × Nat) := #[ (0x1f1a08e107fce49880040, 0x10b9682b3d),
    (0x1f1a08f90498837c60040, 0x1198082c3c0b0f45c1e),
    (0x1f1a08e107fce01800040, 0x1198082f1e0b27c641e),
    (0x1f020bfd64f8849880040, 0x42d3c0da785dbf),
    (0x1f0208e107fce7ece00c0, 0x11970065c119bc037c0),
    (0x1f0208e107e4e01800040, 0x4301e0c07c6480),
    (0x1f7e6c7e68e1049880040, 0x119af037bc0c2f030be),
    (0x1c7e68e10498837c60040, 0x438bc0c6f031be),
    (0x1f0208e107e4e49880040, 0x10c570315d),
    (0x1fe30f7e6bfd649880040, 0x410010400007040916862db18b68189e),
    (0x1f0208e107fce09800040, 0x4670204014323c0ccf0339e),
    (0x1f020bfd6498807800040, 0x467810400c19bc160f02680),
    (0x1f020cf9837c609800040, 0x4680301c00193c098f0579e),
    (0x1f9a08e10498837c60040, 0x4680319c0832bc0e4f05ebe),
    (0x1f0208e10498037c60040, 0x427da09f6c1c5e),
    (0x18e10498837c60fde0040, 0x10a0f0283e18cf01cbc) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_41 : Array (Nat × Nat) := #[ (0x1f0208e106dcc12c20302, 0x40040),
    (0x1c0608e10498837c607c6, 0x1),
    (0x1f020c0608e10498807c6, 0x1),
    (0x1f2e2cf983820254412c2, 0x1),
    (0x1f0208e106dcc130202c2, 0x40040),
    (0x1f3208e106dcc12c20300, 0x11a2000b7012c20121002c244b20),
    (0x1f0209ed26dcc0300, 0x45fa11a200111018468510018400511a),
    (0x1f0209ed26dcc12c20300, 0x41190),
    (0x1f020cf9837c608400040, 0x4128301c00559e14478611e),
    (0x1f020cf983fc637c60040, 0x1054841fa1187746221),
    (0x18e107e30498837c60040, 0x456bc08cf016be),
    (0x1f7a08e10498837c60040, 0x4678119e101bbc162f058be),
    (0x1f020cf983846254412c2, 0x1),
    (0x1fe30f9a8cf9837c60040, 0x10160c058201600575a15d70575d),
    (0x1f9a88e10480037c60040, 0x405821a608185a05f6c693e),
    (0x1f0208e106dcc130012c2, 0x404900124469201a4840040) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_42 : Array (Nat × Nat) := #[ (0x1f0208e107fc649880040, 0x469821a60c25da0976c1a5e),
    (0x1f0208e10498837800040, 0x45ada),
    (0x1f020c8388e1049880040, 0x106d686a3c06d6c1b5e),
    (0x1cf987e305bca254412c2, 0x1),
    (0x1bfd67e304988254412c2, 0x1),
    (0x1f0208e105b4a254400c2, 0x1),
    (0x19e527e304988254412c2, 0x1),
    (0x1f020c7985bca254402c2, 0x1),
    (0x1f4609cd24988254412c2, 0x46a8d),
    (0x1f0208e107ece254400c0, 0x11ab306acd),
    (0x18ed27e304988254412c2, 0x1),
    (0x1be307e304988254412c2, 0x1),
    (0x1f2e29cd24988254402c2, 0x1),
    (0x1f020ab54498812c207c6, 0x1),
    (0x1f020ab54498817c612c2, 0x1),
    (0x1f0208e106ccc134212c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_43 : Array (Nat × Nat) := #[ (0x1f2e28e104988378607c6, 0x1),
    (0x1ec307e304988254402c2, 0x1),
    (0x1f6209ed2498837c60040, 0x410010ee783b1e),
    (0x1f020cf9837c608800040, 0x46b0301c003a420fcf0590c),
    (0x1f8a08e10498837c60040, 0x11ac0c3c5a0ff6c603e),
    (0x1f0208e106dcc12c20342, 0x40040),
    (0x1f0208e106dcc134200c0, 0x46ba01ae840040),
    (0x1d0608e10498837c607c6, 0x1),
    (0x1f9a89ed24e10254412c2, 0x1),
    (0x1f0208e106dcc134202c2, 0x40040),
    (0x1f1a08e10488837c60040, 0x1040103dda0f50c6bbe),
    (0x1f7e6be10498812c20040, 0x46a920b8304206),
    (0x1f2a08e10498837c60040, 0x440da166f059be),
    (0x1f020cf9839c6254412c2, 0x1),
    (0x1f620af54498812c20040, 0x41001020184306),
    (0x1fe3090c24988254402c2, 0x40030) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_44 : Array (Nat × Nat) := #[ (0x1fe30f02039a8254412c2, 0x1),
    (0x1f0208e106dcc1bc20040, 0x1111004541),
    (0x1fc20af54498812c20040, 0x1112304586),
    (0x1f2e28e1039a8254412c2, 0x1),
    (0x1f020af54498817c20040, 0x1118f4473f),
    (0x1f564af10498812c20040, 0x1102305a06),
    (0x1f020cf982dc412c20040, 0x4070011a244809),
    (0x1fe30cb88254412c20040, 0x46b00128003c00),
    (0x1f0209c524988254402c2, 0x1),
    (0x1f0206e304988254402c2, 0x1),
    (0x1e2208ed24988254412c2, 0x1),
    (0x1f0208e106d4c134212c2, 0x1),
    (0x1f0208e104988156412c2, 0x1),
    (0x1f020af544988150012c2, 0x100c94048f1a4dc033d),
    (0x1fe30ad44498812c20040, 0x46980130784b86),
    (0x1f0208e10498837c20040, 0x44cda1336c4cde) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_45 : Array (Nat × Nat) := #[ (0x18e10498825441fdc12c2, 0x1),
    (0x1f164af54498817c612c2, 0x1),
    (0x1f2628e105bca254400c2, 0x1),
    (0x1f0e29c104988254402c2, 0x1),
    (0x1fe3079a84e10254412c2, 0x1),
    (0x1f9a8cf98af542dcc12c2, 0x1),
    (0x1f2e2ce904bca254412c2, 0x1),
    (0x1f564af54498812c203c6, 0x4000d),
    (0x1f164af54498812c207c6, 0x1),
    (0x1fe3079a84f98254412c2, 0x1),
    (0x1f2e28e105b88254400c2, 0x1),
    (0x1f0629ed24988254402c2, 0x46c33),
    (0x1f564af54498813c612c2, 0x1),
    (0x1f2e29ed2498825440042, 0x100d3c034e),
    (0x1f020af544988178212c2, 0x4033d),
    (0x1f2e29e524988254400c2, 0x1001206c30) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_46 : Array (Nat × Nat) := #[ (0x1f2e29e504988254402c2, 0x40ee0),
    (0x1f2e2ce905bca254402c2, 0x100dac6bc9),
    (0x1fef2cb88254412c202c2, 0x100a001009),
    (0x1fa209e524988254412c2, 0x40367),
    (0x1f020ce905bca254402c2, 0x1),
    (0x1f2e2be104988254402c2, 0x1),
    (0x1fe30cb88254412c202c2, 0x40280),
    (0x1ff74f9a8cf9837c612c2, 0x11b2006c81),
    (0x1fff6f9a8cf98254412c2, 0x11020c4082),
    (0x1f0208e106dcc5bca01c6, 0x1),
    (0x1feb2f9a8cf98254412c2, 0x100c0c0302),
    (0x1f020af549ed2498807c6, 0x1),
    (0x1f020dfdaaf546dcc02c2, 0x1),
    (0x1fe30f9a8cf9827c412c2, 0x101e003f820fe006d18),
    (0x1f9a8f5648e107fce00c0, 0x408801b4806df0),
    (0x1f7e6af549ed2498807c6, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_47 : Array (Nat × Nat) := #[ (0x1ff74fbeacf98254412c2, 0x11b8006c80),
    (0x1f020efdc9ed2498807c6, 0x1),
    (0x1f020cf98af5412c20fce, 0x1),
    (0x1fe30cf98cb88254412c2, 0x1),
    (0x1fe30fbeacb88254412c2, 0x1),
    (0x1f7e6af54498812c201c6, 0x40313),
    (0x1fe30f9a8cb88254412c2, 0x40000),
    (0x1f564af54498812c201c6, 0x100034000c),
    (0x1fe72f9a8cf98254412c2, 0x10000c0002),
    (0x1fef2f9a8cf98254412c2, 0x100c0c0302),
    (0x1f9a8ec30cf98254400c2, 0x46de0),
    (0x1f020cf98af541fce12c2, 0x1),
    (0x1f2e28e105bca25440342, 0x4004c),
    (0x1f020af549652498807c6, 0x1),
    (0x1f2e2af549ed2498807c6, 0x1),
    (0x1ffb8f564af546dcc12c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_48 : Array (Nat × Nat) := #[ (0x1fe30f9a8dfda254402c2, 0x103a080e80),
    (0x1fe30e928cf98254402c2, 0x1),
    (0x1f2e29ed25b88254412c2, 0x103ba40ee8),
    (0x1fe30f9a8cf986d4412c2, 0x40a15028500f92),
    (0x1f9a8ce905bca254412c2, 0x1),
    (0x1fe30f564cf982dcc12c2, 0x11bbb05962),
    (0x1fe30fdeccb98254412c2, 0x100a740000),
    (0x1f2e28e104988328207c6, 0x1),
    (0x1f0209ed24988250402c0, 0x46f6103b8c0355),
    (0x1fe3094404988254402c2, 0x11be000e8600cc06e8a),
    (0x1f0208e105b0a250400c0, 0x1),
    (0x1fe306e304988254402c2, 0x1),
    (0x1fe30d988254402c2, 0x1),
    (0x1f0e08e105bca250400c0, 0x11c1880a38),
    (0x1fe30b5444988254402c2, 0x1),
    (0x19ed26e304988254402c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_49 : Array (Nat × Nat) := #[ (0x1f9a8de105bca254402c2, 0x1),
    (0x1fe30f020d988254402c2, 0x1),
    (0x1f0209ed25b88254402c2, 0x1),
    (0x1fe30d988254412c202c2, 0x1),
    (0x1fef2f9a8af546dcc12c2, 0x11c2006ce2),
    (0x1f020cf98af545bca07c6, 0x11c6007100),
    (0x1f020af545bca0780, 0x474271ce0073061ca6872001ca00721a),
    (0x1f020af545bca37c60780, 0x47480),
    (0x1f5649ed2498837c601c6, 0x47104),
    (0x1f020af545bca12c20780, 0x47506),
    (0x1fe30f9a8af546dcc12c2, 0x11c5887160),
    (0x1f020cf985a00254402c2, 0x4758c1c44c0339),
    (0x1fe30f9a8af545bca37c6, 0x1),
    (0x1fe30f9a8af546d4c12c2, 0x47160),
    (0x1fe30dbeacf98254412c2, 0x40300),
    (0x1fe30cb885bca254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_50 : Array (Nat × Nat) := #[ (0x1fa20cf985bca254412c2, 0x1),
    (0x1f9a88e105a00254400c2, 0x476001ba480338),
    (0x1fe30f9a8af546d4412c2, 0x1114287160),
    (0x1fc20cf986dcc37c612c2, 0x1116007680),
    (0x1f020cf9837c60c0000c0, 0x476800fc0076d60fd587108),
    (0x1f5649ed2498831c607c6, 0x1),
    (0x1fe309cc04988254412c2, 0x46e041b84840b01c26870a4),
    (0x1fe30dbaacf98254412c2, 0x100c007742),
    (0x1f020af54498812c20780, 0x11c4006e0600c54033d),
    (0x1af54498812c20f9807c6, 0x471801dc00773c),
    (0x1f020af544f8812c20780, 0x11c868780c1205477a3),
    (0x1f020afd4498812c20780, 0x11c800788612054483d),
    (0x1f020a854498812c20780, 0x4729a),
    (0x1f9a88e1038a8254412c2, 0x1),
    (0x1fb60cf98254412c2, 0x475e21d648751a1d4007300),
    (0x1f7a0af54498812c20780, 0x11ce0078861d96c780c1d824781e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_51 : Array (Nat × Nat) := #[ (0x1fe30bbc24988254412c2, 0x47400),
    (0x1fb60cf985bca254412c2, 0x11d9347486),
    (0x1f9a8cf105bca254412c2, 0x1),
    (0x1f7a09ed24988254412c2, 0x11d4206fe7),
    (0x1fe30cb8837c6254412c2, 0x46b00),
    (0x1f0208e106dcc5bca03c6, 0x1),
    (0x1fe30fbeacb98254412c2, 0x100c007913),
    (0x1f020af5496d2498807c6, 0x1),
    (0x1fef2f9a8cb98254412c2, 0x1),
    (0x1f020af549e52498807c6, 0x1),
    (0x1f0208e106dcc1bca07c6, 0x1),
    (0x1f2e29e52498825440042, 0x402cf001206c30),
    (0x1fe30f9a8c998254412c2, 0x40000),
    (0x1f0209ed24bc8254402c2, 0x40ee3),
    (0x1f2609ed24988254402c2, 0x40ee1),
    (0x1fe30f9a8cb18254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_52 : Array (Nat × Nat) := #[ (0x1f020cf989ed22dc402c2, 0x1),
    (0x1fa20cf985bca254402c2, 0x1),
    (0x19ed2498825440fdc02c2, 0x11e520794e),
    (0x1fe30e9a8cf98254402c2, 0x1),
    (0x1f020cf982dc412c202c2, 0x1),
    (0x1f8a0cf98254412c202c2, 0x40003),
    (0x1f0208e106dcc15c212c2, 0x40340),
    (0x1f020cf985ac2254402c2, 0x1),
    (0x1f020cf986d4412c202c2, 0x1),
    (0x1fe30b2c24988254402c2, 0x1),
    (0x1fe30e988254412c202c2, 0x1),
    (0x1f0e08e105b0a254400c0, 0x479b200d303e5c),
    (0x1f020aa54498817c212c2, 0x1),
    (0x1f9a88e103bea254412c2, 0x1),
    (0x1f0208e105bca2544034a, 0x1),
    (0x1fbea8e1039a8254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_53 : Array (Nat × Nat) := #[ (0x1f0208e104988338607c6, 0x1),
    (0x1fe30e9885e30254412c2, 0x1),
    (0x1f020cf982dc412c200c0, 0x10fc007a0900a244809),
    (0x1fe30dbcacb88254412c2, 0x43f12),
    (0x1fa20cf98254412c200c2, 0x1),
    (0x1f0208e106dcc33c203c2, 0x1),
    (0x1f1608e106dcc12c200c0, 0x11ec000010020207a88),
    (0x1fef2fe30cb88254412c2, 0x47b10),
    (0x1fe30cb88254412c200c2, 0x1),
    (0x1f0209e50498837c607c6, 0x1),
    (0x1fe30efcccb88254412c2, 0x469b0),
    (0x1f920cf98254412c202c2, 0x1),
    (0x1f020af54498817c207c2, 0x1),
    (0x1f5208e106dcc12c200c0, 0x47c801f0207b88),
    (0x1ff74fe30cb88254412c2, 0x47ccc),
    (0x1fe30cd88254412c200c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_54 : Array (Nat × Nat) := #[ (0x1f0208ed0498837c607c6, 0x1),
    (0x1f0208e105bca27c403c0, 0x10ce007db803bc07d39),
    (0x1ffb8fe30cb88254412c2, 0x433dc),
    (0x1fe3096c24988254400c2, 0x1),
    (0x1f8a08e105bca2544034a, 0x1),
    (0x1f8a0cf982dc412c2, 0x1),
    (0x1f0e08ed05bca254400c0, 0x4034d00d3079b21c1883e98),
    (0x1f520af54498817c212c2, 0x1),
    (0x1f0208e106dcc17c200c0, 0x11fa807e23),
    (0x1f0e08e10498837c607c6, 0x1),
    (0x1fe30cd885bca254412c2, 0x1),
    (0x1f020af54498817c202c2, 0x1),
    (0x1f0208e105bca254403c0, 0x10ce007c32020cc0358),
    (0x1fe30bfc64988254412c2, 0x46980),
    (0x1f020af54498812c207c2, 0x4033d),
    (0x1f1608e105bca254400c0, 0x11ec0008321eacc0fb8) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_55 : Array (Nat × Nat) := #[ (0x1f0208e107fce014000c0, 0x47b001ec047b181ec640980),
    (0x1fe3049883fb8254412c2, 0x1),
    (0x1f0208e105bca2f4400c0, 0x11fc007bb81f9040846),
    (0x1fa208e105bca254400c0, 0x11fe047c381fac807c6),
    (0x1f0208e107fce050000c0, 0x47c80022047fe21fd283398),
    (0x1f020af544988158212c2, 0x4033d),
    (0x1f2a09c524988254412c2, 0x4034f),
    (0x1f0209ed24bc8254402c0, 0x480b003b8c8039),
    (0x1f2e29e90498825440042, 0x1),
    (0x1f2609ed24bc8254412c2, 0x47060),
    (0x1fc20cf986dcc2d4412c2, 0x1),
    (0x1de10a9a85bca254412c2, 0x1),
    (0x1f564be10498812c207c6, 0x40e8c),
    (0x1f1a08e106dcc37c600c0, 0x47b060eee08120),
    (0x1f5649e50498837c607c6, 0x4035d),
    (0x1fe30fd64cf986d4412c2, 0x11de007266) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_56 : Array (Nat × Nat) := #[ (0x1fa20cf985bca254400c2, 0x1),
    (0x1fc20cf98254412c200c0, 0x11da006e02128744580),
    (0x1fa20cf987fce254412c2, 0x1),
    (0x1f9a88e106d4412c200c2, 0x1),
    (0x1f020af544f8812c207c6, 0x1),
    (0x1f620af54498812c201c6, 0x1),
    (0x1f9a88e105ac2254400c2, 0x1),
    (0x1f8a0cf989ed22dc412c2, 0x1),
    (0x1f020cf9825441ec200c0, 0x10fc00819a120d44539),
    (0x1f620af54498812c207c6, 0x1),
    (0x1fc208e105bca254400c0, 0x11da186e38206c83ff0),
    (0x1f020af544988154212c2, 0x4033d),
    (0x1f1e6af54498812c207c6, 0x1),
    (0x1d2a28e10498832c207c6, 0x1),
    (0x1f2e28e104988254412c0, 0x440c81032840d4),
    (0x1fef2f9a8cb88254412c2, 0x47f13) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_57 : Array (Nat × Nat) := #[ (0x1fdecee105bca254412c2, 0x11fe606d70),
    (0x19ed249883fb8254412c2, 0x46d98),
    (0x1f0209c124988254402c0, 0x1),
    (0x1f5648e104988156412c2, 0x1),
    (0x1fe30cf88254412c2, 0x1),
    (0x1f2e09ed24988254402c0, 0x11bd9c80b01bd8480b6),
    (0x1fe309ec24988254412c2, 0x1),
    (0x1f2e29ed04988254412c2, 0x11bd986f60),
    (0x1fe20cf987fce254412c2, 0x1),
    (0x1f7a08e104988254412c2, 0x11b8186e081b8c06e32),
    (0x1fe20cf985bca254412c2, 0x1),
    (0x1fc20cf985bca254412c2, 0x1),
    (0x1f0209ed24f88254402c2, 0x1),
    (0x1f6209ed24988254402c2, 0x1),
    (0x1f020af54498815c212c2, 0x4033d),
    (0x1fe3096c24988254402c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_58 : Array (Nat × Nat) := #[ (0x1fe30cd88254412c202c2, 0x1),
    (0x1f564be104988254402c2, 0x1),
    (0x1f020ae504988178612c2, 0x402f5),
    (0x1f0208e105bca2dc400c0, 0x12094077c7),
    (0x1fe30fba8cb88254412c2, 0x1),
    (0x1f6209ed24988254400c2, 0x1),
    (0x1f9a88e1053c2254403c2, 0x1),
    (0x1f7e6be104988254412c2, 0x41000),
    (0x1f020ae50498812c207c6, 0x402f5),
    (0x1f6209ed24f88254412c2, 0x1),
    (0x18e1049883fb8254412c2, 0x1),
    (0x1f2e2ae50498812c207c6, 0x1),
    (0x18e104988254412c20fde, 0x1),
    (0x1fe209ed24988254412c2, 0x1),
    (0x1f0628e105bca254400c2, 0x46c35),
    (0x1fef290c24988254402c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_59 : Array (Nat × Nat) := #[ (0x1f4e29ed24988254402c2, 0x1),
    (0x1f020ae544988178212c2, 0x402bd),
    (0x1f6309ed24f98254412c2, 0x1),
    (0x1fa20ce985bca254412c2, 0x1),
    (0x1f8a09ed24f98254412c2, 0x1),
    (0x1f9a8ee30cb98254412c2, 0x1),
    (0x1f020ad54498812c20780, 0x46ed620a780295),
    (0x1f9a8de30cb98254412c2, 0x1),
    (0x1f020af544f8817c612c2, 0x1),
    (0x1f620af54498817c612c2, 0x1),
    (0x1fe30e9a8cb98254412c2, 0x40000),
    (0x1fe30d9a8cb98254412c2, 0x40000),
    (0x18e107e104988254412c2, 0x1),
    (0x18e1049883f98254412c2, 0x1),
    (0x1f020be104988054402c2, 0x103a300ec8),
    (0x1f0209e504988250402c2, 0x103b8002dd) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_60 : Array (Nat × Nat) := #[ (0x1f020bfd64f88254402c2, 0x41003),
    (0x1f620bfd64988254402c2, 0x41001),
    (0x1f020b9d64988254402c2, 0x1),
    (0x1f0008e104988254402c2, 0x1),
    (0x1fe10f0204988254402c2, 0x46f021bc3040e0),
    (0x1f0208e105b8a250400c0, 0x1),
    (0x1f020be107988254402c2, 0x11c01849c9),
    (0x1f7e6be104988254402c2, 0x41000),
    (0x1f020be3039a8254412c2, 0x1),
    (0x1f020bf904988254402c2, 0x11be3075801b8c482cb),
    (0x1f6209e524988254412c2, 0x40361),
    (0x1f6208ed24988254412c2, 0x40361),
    (0x1f9a87e304f98254412c2, 0x1),
    (0x1fc30cb88254412c2, 0x1),
    (0x1f0e08e105b8a254400c0, 0x4833200d304950),
    (0x1f020ae54498817c212c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_61 : Array (Nat × Nat) := #[ (0x1f2a29e504988254412c2, 0x40348),
    (0x1fa20cd985bca254412c2, 0x1),
    (0x1f0209e524988254402c0, 0x120f2002d5),
    (0x1f0209e904bca254402c2, 0x1),
    (0x1f020ae50498817c612c2, 0x1),
    (0x1f0209e5059c8254402c2, 0x1126c4833f),
    (0x1f0209ed04988254402c2, 0x440c820f2c83d5),
    (0x1f0e28e105b88254400c2, 0x1),
    (0x1f0208e105b88374400c2, 0x120ce8833b),
    (0x1f2629e504988254412c2, 0x40348),
    (0x1f2609e504988254412c2, 0x4034800d248042),
    (0x1f2e08ed04988254412c2, 0x440c9202c880bc),
    (0x1f2a08e524988254412c2, 0x4034f),
    (0x1f4609e504988254412c2, 0x4480d1212077bc),
    (0x1f4608ed04988254412c2, 0x44a0d1e934823c),
    (0x1f0e08e104988254412c0, 0x121130845a) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_62 : Array (Nat × Nat) := #[ (0x1e5448e10498812c207c6, 0x1),
    (0x1f2608ed24988254412c2, 0x40349),
    (0x1f0208e105b88254400c0, 0x12133084cd),
    (0x1ffb8ce10c988254412c2, 0x409da),
    (0x1fa20dfda4b88254412c2, 0x47b0e),
    (0x1ce1049883fb8254412c2, 0x1),
    (0x1fef2fba8cb88254412c2, 0x1216488531),
    (0x1feb0fba8cf98254412c2, 0x1020004802120008563),
    (0x1f0209ed24dc8254402c0, 0x1216188630020d47e39),
    (0x1f7e6be104988254400c2, 0x41000),
    (0x1f7e6ae50498812c207c6, 0x41015),
    (0x1fc208ed04988254412c2, 0x1128744a2b206c881bc),
    (0x1f666be104988254412c2, 0x1),
    (0x1f620be104988254412c2, 0x1120484813121804861),
    (0x1fce08ed04988254412c2, 0x11e208788c1e0c8783c),
    (0x1f6208fd64988254412c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_63 : Array (Nat × Nat) := #[ (0x1f620bfd64f88254412c2, 0x46600),
    (0x1ee109dec4988254412c2, 0x1),
    (0x1f0208e1038ec254412c2, 0x1),
    (0x1e524d2a28e10498807c6, 0x1),
    (0x1f0209e124988254402c0, 0x486c8),
    (0x1f0208e10498837c40042, 0x486da21b6c86de),
    (0x1f2e08e104988254412c0, 0x4874821d288754),
    (0x1f2c28e104988254402c2, 0x1),
    (0x1ffeefe104988254412c2, 0x45a80),
    (0x18e10498825441ffc12c2, 0x1),
    (0x1f0008e104988254402c0, 0x45ac8),
    (0x18e004988254412c20fce, 0x1),
    (0x18e10498825441fde02c2, 0x46a31),
    (0x18e104f98254412c20fce, 0x11e4187930),
    (0x1f0628e524988254412c2, 0x1),
    (0x1fe20bfd64988254412c2, 0x46700) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_64 : Array (Nat × Nat) := #[ (0x1f0208e105bc8254400c2, 0x483cc20f3486d8),
    (0x1f7e6bf904988254412c2, 0x46780),
    (0x1fe30cf8837c6254412c2, 0x46800),
    (0x1f1e68fd64988254412c2, 0x1),
    (0x18e1049882fdc12c207c6, 0x11dc60771a),
    (0x1e564d2e28e10498807c6, 0x1),
    (0x1be3049883fb8254412c2, 0x1),
    (0x1f0e28e524988254412c2, 0x46c34),
    (0x1f0629e524988254402c2, 0x1),
    (0x1f0209e5259ca254402c2, 0x1),
    (0x1f2629e524988254400c2, 0x1),
    (0x1f0208e107f88254400c2, 0x11d818760720b3082cd),
    (0x1fc30f9a8cb98254412c2, 0x1),
    (0x1fa20cf985b8a254412c2, 0x1),
    (0x1fa20cf984bca254412c2, 0x1),
    (0x1f0e29e524988254402c2, 0x487b0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4_65 : Array (Nat × Nat) := #[ (0x1f4e28ed24988254412c2, 0x1),
    (0x1f6e6be104988254412c2, 0x1),
    (0x1f6209fd64988254412c2, 0x1),
    (0x1f0208e103b6a254412c2, 0x1),
    (0x1f0209e5249ca254402c2, 0x46c30),
    (0x1f0209e524bca254400c2, 0x487b0),
    (0x1f0e29cd24988254402c2, 0x1),
    (0x1f2a29e504988254402c2, 0x40348) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock4 (b : Nat) : Array (Nat × Nat) :=
  if b < 33 then
    if b < 16 then
      if b < 8 then
        if b < 4 then
          if b < 2 then
            if b < 1 then
              certificateBlock4_0
            else
              certificateBlock4_1
          else
            if b < 3 then
              certificateBlock4_2
            else
              certificateBlock4_3
        else
          if b < 6 then
            if b < 5 then
              certificateBlock4_4
            else
              certificateBlock4_5
          else
            if b < 7 then
              certificateBlock4_6
            else
              certificateBlock4_7
      else
        if b < 12 then
          if b < 10 then
            if b < 9 then
              certificateBlock4_8
            else
              certificateBlock4_9
          else
            if b < 11 then
              certificateBlock4_10
            else
              certificateBlock4_11
        else
          if b < 14 then
            if b < 13 then
              certificateBlock4_12
            else
              certificateBlock4_13
          else
            if b < 15 then
              certificateBlock4_14
            else
              certificateBlock4_15
    else
      if b < 24 then
        if b < 20 then
          if b < 18 then
            if b < 17 then
              certificateBlock4_16
            else
              certificateBlock4_17
          else
            if b < 19 then
              certificateBlock4_18
            else
              certificateBlock4_19
        else
          if b < 22 then
            if b < 21 then
              certificateBlock4_20
            else
              certificateBlock4_21
          else
            if b < 23 then
              certificateBlock4_22
            else
              certificateBlock4_23
      else
        if b < 28 then
          if b < 26 then
            if b < 25 then
              certificateBlock4_24
            else
              certificateBlock4_25
          else
            if b < 27 then
              certificateBlock4_26
            else
              certificateBlock4_27
        else
          if b < 30 then
            if b < 29 then
              certificateBlock4_28
            else
              certificateBlock4_29
          else
            if b < 31 then
              certificateBlock4_30
            else
              if b < 32 then
                certificateBlock4_31
              else
                certificateBlock4_32
  else
    if b < 49 then
      if b < 41 then
        if b < 37 then
          if b < 35 then
            if b < 34 then
              certificateBlock4_33
            else
              certificateBlock4_34
          else
            if b < 36 then
              certificateBlock4_35
            else
              certificateBlock4_36
        else
          if b < 39 then
            if b < 38 then
              certificateBlock4_37
            else
              certificateBlock4_38
          else
            if b < 40 then
              certificateBlock4_39
            else
              certificateBlock4_40
      else
        if b < 45 then
          if b < 43 then
            if b < 42 then
              certificateBlock4_41
            else
              certificateBlock4_42
          else
            if b < 44 then
              certificateBlock4_43
            else
              certificateBlock4_44
        else
          if b < 47 then
            if b < 46 then
              certificateBlock4_45
            else
              certificateBlock4_46
          else
            if b < 48 then
              certificateBlock4_47
            else
              certificateBlock4_48
    else
      if b < 57 then
        if b < 53 then
          if b < 51 then
            if b < 50 then
              certificateBlock4_49
            else
              certificateBlock4_50
          else
            if b < 52 then
              certificateBlock4_51
            else
              certificateBlock4_52
        else
          if b < 55 then
            if b < 54 then
              certificateBlock4_53
            else
              certificateBlock4_54
          else
            if b < 56 then
              certificateBlock4_55
            else
              certificateBlock4_56
      else
        if b < 61 then
          if b < 59 then
            if b < 58 then
              certificateBlock4_57
            else
              certificateBlock4_58
          else
            if b < 60 then
              certificateBlock4_59
            else
              certificateBlock4_60
        else
          if b < 63 then
            if b < 62 then
              certificateBlock4_61
            else
              certificateBlock4_62
          else
            if b < 64 then
              certificateBlock4_63
            else
              if b < 65 then
                certificateBlock4_64
              else
                certificateBlock4_65
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_0 : Array (Nat × Nat) := #[ (0x1f0208e104988254412c20040, 0x1002000000000040004),
    (0x1f0208e10498837c6254412c2, 0x40080),
    (0x1f0208e104988254412c202c2, 0x1),
    (0x1f0208e104988254412820040, 0x40080006480193006580100),
    (0x1f0608e104988254412c2, 0x401e00064802e000a48025a),
    (0x1f0608e104988254412c20040, 0x100e00010000c000302007800192),
    (0x1f0208e104988254413c212c2, 0x40400),
    (0x1f0208e10498837c60040, 0x4042100e00025a0108003810096c041e00e10025e015680480),
    (0x1f0208e10498837c612c20040, 0x100a48029300a5805da),
    (0x1f0208e104988254417c612c2, 0x1),
    (0x1f0208e104988254412c200c2, 0x1),
    (0x1f2e28e104988254412c202c2, 0x1004000089),
    (0x1f0208e10498837c6254402c2, 0x40080),
    (0x1f0208e104988254410c202c2, 0x40100),
    (0x1e0208e104988254412c202c2, 0x405c8),
    (0x1f0209e104988254412c202c2, 0x1018000280) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_1 : Array (Nat × Nat) := #[ (0x1f0208e10498837c612820040, 0x406120184c0616),
    (0x1f0208e104988250412820040, 0x40480),
    (0x1f0608e104988250412820040, 0x4070001a4806940064801e0),
    (0x1e0208e1049883544254402c2, 0x4079b),
    (0x1f0208e10498837860040, 0x101e84070001e80070101e780704015680080),
    (0x1f0208e104988378612820040, 0x405da),
    (0x1f020e5648e104988254402c2, 0x1),
    (0x1f0208c104988254412c200c2, 0x40860),
    (0x18e107e304988254412c2, 0x101300050002488089e024b00898025a00880),
    (0x1e2e28e104988254412c202c2, 0x40489),
    (0x1f020e2e28e104988254402c2, 0x40548),
    (0x1e0208e10498837c6254402c2, 0x408c8),
    (0x1f0208c104988254410c202c2, 0x40900),
    (0x1f2e2e0208e104988254402c2, 0x40548),
    (0x1e0209e104988254412c202c2, 0x1018000981),
    (0x1f0208e104988378612c20040, 0x100200098c026340990) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_2 : Array (Nat × Nat) := #[ (0x1f0209e104988254402c20040, 0x40c1802e600b0002a000a00),
    (0x1f0209e10498827c6254402c2, 0x1032600b98),
    (0x1f0208e105988254402c200c2, 0x1036040d02),
    (0x1d020ae104988254412c202c2, 0x40e0c),
    (0x1f0208e104988354402c20040, 0x40f9b002000f0c03a300e8e),
    (0x1f0209ed29e104988254402c2, 0x1041200088),
    (0x1f0209e104988254402c200c2, 0x1044001080),
    (0x1f0209e109c104988254402c2, 0x411e1),
    (0x1fe30c988254412c2, 0x106500189e0600017da05d1816980586015cc05568149c0506013e005dc01680058001590055c8148405000139204d80131204a001200),
    (0x1f2e29e104988254402c2, 0x100ba40180047841100041200fa8039980d84032780c1e039800d92032600c18),
    (0x1f2e29e104988254412c2, 0x1019a401e906da01100041201a90039981a04066d80c1e039801a12066c00c18),
    (0x1f2e2f0209e104988254402c2, 0x1),
    (0x1f020ce10254412c209880040, 0x41d00048081c9e070781b9e),
    (0x1f0209e106dcc4988254402c2, 0x1074c012c8),
    (0x1f0208e104d88214412c202c2, 0x41306),
    (0x1f0208e10654412c209880040, 0x41f0004e041ea4078901d9e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_3 : Array (Nat × Nat) := #[ (0x1f020bf549e104988254402c2, 0x107cc81448),
    (0x1f4208e104988214412c202c2, 0x41486),
    (0x1f0209e1096104988254402c2, 0x41528),
    (0x1f1208e104888254412c20040, 0x40c040840020aa080ac1f92),
    (0x1f564f0209e104988254402c2, 0x1084cc19e1),
    (0x1f020ae10498812c2054402c2, 0x40e0c),
    (0x1f0208e504988250412c202c2, 0x1068302193),
    (0x1f0208e1049c8250412c200c0, 0x4230006a1822e208b8c2210),
    (0x1fe30f0209e104988254402c2, 0x108ca41060),
    (0x1f0208e10498832c2054402c2, 0x41b0c),
    (0x1f2208c104988254412c200c2, 0x10440423e0),
    (0x1f0209e105988254402c2, 0x42551092002431),
    (0x1f0608e504988254412820040, 0x109800019300648259201a480300),
    (0x1f0209e1049883544254402c2, 0x4269b),
    (0x1f0208e1049883544254402c2, 0x4041b),
    (0x1f0608e10498837c60040, 0x101084008009a802600090f0269e09808243e09d680700) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_4 : Array (Nat × Nat) := #[ (0x1f0608e10498837c612820040, 0x42492092500292),
    (0x1f0608e10498837c612c20040, 0x109430250e026300612),
    (0x1f0209e108ed24988254402c2, 0x427c8),
    (0x1f0208e1049883544250402c2, 0x41b60),
    (0x1f0208e1049883504254402c2, 0x1006302833),
    (0x1f0208e106dcc13c212c2, 0x10b0002b890b0042b880ad802a80053c42a000a70413a1053c02a010a70013a00a580189006100288000f8000b0),
    (0x1f2e28e1049883544254402c2, 0x4283306d80110c09f500f9b),
    (0x1f0208e106dcc254413c212c2, 0x42d180b3901b16041000f80),
    (0x1f0608e104988254412820040, 0x100e002d920b6500000),
    (0x1f020af549e104988254402c2, 0x429c8),
    (0x1f0208e104988244413c202c2, 0x42a00),
    (0x1f0208e10490825c412c20040, 0x103e602eec0bbb42e16),
    (0x1f0608e104988250412c202c2, 0x10b2302f0c),
    (0x1f0208e107dcc4988254402c2, 0x107cc02bb1),
    (0x1f0208e1049883144254402c2, 0x1006302c1b),
    (0x1f0208e104988250412c200c0, 0x108c002d060838020e1007900012) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_5 : Array (Nat × Nat) := #[ (0x1f0208e1049c8498837c60040, 0x4269e09a7c079e),
    (0x1fe307e304988254412c2, 0x10030004c00c300301e0ad002f9e0c31830180ad182f980c3c030000adc02f80),
    (0x1f0208e10498837c637860040, 0x4275a09d6c275e),
    (0x1f0208e10498837c601800040, 0x431800c400310105678159f0a2782a9e),
    (0x1f0208e107fce498837c60040, 0x10c600165a0596c2fda06178305a),
    (0x1f0208e10498837c607c60040, 0x4290005c0017020c2002b00),
    (0x1f0208e104988480837c60040, 0x105b6816db06368321e),
    (0x1f020cf98254412c208000040, 0x434000480c138004e6033bc0ccf0328c),
    (0x1f020cf988e10498837c60040, 0x4340004b682bbc0a76c29de),
    (0x1f0208e10498837c609880040, 0x1052f0133c0a8782c1e),
    (0x1f2e2e2e28e104988254402c2, 0x405e0),
    (0x1f0208e105bca254400800040, 0x1030700c1d03e6034860d21c2d00),
    (0x1f0208e105b8a498837c60040, 0x40caa032ac27de),
    (0x1f0208e10498837c602820040, 0x41112036300d8e),
    (0x1f0208e104988488837c60040, 0x1039680e5b06d68281e),
    (0x1fe308e107e304988254412c2, 0x400c0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_6 : Array (Nat × Nat) := #[ (0x1f0208e105bca498837c60040, 0x10670819c30417808da),
    (0x1f0208e10498837c602c20040, 0x10b2301a0c06838090c),
    (0x1f0208e1049882544124200c0, 0x10b400350602a100a85006400100),
    (0x1f0208e10498825c412820040, 0x10d660008002c480b1303c580012),
    (0x1f0a08e104988254412820040, 0x10d870348002a480a1303a580006),
    (0x1f0208e105b8a254400800040, 0x4361c0d874359802ea80bab002183500),
    (0x1f0208e10498827c612820040, 0x10020010920344c0d16),
    (0x1f0208e104988258412c20040, 0x10da60008007f981fe70b8400012),
    (0x1f1208e104988254412820040, 0x10dc1034980824820120ba500030),
    (0x1f0208e105bca250400800040, 0x4371c0dc74369808478211f002182300),
    (0x1f0208e10498827c612c20040, 0x400800bc30219308658086c),
    (0x1f0208e1049882544154402c2, 0x100630281b),
    (0x1f0208e1049882544110002c2, 0x10de001c0000608018c0ca6c0060),
    (0x1f0208e1049882d0412c20040, 0x10e000330006f801de0077880042),
    (0x1f0208e1049882d4412820040, 0x10e2003300072481e9307a580042),
    (0x1f8208e104988254412820040, 0x10e40c3380070481e1307858003c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_7 : Array (Nat × Nat) := #[ (0x1f020cf982544128208000040, 0x10d00039030e2003818075081f42002f03792),
    (0x1f0208e104988254412c2, 0x1),
    (0x1f0209e104988254402c2, 0x402e9018000248),
    (0x1f0208e504988254412c202c2, 0x41a0c007842193),
    (0x1f0608e104988254412c202c2, 0x10b2300100007802f0c),
    (0x1f0e28e104988254412c200c2, 0x401000e6003510),
    (0x1f0e28e104988254412c202c2, 0x43a00004003980),
    (0x1f564f0e28e104988254412c2, 0x400000b46c3ada),
    (0x1f0208e10498833c6254402c2, 0x1),
    (0x1fe30f0e28e104988254412c2, 0x40100003003510),
    (0x1f0208e104988254417c602c2, 0x1),
    (0x1f0208e104988254412c200c0, 0x10b4002d060ec003b01000100012),
    (0x1f0208e1049883fce254412c2, 0x1),
    (0x1f0208e104988254412c203c6, 0x1),
    (0x1f0208e107fce4988254412c2, 0x1),
    (0x1f0208e104988254412c207c6, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_8 : Array (Nat × Nat) := #[ (0x1f0208e106dcc498817c612c2, 0x10b4783ac0),
    (0x1f0208e10498835c6254402c2, 0x1),
    (0x1f5648e104988254417c612c2, 0x1002cc3a60),
    (0x1f0e28e104988254410c202c2, 0x43a00),
    (0x1f0208e1049882544120200c0, 0x435000d4183b900ee440100),
    (0x1f0208e104988254413c612c2, 0x1),
    (0x1f0208e104988254412c20042, 0x1),
    (0x1f0208e10498837c6254400c2, 0x40080),
    (0x1f0208e1049882544124200c2, 0x40100),
    (0x1f2e28e104988254412c200c2, 0x43c00000202d10),
    (0x1f0209ed24988254402c200c2, 0x10f0003a00006000088),
    (0x1f2e28e10498837c6254402c2, 0x10a0cc3c0c),
    (0x1f2e28e104988254410c202c2, 0x10e8040089),
    (0x1f564f2e28e104988254412c2, 0x1000002d1b0b40c3cbc),
    (0x1f0208e105bca2544134212c2, 0x40086),
    (0x1f020af549ed24988254402c2, 0x10b4083ad5) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_9 : Array (Nat × Nat) := #[ (0x1f0208e10498837c6214402c2, 0x40080),
    (0x1fe30f0209ed24988254402c2, 0x1006002329002203cb0),
    (0x1f0208e10498837c6054402c2, 0x40080),
    (0x1f0208e107fce4988254402c2, 0x1),
    (0x1f0208e10498831c6254402c2, 0x1),
    (0x1f0208e1049882544134212c2, 0x10a0000060),
    (0x1f0208e1049883786254412c2, 0x1015680480),
    (0x1f0208e104988254412c203c2, 0x10b0000060),
    (0x1f0208e104988254413c202c2, 0x42a00),
    (0x1f0208f104988254412c202c2, 0x41308),
    (0x1f1208e104988254412c202c2, 0x41488),
    (0x1f0208e104988254415c612c2, 0x1),
    (0x1f0208e10498832c2254402c2, 0x41b0c),
    (0x1f020ae104988254412c202c2, 0x40e0c),
    (0x1f020e5248e104988254402c2, 0x1),
    (0x1f0a08e104988254412c20040, 0x40c1c0d2003b000f6003d02) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_10 : Array (Nat × Nat) := #[ (0x1f020ae104988254417c612c2, 0x40c80006600b80),
    (0x1f0208e104b88254412c200c2, 0x1036002183),
    (0x1f0208e10498825c412c20040, 0x40f98002003d0c0f4342210),
    (0x1f2e2f0608e104988254412c2, 0x10b40c105a),
    (0x1f2208e104988254412c200c2, 0x1044042f00),
    (0x1f0208e1049883544154412c2, 0x1007d411bc),
    (0x1f2e29e104988254412c202c2, 0x1000240389),
    (0x1f0608e10498837c6254412c2, 0x40660018480380),
    (0x1f0209e10498837c6254402c2, 0x1066c03483),
    (0x1f0208e104b88254410c202c2, 0x41a000340c000a),
    (0x1f0208e10498825c4124200c0, 0x106a002d060f8283e0b03c400012),
    (0x1f0209e105988254412c202c2, 0x40680092002501),
    (0x1f2a2f0608e104988254412c2, 0x10040001920d40c27da),
    (0x1f2208e104988254410c202c2, 0x42c80042040008),
    (0x1f0608e504988254412c2, 0x42de00b648254809430243c),
    (0x1f0608e504988254412c20040, 0x1098000001000003e800b7802d92) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_11 : Array (Nat × Nat) := #[ (0x1f1208e104988254413c212c2, 0x42680),
    (0x1fe30c988254412c20040, 0x439180e400429810a0042001060041001020040000fe003f0004d80391804c483900),
    (0x1fe30c98837c6254412c2, 0x4495e12200480011e10475a11a10460011678451811248441c10e48431204c48450011380440410f80436004d80436010c48429810a004200),
    (0x1f020cf982d4412c202c2, 0x1137a44d8010c0039091340c4c80130484b8004a24430005dc84b0012a241592055804a12126241380048243909),
    (0x1f020cf982d4412c20040, 0x438000e200521814600510014284500013e244f0913a004e09055803800052543880),
    (0x1fe30dbcac988254412c2, 0x4594c16218580015f18571e15a10528405210561212930460015660555a15210540014f805372055c8537214a10522a14648511212e4843e0),
    (0x1f820cf98254412c202c2, 0x1172005c0014a00389516e0c5b001303044000500c528005db05a831680c158c04d8c4a0c16660120304e543895),
    (0x1f0208e106dcc13c203c2, 0x1171c45cf114c00382117e00550017c405e80051045300053c047001788013a0065805d8817500178004e843821),
    (0x1f1208e106dcc12c200c0, 0x4608018000650019200640018e40630018a20622018600610805d80608005a406000),
    (0x1fef2fe30c988254412c2, 0x4658005a006a041779858001a76869401a200681612d80480019e70674619a00667005dc0667019600651019240641016c1053e01324844e0),
    (0x1fe30c988254412c200c2, 0x11b0006b8019600601016e005400134184500058006580055c85a801ac00139204d804b121aa601200056406010),
    (0x1f0208e50498837c607c6, 0x11af746c5d1980060a11ba046e001b608670005974660006370591f1b56c17a005b6c49021b278159f0568460a1),
    (0x1f0208e106dcc13c201c0, 0x46f801bc4072b01c80071801c48470801c08071201c2047021065806f80062406f10),
    (0x1ffb8fe30c988254412c2, 0x4741e0627874c00650074c01d07872de1c96871da1cf685a981606073601b918689817b68569c1cfc85a801600073121b9c0688017bc85684),
    (0x1fe3092c24988254400c2, 0x11d80075801d0006f0017c00570617c185700060c0740005e406f00053985d841d47813aa053805d921d460139c),
    (0x1f0608e10498837c60786, 0x11d774765d1d2006fa11ba0069021ba08690006168748005b70591e1daf815a005b6859201daf0159e05e846fa1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_12 : Array (Nat × Nat) := #[ (0x1f564ae10498812c20040, 0x11e8a836001e63079001e230781e1de007706038483700),
    (0x1f2e29e104988254412c20040, 0x43718086187b001ea001a12),
    (0x1f9a8ce105bca254412c2, 0x1037ac168205808830120bc0820720608815c2024880641fe007f181fbb47e0d1f6047d621f3981a661f0507be2),
    (0x1f2e29e10498837c6254412c2, 0x1039807c92),
    (0x1f0209ed24b88254402c2, 0x1066e47c80219c4858006d9c85032132c1a8c0398c840c20e600c1b),
    (0x1f0209ed24b88254412c202c2, 0x47c8007fc40c21),
    (0x1fe30c988254412c202c2, 0x122a008a102260889002224888001e8641680058000c08055c8878221c00139204d80801221a601200030243709),
    (0x1fe30f020c988254412c202c2, 0x10dc241983),
    (0x1f0208e105bca25c400c0, 0x1234848c80230e08d20232048c3922fd88b0006d902300),
    (0x1f0208e105bca25c412c200c0, 0x42300236208d8908fd81110),
    (0x1fe30cf98c988254412c2, 0x104484189e06000910224300905c0f080112023f68879b206608f6023b688e1823fc88783206008f1223bc88e00),
    (0x1f2e29ed29e104988254412c2, 0x106da03c00),
    (0x1f2e29e104988254400c2, 0x1245849200041203c00039988500246780c1e039808506246600c18),
    (0x1f2e29e104988254412c200c2, 0x43c00088001a90),
    (0x1fe3092c24988254402c2, 0x125400949025000938625018938024d841880060c00f9006aa4232905398828a24a7813aa05380829424a60139c),
    (0x1fe30f02092c24988254402c2, 0x108ca41031) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_13 : Array (Nat × Nat) := #[ (0x1f9a8ce104988254412c20040, 0x125c00969e2587c9580),
    (0x1f9a8ce10498837c6254412c2, 0x4845a260107f8025e78881c1ee5088041ef889700),
    (0x1f020af544d88254412c202c2, 0x1222307c060698c800c262240c03),
    (0x1f020cf9849882d4412c20040, 0x126a009a1e26694990f),
    (0x1f2e2bf549e104988254412c2, 0x49ab426f888506207209b0424fa08e48225807d42),
    (0x1f420af544988254412c202c2, 0x1226487d86069848792270180c01),
    (0x1f0208e106dcc254413c203c2, 0x1250588e8004530828c273001a98),
    (0x1f1208e106dcc254412c200c0, 0x49e00228187e00276689d1b069900c1220c200c04),
    (0x1f7e6f2e29e104988254412c2, 0x12786c9ee3),
    (0x1fe30c9888e10254412c200c2, 0x49f02),
    (0x1f0208e50498837c612c207c6, 0x122bd47e80030b40dc81e96c1a0c),
    (0x1f0208e105bca25c412c201c0, 0x4a000252c0900027e209f89044400fb0245001a80),
    (0x1fef2f2e29e104988254412c2, 0x128040a0f0),
    (0x1fe3092c28e104988254400c2, 0x4a148),
    (0x1f0608e10498837c612c20786, 0x1255d4908006a24116024cf01112),
    (0x1f1208e106dcc498812c20040, 0x4a22428694830e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_14 : Array (Nat × Nat) := #[ (0x1f564f2e29e104988254412c2, 0x43d0128e6c9ee303648164828c0ca2c2),
    (0x1f0208e50498837c6254402c2, 0x1019840d8c1e9cc0381),
    (0x1f564ae104988254412c202c2, 0x12903021b006980168c27c180c00),
    (0x1f0208e1049c837c6254400c0, 0x129328a4cb019900f9e245c00384),
    (0x1fe30f2e29e104988254412c2, 0x422000aa40a0f004400184806a403cb0),
    (0x1f2209ed28e104988254400c2, 0x49348),
    (0x1f5648e10498832c2254402c2, 0x42f600b380188c285500f83),
    (0x1f1208e104988254412c200c0, 0x4158028e00a38629600a5310f4683d24),
    (0x1f0608e107fce4988254412c2, 0x4165a),
    (0x1f0208e504988254412c207c6, 0x417000864c21e1),
    (0x1f020c9888e10254412c200c2, 0x41680),
    (0x1f0208e1049c8254412c201c0, 0x42a800aa60179e29808a60308840224c),
    (0x1f7e6f0608e104988254412c2, 0x4185a),
    (0x1f0608e104988254412c20786, 0x419000bc302f48),
    (0x1f02092c28e104988254400c2, 0x41880),
    (0x1f2208e504988254412c2, 0x1007a0a81320d200281009242ee003a4ca7c829c4ca6db) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_15 : Array (Nat × Nat) := #[ (0x1f2208e504988254412c20040, 0x40c192a600a90000020a8820bb800e93),
    (0x1f0608e104988254413c212c2, 0x12a800029202d80833c),
    (0x1f0a08e504988254412c2, 0x10819c0a042873c7a841dcd020600284ca1c81ea4c7743),
    (0x1f0a08e504988254412c20040, 0x4779c2ac00aa8000018a880081800a13),
    (0x1f4208e104988254413c212c2, 0x11e01cab80),
    (0x1f0e08e104988254412c2, 0x1083980a84289387b041e33020e002a48a2481ec4878da),
    (0x1f0e08e104988254412c20040, 0x4791c2b00000062aa00a902083800a92),
    (0x1f0e0f0608e104988254412c2, 0x12b33079da),
    (0x1f0a08e10498837c60040, 0x4acda2b00078da2ae80ab001dd0caa1e2a608a6de2b768ad00),
    (0x1f0a08e10498837c612c20040, 0x421181ec487a9329c58ae2a),
    (0x1f1208e10498837c612c20040, 0x128830a18c29e38ae8c),
    (0x1f2e28e504988254412c202c2, 0x11f23000012bc303489),
    (0x1f2e2ae104988254412c202c2, 0x1000cc34a1),
    (0x1f9a8f5649e104988254412c2, 0x12c2c4b04f2c124af90),
    (0x1f0208e90498837c6254402c2, 0x12c4d43481),
    (0x1fe30f5649e104988254412c2, 0x12cc00b2c02c930b18d) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_16 : Array (Nat × Nat) := #[ (0x1f2208e10498837c6254400c2, 0x12cf203482),
    (0x1f564f2e28e504988254412c2, 0x100c00b41b2d00ca2bc),
    (0x1f020ae10498837c6254402c2, 0x4349b),
    (0x1f9a8f2e28e504988254412c2, 0x43d802d494b48d2bec87bbc),
    (0x1f0208f10498837c6254402c2, 0x11f0203499),
    (0x1fe70f2e28e504988254412c2, 0x4a9002d840b5842c6c07d3c),
    (0x1f1208e10498837c6254402c2, 0x11f6203498),
    (0x1f0608e104988254412c200c0, 0x12d000a306004003b002aa040302007803d0c),
    (0x1f0209e104988254412c207c6, 0x127a600180),
    (0x1f4208e104988254412c200c0, 0x47f072d400b0062dc08b6800f668b08c),
    (0x1f2208e107fce4988254412c2, 0x47fb1),
    (0x1f0208e904988254412c207c6, 0x4809a),
    (0x1f0208e104d88254412c200c2, 0x48006),
    (0x1f0208e104988274412c20340, 0x12d800811a2ca00b80e007d0b78d2a440b35a),
    (0x1fbeaf0608e104988254412c2, 0x481da),
    (0x1f4208e104988254412c203c6, 0x48200) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_17 : Array (Nat × Nat) := #[ (0x1f0208e104988254416c200c2, 0x48280),
    (0x1f2629e104988254412c2, 0x401e90d8787a6000a0002482ea00ba482e798b9662bc10361e2e248b130),
    (0x1f0208ed24b88254412c202c2, 0x106800af00007a83621),
    (0x1f0208e504988254417c612c2, 0x40293035847a5b),
    (0x1f0208f104988254417c612c2, 0x48382),
    (0x1f0208e1049c8254412c200c2, 0x4840600790bb16),
    (0x1f0208e1049c8254412c200c0, 0x10b4001a862a408a903007902210),
    (0x1f0e2f0608e104988254412c2, 0x484da),
    (0x1f0a08e104988254412c20042, 0x121410bb82),
    (0x1f0a08e10498837c6254412c2, 0x1066d03480),
    (0x1f0208e1049c8254410c202c2, 0x4b88e2e23c0004),
    (0x1f0209ed28e504988254402c2, 0x10b408ba5b),
    (0x1f2208e1049882544124200c2, 0x4ba812f0140008),
    (0x1e0208e504988254412c202c2, 0x12b860b975),
    (0x1e020ae104988254412c202c2, 0x12e630ae81),
    (0x1f0209e104988254417c612c2, 0x1007a49f30) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_18 : Array (Nat × Nat) := #[ (0x1f8208e104988254412c20040, 0x412030ce00bc8c2c200b082),
    (0x1f020ce104988254417c612c2, 0x48682),
    (0x1f0208e1049882d4412c20040, 0x413800cc00b0bc2cc4cb316),
    (0x1f8e8f0608e104988254412c2, 0x4875a),
    (0x1f4208e104988254412c200c2, 0x48787),
    (0x1f0208e104988254413c203c2, 0x41500),
    (0x1f020c9888e10254410c202c2, 0x1290000040),
    (0x1f020ce10498837c6254402c2, 0x1220083381),
    (0x1f0208e104d88254410c202c2, 0x1222180034),
    (0x1f020bed2ae104988254402c2, 0x122430330a),
    (0x1f4208e104988254410c202c2, 0x12261c0032),
    (0x1f0208e1049c82544120200c0, 0x10b400bd862f440bd11248400004),
    (0x1f2209e104988254412c2, 0x1007a492002458402800092001e824800916000a040249),
    (0x1f0208e1049c825c412c200c0, 0x41a8006a18be082f82401f2007909210),
    (0x1f0208e1049c8254413c212c2, 0x101000029603d909146),
    (0x1f2608e504988254412c2, 0x1083a0bd0d2fb207b011e32422e00f848a4c8236308c3c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_19 : Array (Nat × Nat) := #[ (0x1f0e08e1049c8254412c200c0, 0x12fe008c8600010bf000839822e22f820bd10),
    (0x1f0208f104988254417c212c2, 0x1300008d02),
    (0x1f0208e105bca254400c0, 0x4c0212fe0078cc30080bf811e334c17630200230000218041806a000258),
    (0x1f0208e105bca254412c200c0, 0x423001ec107b05021d80290),
    (0x1f0208e105bca49c8254400c0, 0x12fb28becb307d89176),
    (0x1f2e28e10498832c2254402c2, 0x10018c2d39),
    (0x1f0208e104988354412c207c6, 0x128260018c),
    (0x1f5e4f2e28e104988254412c2, 0x43b0030a6cc20123930b1bc),
    (0x1f0208e10498837c6254403c2, 0x123a002d30),
    (0x1f0208e104d88254412c200c0, 0x48f0630a00b20630ec8c31b0ec70b310),
    (0x1f0208e10498825c412c207c6, 0x48f98),
    (0x1f4208e104988254413c612c2, 0x49181),
    (0x1f2208ed24988254412c2, 0x4c4692f64401e80d6a4934800a0402492f014b3ce2f04cb3c8),
    (0x1f2208ed24988254412c200c2, 0x4110100020bd91),
    (0x1f0608e104988254417c612c2, 0x4029204380933c),
    (0x1f0209e108c104988254400c2, 0x1311a0c1e0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_20 : Array (Nat × Nat) := #[ (0x1f0208e104988354417c612c2, 0x1007d4a13c),
    (0x1f0208e106544498817c612c2, 0x49282),
    (0x1f0208e1077c64988254402c2, 0x124e083301),
    (0x1f0208e10498830c2254402c2, 0x1250300063),
    (0x1f8208e504988254412c2, 0x106e881c9f31210969f1020c1e610784c9a48268304fdb),
    (0x1f8208e504988254412c20040, 0x4410331800c580000f0c500079841e13),
    (0x1f2208e104988254413c212c2, 0x4c680007a09681073a095b1),
    (0x1f3208e104988254412c2, 0x1070a81c1c25890961a0fc401c68070049650258003f49),
    (0x1f8608e104988254412c20040, 0x43f8331c00003c31600c582071801c12),
    (0x1f860f0608e104988254412c2, 0x131e0c405a),
    (0x1f8208e10498837c60040, 0x1074101d0125c1097011080cc7da31c003f5a31a80c60013f6cc69e318084fde32368c800),
    (0x1f8208e10498837c612c20040, 0x44283258309a0c26838c942),
    (0x1f2e28f104988254412c202c2, 0x44308000c43389),
    (0x1fe70f9a88e504988254412c2, 0x4b08032b70ca5b3260443bc),
    (0x1f8208e10498837c6254402c2, 0x1110003380),
    (0x1f2208e104988254412c200c0, 0x497812d200b48632e00cb000f6083d8c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_21 : Array (Nat × Nat) := #[ (0x1f020ce104988254412c207c6, 0x49802),
    (0x1f02092c28e104988254400c0, 0x4458032a00ca8633140cc512c360b0de),
    (0x1fff8f0608e104988254412c2, 0x4cd5a33260cd7233200465a),
    (0x1f8208e104988254412c207c6, 0x44680),
    (0x1f0208e104988254413c201c2, 0x44700),
    (0x1f0208e904988254417c612c2, 0x498b5),
    (0x1f1e8f0608e104988254412c2, 0x449da),
    (0x1f1208e104988254412c200c2, 0x44a00),
    (0x1f8208e10498837c6254412c2, 0x104a0c3380),
    (0x1f0209fd28f104988254402c2, 0x112e203308),
    (0x1f1208e104988254410c202c2, 0x1130000030),
    (0x1e0208f104988254412c202c2, 0x113620c930),
    (0x1f4209e104988254412c2, 0x1076b81e99336489999138341deb07a00cde1266004e48),
    (0x1f0208e5049882d4412c20040, 0x44e8033c00ce9e00108ce0f077801e93),
    (0x1f0208e104b88254413c212c2, 0x4cf80007a8998307ba89933),
    (0x1f0608e1049882d4412c20040, 0x4500034000004233a78cea006f801c92) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_22 : Array (Nat × Nat) := #[ (0x1f020c9888e10254413c212c2, 0x114200d080),
    (0x1f0208e1049883fc60040, 0x107c101f0126a089a8014400d0a13400040da33e80cf001396ccf9e33c084e5e34768d100),
    (0x1f0208e1049883fc612c20040, 0x4518025a48999326658d25a),
    (0x1f0208e1049883fc61ac20040, 0x4520031308cdc333718d2da),
    (0x1f0208e504988254412c202c0, 0x130800b58226c30d3800ec04a90500784d313),
    (0x1f0208e106544498812c207c6, 0x49b82),
    (0x1f3e28e104988254412c202c2, 0x45288000c03309),
    (0x1f3e28e104988254413c203c2, 0x45300001803309),
    (0x1ff30f3e28e104988254412c2, 0x4bc8032aa0548832a40c9b0),
    (0x1f0209fd28e104988254403c2, 0x1154003308),
    (0x1f020c9888e10254412c200c0, 0x4558032a00ca0035080bc9035084b0c6),
    (0x1f0208e1049882d4412c20fc6, 0x45600),
    (0x1f0a08e104988254417c612c2, 0x49c32),
    (0x1f8208e104988254417c612c2, 0x45980),
    (0x1f9e8f0608e104988254412c2, 0x10ccf4145a),
    (0x1e1208e104988254412c202c2, 0x117020d248) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_23 : Array (Nat × Nat) := #[ (0x1f120e1208e104988254402c2, 0x117220d2e0),
    (0x1f0208e10498825c417c612c2, 0x49cd8),
    (0x1f0208e1049882d441fc612c2, 0x45e00),
    (0x1f0208e104988254411c203c2, 0x117e000060),
    (0x1f820cf982d4412c2, 0x136684da3c36454d8dd36f74dbc836c00dae036908d99b36400d8c8359d4d58035454d495361b0d78335c00d68c35980d59535400d480),
    (0x1f2209ed24b88254412c2, 0x137facdf0037ad4de11093a02de837f98df0537ac0de0c37780dd12372c0dc18),
    (0x1f0608e50498837c6254412c2, 0x424e0092482600),
    (0x1f0a08e904988254412c20040, 0x4dc1a38200aa862aa1ce000),
    (0x1f0a08e90498837c6254412c2, 0x1372c8e080),
    (0x1f0208e5049c8254412c202c2, 0x4dd060b78ce10f),
    (0x1f020ae106988254412c202c2, 0x4dd86),
    (0x1f0608e1049c8254412c200c0, 0x4b4003781800042a408e2010b788e188),
    (0x1f0609ed28e504988254412c2, 0x12d008debc),
    (0x1f2208e104b88254412c200c2, 0x137c00e280),
    (0x1f020ae10498832c2254402c2, 0x4df86),
    (0x1f8208e1049882d4412c20040, 0x4d48038c00c5bc33a30ce8e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_24 : Array (Nat × Nat) := #[ (0x1f060cfd88e504988254412c2, 0x138cf0d53c),
    (0x1f1208f104988254412c202c2, 0x4d588),
    (0x1f0208f104988254413c203c2, 0x4d600),
    (0x1f0208e104b88274412c20300, 0x4e40036a68e3880b7c0ce0b0b624ce58),
    (0x1fe70f0608e504988254412c2, 0x139040db3c),
    (0x1f1208e104988254413c202c2, 0x4db80),
    (0x1f0608e5049c8254412c2, 0x425e009648e53039418e49e),
    (0x1f0608e5049c8254412c20040, 0x139600030300c080300097802592),
    (0x1f1208f104988254413c212c2, 0x4e600),
    (0x1f0608e50498837c60040, 0x109a8403810096c26a000e00025a39878e58039278e7bc39c00e6bc),
    (0x1f0608e50498837c612c20040, 0x4029300a48e5063a0302492),
    (0x1f0a08e10498825c412c20040, 0x4e8980d200a90c2a21ce18e),
    (0x1f0608e504988254412c202c2, 0x13a43000010b780e28c),
    (0x1f060cf988e504988254412c2, 0x400000cef0e9bc),
    (0x1f0208f104988254413c202c2, 0x4ea00),
    (0x1f0208e1049882d441ac20040, 0x4ea800cc00c53c3390cce46) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_25 : Array (Nat × Nat) := #[ (0x1f1208e104988254413c203c2, 0x13ac000060),
    (0x1f8208e1049883fc6254412c2, 0x13ae00e300),
    (0x1f0208f104988254412c203c2, 0x13b0000349),
    (0x1f0208f104988254412c20300, 0x13b200e41a316c001ab2cc0c019d2cc340349),
    (0x1f1208e106dcc13c212c2, 0x10a9a4148805040ec8104dc0ec013ae2012103bb80169005840ee003ada4db8036c80ea89357c0ea013a680d4a03b780d99036480ed000992003b0),
    (0x1f1208e106dcc254413c212c2, 0x1037900e1606628a3183a590df9437a80e880),
    (0x1f0608e1049c8498837c60040, 0x4041e39878ef1e),
    (0x1f9a8f0608e104988254412c2, 0x40100002f429da),
    (0x1f0208e1049883fc6254412c2, 0x10ae003300),
    (0x1f0608e10498837860040, 0x407a101200ef2039c00e6bc3bc78e70239af8275a00e00025a),
    (0x1fe30c9887e30254412c2, 0x13c878f1da00f0007403c41019400600028da3c318f0183bb1816983be6015cc3c3c0f0003bbc016803be001590),
    (0x1f0608e10498837c637860040, 0x4055a39ef0e7be),
    (0x1f0608e10498837c601800040, 0x13ce00f3003ca04d69e3b478ee1e),
    (0x1f0608e107fce498837c60040, 0x4f38035cf0efda364f8f05a),
    (0x1f0208e50498837c607c60040, 0x13b600d8003c200ee80),
    (0x1f0608e104988480837c60040, 0x4d7da36768f41e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_26 : Array (Nat × Nat) := #[ (0x1f0208e1049c837c601c00040, 0x13d400f4823d20cd89e3627c2a9e3c678289e),
    (0x1f7e6f0608e10498837c60040, 0x13d40cf5da364f4d940),
    (0x1f0608e10498837c607860040, 0x10ac00da00368082900),
    (0x1f0208e1049c8480837c60040, 0x136768d9db3c500f25a),
    (0x1f820cf98254412c208000040, 0x13daf0d48035260c73c340f0f60c),
    (0x1f060cf988e10498837c60040, 0x13da00ebbc3a6f0e9be),
    (0x1f0208e50498837c609880040, 0x4d5bc3a878ec1e),
    (0x1f020cf982d4412c208000040, 0x13dcf0d4803aa00c63c33cf0ec8c),
    (0x1f9e8f0608e10498837c60040, 0x4f7010a7682bbd354f4db3e),
    (0x1f0608e10498837c609880040, 0x4d5bc36e78f79e),
    (0x1f0208e1049c837c609c80040, 0x13ac78d61e0b0782a1e),
    (0x1f2209cd24988254412c2, 0x4f9e93e44401e801c20274900a0402493e214f8373e24cf831),
    (0x1f0608e104988378612c20040, 0x4038001768e80c3a0380292),
    (0x1f2209ed29cd24988254412c2, 0x4066800e200601),
    (0x1f0a08e105bca254400800040, 0x4dc1a3a260ac062ac1ca300),
    (0x1f0608e105bca498837c60040, 0x1372f00caa37af8f842) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_27 : Array (Nat × Nat) := #[ (0x1f0208e50498837c602c20040, 0x13a430dd063e2300d8c),
    (0x1f0608e104988488837c60040, 0x4ddc237f08fa1e),
    (0x1f0208e1049c837c600c00040, 0x4fa823ea0cde063781c2d063e4180f9e),
    (0x1f2e2f0608e10498837c60040, 0x427da37af4dec0),
    (0x1f0608e10498837c602820040, 0x4df0c37c382c8c),
    (0x1f0208e1049c8488837c60040, 0x137f08dfc304718f9da),
    (0x1f0608e1049883786254412c2, 0x100a4801e000b80019209d680700),
    (0x1f0608e10498825c412c20040, 0x4fb1800e00001238018e18807f980b12),
    (0x1f0608e105bca254400800040, 0x11e470779d3ec600086382180baa08478b400),
    (0x1f0208e50498827c612c20040, 0x4038138a30e10f3ee340d13),
    (0x1f1208e1049882544134212c2, 0x4fa00006a80348),
    (0x1f0208e1049c825c412c20040, 0x40f9800e10e1883862400120b8400f16),
    (0x1f2608e504988254412c20040, 0x479193ea003d000ec08e20208b803e12),
    (0x1f0208e105bca254400c00040, 0x11e470791d03e60b4002d004350008c000086),
    (0x1f0608e10498827c612c20040, 0x4038038a30e28e08fb01092),
    (0x1f1208e104988254412c20300, 0x13d800fc1a00400bc8000cc001aa2c220019c2c2380348) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_28 : Array (Nat × Nat) := #[ (0x1f060cf98254412c208000040, 0x4f6800fe0c50001406000bc38cf01d6c07508fc0c),
    (0x1f020cfd8254412c208000040, 0x4f7001040c4e8013a60e33c002f01f6c07d08e40c),
    (0x1f1208e104988254412c203c2, 0x4f780004000348),
    (0x1f0208e104d88254413c212c2, 0x13f2180400),
    (0x1f0208e10498837c613c20040, 0x120cf0833d24518fd5a),
    (0x1f0208e104988354402820040, 0x10d66c008024830a80c2a038018c),
    (0x1f0208e106dcc13c20040, 0x13f284fb0029b00fca03ec04a6c124dd83580047783680),
    (0x1f0208e105bca25c412c20040, 0x129c40a7110bc582c96),
    (0x1f0208e106dcc498813c20040, 0x4a7bc29ef4915e),
    (0x1f0208e106dcc13c212c20040, 0x12a800aa010a0181b16),
    (0x1f0208e10498837c6254400c0, 0x128920a24900b900080),
    (0x1f0208e106dcc37c613c212c2, 0x42ce4),
    (0x1e0208e10498832c2254402c2, 0x131030fd48),
    (0x1fe3092c24988254412c202c2, 0x10b4a40f91),
    (0x1f2208ed24988254412c202c2, 0x42c80007a035a9),
    (0x1f1208e104988254417c612c2, 0x4fd82) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_29 : Array (Nat × Nat) := #[ (0x1f0608e104988254412c200c2, 0x13f818010000780bb8c),
    (0x1f2209ed24988254402c2, 0x1010a411010412403883fd84fe800399cfe023f6780c1f03984fe0c3f6600c19),
    (0x1f2209ed24988254412c202c2, 0x10b8000fa9),
    (0x1f0608e10498837c6254402c2, 0x101980111224d500380),
    (0x1f0a08e10498837c6254402c2, 0x12cf283480),
    (0x1f0608e104988254410c202c2, 0x4ff8c2f0340000),
    (0x1f0208e1049c82544124200c0, 0x10b400bd8640011000503c400004),
    (0x1f0208e106d8c254413c212c2, 0x1010003518310583580),
    (0x1f220f0209ed24988254402c2, 0x1002201049),
    (0x1f0208e10498837c61ac20040, 0x14040033002570899432651900da),
    (0x1f020cf9825441ac212c20040, 0x451800e261010031a30cf8c0b0482a12),
    (0x1fe30c9885bca254412c2, 0x141d60588616001069200f00148405000045a419690580414484a4c4120055984100103e040dc9012a40bc82a724084901e0),
    (0x1f2e2af549e104988254412c2, 0x126f88fe0d2072108844218107c2),
    (0x1fe30f2e28e504988254412c2, 0x43d004264109100f2c107bc),
    (0x1f020ae109ed24988254402c2, 0x1420300088),
    (0x1f0208e104b88254412c200c0, 0x508800b401090642820d3030ec103d16) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_30 : Array (Nat × Nat) := #[ (0x1fe30f9a88e504988254412c2, 0x4b0800b570ca5b42a0d01bc),
    (0x1f0209ed28f104988254402c2, 0x1408200088),
    (0x1f2e28e104988254413c203c2, 0x50300001800089),
    (0x1f2e28e104988254413c202c2, 0x5028000180329b),
    (0x1fd64f2e28e104988254412c2, 0x400004160cca9b0b40d0abc),
    (0x1f0209ed28e104988254403c2, 0x1418000088),
    (0x1ffb8f0608e104988254412c2, 0x100400cd5a42d80cd7242c4904da),
    (0x1f0208e1049882d4412c207c6, 0x50500),
    (0x1f2e28e104988254412c203c2, 0x50b80004000089),
    (0x1f0209ed28e106dcc13c212c2, 0x1002c02b8842e0414f040a050108),
    (0x1f0208e1049882d4417c612c2, 0x50c00),
    (0x1f0208e104988254413c200c2, 0x50c80),
    (0x1f0208e1049883fc6254402c2, 0x1434003300),
    (0x1f0208e104988254411c202c2, 0x1436000060),
    (0x1f3e28e104988254413c202c2, 0x50e0000d20e41b),
    (0x1e0208e104988254413c202c2, 0x143a0100c8) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_31 : Array (Nat × Nat) := #[ (0x1f0208e106dcc13c202c2, 0x143a010e00436010d080a7050280053c10c804308013a00a5805d881750028803b3443780),
    (0x1f0208e106dcc254413c202c2, 0x10b390828c273000f80),
    (0x1f0208e104988254412c20300, 0x432800ca68bc80000c4000a000500060),
    (0x1f0208e106dcc13c212c202c2, 0x4528843a0102800ca0413a1),
    (0x1f020e1208e104988254402c2, 0x143c20d260),
    (0x1f820f020cf98254412c202c2, 0x50f0043bd438950ae542983),
    (0x1f0e08e104988254412c200c0, 0x4bf802fe18010043e0020e62a40820e02a4303b90),
    (0x1f0208e104988254417c212c2, 0x130000c002),
    (0x1f1608e104988254413c212c2, 0x510000ef30a20c40180bebc),
    (0x1f0208e105bca25c4254400c0, 0x51018440641b6400e480f98),
    (0x1f2e29e108e104988254400c2, 0x427c8),
    (0x1f3e28e104988254412c203c2, 0x51080004003309),
    (0x1f0208e104988254412c202c0, 0x4c20030808c20c32e003b010ec103b12),
    (0x1ffcef0208e104988254412c2, 0x511a1446811100),
    (0x1f0208e104988254412c20fc6, 0x51200),
    (0x1f020cf983fc6254412c2, 0x512004440d135d44af10d1841684571b15a5510920b0490d00416e4570315b8d10e00b18052e314a545198146005100) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_32 : Array (Nat × Nat) := #[ (0x1f020cf9849883fc6254412c2, 0x130878939d238249385238cc9a80),
    (0x1f0209fd28e106dcc13c212c2, 0x5108114620f7e8438045208),
    (0x1f0208e10498825441fc612c2, 0x51380),
    (0x1f0208e104988254412c201c2, 0x1450000060),
    (0x1f0208e106dcc12c203c2, 0x45c7143dc50b800e0850d81418005f1017a002b8944201140044e802b600aa003821002c00400054000240),
    (0x1f0208e106dcc254412c203c2, 0x1250588e800b46002cc),
    (0x1f0208e106dcc13c212c203c2, 0x50f71442005cf140c0013a100f802a00),
    (0x1f0208e106dcc13c200c0, 0x145a8516004568116a04580515a10a58115003c5c11480),
    (0x1f0208e106dcc13c212c200c0, 0x5150045c0117010c8001890),
    (0x1f0208e107fce6dcc13c212c2, 0x10ad80a0000a5807410),
    (0x1fe3092c24988254412c200c2, 0x145e0074000aa402890),
    (0x1f0608e10498837c607c6, 0x145f7519a146401188246409188001084190006168038005b7107004608015a005b69070246078159e0a2851521),
    (0x1f060f0208e10498837c607c6, 0x14688517dd454842b0000200185a),
    (0x1f0208e106dcc12c201c0, 0x1468006f101cac0a0001c6011ba146c00628846e811b0118a242b6046a006f10002c0040005e000240),
    (0x1f0208e106dcc13c212c201c0, 0x51a802800119801c8011c0047004189000f802880),
    (0x1f0208e10498837c60786, 0x11d9747480478011d82478091d800bf751d0044c791cbe44c811cbc0aa851aa1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_33 : Array (Nat × Nat) := #[ (0x1f060f0208e10498837c60786, 0x51aa11d774f5da),
    (0x1f0208f108e106dcc12c200c0, 0x147e011f5046e811e91),
    (0x1f020efdc8e106dcc13c212c2, 0x51fd0487c1210015a251de0483a05d8916101200016dc103a14638068c0),
    (0x1f0208e1049c8498837c607c6, 0x51e04464106e0244c802a9e0636907041b578289e),
    (0x1fe30a5444988254412c200c2, 0x4570016e1904060b191229c0a9905a86488181384),
    (0x1fe30c9884988254412c20040, 0x149000d0da48ea92300),
    (0x1fe30f0208e106dcc13c212c2, 0x52440450011110416a105a911bc10c80413004590111c501a0111c101a1),
    (0x1f020cf982d44254412c202c2, 0x50d001304902000b18113980a9804a12492241380),
    (0x1f0208e106dcc254413c200c0, 0x1494c925330b3900f86245600f80),
    (0x1f0608e10498837c612c207c6, 0x103e84116024cf02c8c),
    (0x1f0208e105bca254412c201c0, 0x4a000252c09000276089d8300a402d00),
    (0x1f0208e10498837c612c20786, 0x49575242002d09),
    (0x1f020af544d88498812c20040, 0x4abce300d9258f),
    (0x1f020af548e106dcc13c212c2, 0x1426008e1149ba8828d2070126021f7c107a1),
    (0x1f0208e105bca25c4254402c2, 0x42d0006d90fe14213600f98),
    (0x1fe30a5444988254412c202c2, 0x493802263108060b191279c0a990878c49c181384) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_34 : Array (Nat × Nat) := #[ (0x1f0208e104988254413c200c0, 0x428800b4002d064a121284908930225a),
    (0x1f0608e104988254412c207c6, 0x10a40001000bc302f48),
    (0x1f0208e104988254412c201c0, 0x10aa002a980aa78a580296040004000480060),
    (0x1f0208e104988254412c20786, 0x42b00),
    (0x1f0a0f0608e104988254412c2, 0x10ec0001004973125da),
    (0x1f0208e104b88498837c60040, 0x11e108fcbc3009125de),
    (0x1f0208e104988254416c200c0, 0x5260030a002d064a328b7c90f530b35c),
    (0x1f0a08e104988254412c207c6, 0x149a680100),
    (0x1f0208e104988254412c20340, 0x142601099a2ca00b7000ec643b04000500060),
    (0x1f0208e104dcc254413c212c2, 0x404003ff90ba40),
    (0x1f8a8f0608e104988254412c2, 0x100401275a),
    (0x1f0208e1049883bc6254412c2, 0x52780),
    (0x1f820f0608e104988254412c2, 0x12f230010048c0d235a),
    (0x1f0208e1049883ac2254412c2, 0x148e012387),
    (0x1f020c9888e10498837c60040, 0x524001436923bc1436d235e),
    (0x1f1a8f0608e104988254412c2, 0x10040124da) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_35 : Array (Nat × Nat) := #[ (0x1fe30f0608e504988254412c2, 0x10000400000ca41293c),
    (0x1f0208f108e106dcc13c212c2, 0x10ae2032800a9a0f7810504413883dfa02a010510013a036fa0db814a484ea88),
    (0x1f0208e106ccc13c212c2, 0x14b0012b894b0052b884ac0030104aa012a414aa052a403c84129c001d8004b0),
    (0x1f0208e1049c8498837860040, 0x4ef1e3bc7c041e),
    (0x1f0208e106dcc6ccc13c212c2, 0x10c0412d000ad8032004b380f2100658018903d7002880),
    (0x1f0208e1049c837c601800040, 0x10c6012d824b60ced1e3b47c179e),
    (0x1f0608e10498837c607c60040, 0x400803b600ed824b2001900),
    (0x1f0208e10498837c601c00040, 0x13d400f3003cc0403843b878ee1f05e792d1e),
    (0x1f0208e10498837c607860040, 0x419003ba00ee82),
    (0x1f9a8f0608e10498837c60040, 0x100200340105168e9bd4a4f92a5a),
    (0x1f0208e1049c837c609880040, 0x136e78ea1e4aa78151e),
    (0x1f020cfd88e10498837c60040, 0x4f7003aef0145b051792bbc),
    (0x1f0208e10498837c609c80040, 0x403843de78ec1e054792c1e),
    (0x1f0208e106ccc254413c212c2, 0x40400022412e984b990f996),
    (0x1f0208e105bca25c400800040, 0x4e8983a264a98c2a6341a80),
    (0x1f0608e10498837c602c20040, 0x400803a430e90e4b8301112) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_36 : Array (Nat × Nat) := #[ (0x1f0208e10498837c600c00040, 0x4ac002b004038428c18a30706a192e86),
    (0x1f0208e104988378601800040, 0x14be012f004bc052d1e),
    (0x1f0208e107f8e498837860040, 0x14be00305a4a7782fda),
    (0x1f0208e104988378607860040, 0x10ac003080),
    (0x1f0208e104988480837860040, 0x13c9692b1e),
    (0x1f020c798254412c208000040, 0x14c2f0c83c344f1300c),
    (0x1f020cf988e10498837860040, 0x14c2012bbc4a96d2a5e),
    (0x1f0208e104988378609880040, 0x14aa792c1e),
    (0x1fe307e304988254412c20040, 0x14c80131804c400c880),
    (0x1fe307e30498837c6254412c2, 0x534de4d001135a4ce0133064ca1933304cac13200),
    (0x1f020cf98c798254412c202c2, 0x14da0136000c3b135830adb13503),
    (0x1f0208e106dcc6ccc12c200c0, 0x537804dc4137110c3802b60),
    (0x1fe307ef24988254412c2, 0x10030005004e50138864861133864e51938804864933804e1c13790475c02b704d81132b64d84932b0),
    (0x1fe307ef27e304988254412c2, 0x404c00c00139f0475c13790),
    (0x1fe307e304988254412c200c2, 0x14e80076000c0002f80),
    (0x1f0208e10498837c637860786, 0x4765d474012d21) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_37 : Array (Nat × Nat) := #[ (0x1fef27e304988254412c2, 0x14ee412b104ec41340647701389e4ec5934004771938984ebc030f04da1133364da493330),
    (0x1fef2fe307e304988254412c2, 0x432104ebc074f0),
    (0x1f0208e104988378607c6, 0x14e97539804780539024781139000c1753a804d2013c204d2093c1e01200055a),
    (0x1f0208e10498837c6378607c6, 0x53a5d4ea013800002002b00),
    (0x1f0208e107f8e498837c60040, 0x404804be00efda3bf6cf5de),
    (0x1f0208e107fce498837860040, 0x431803c168f05b),
    (0x1f0208e104988378607c60040, 0x1002012c803c200f082),
    (0x1f0208e106dcc12c201c000c0, 0x53d0018c0063010a2013c804f2051a001bc4000b0),
    (0x1f0208e104988364601800040, 0x10c6013d844f614008018278609f454791a1e),
    (0x1f0208e10480837c601800040, 0x10c6013e004f804008018078601f452786f5a),
    (0x1f1a08e10498837c60040, 0x14f8013d84500013f844fc113eda3cc0062bc47c80f280184f5171e4b60915be4dd692f00),
    (0x1f1a08e10498837c601800040, 0x541000020140804f8013d8418c78619f458793c9e),
    (0x1f0208e104f88498837c60040, 0x54180188f116bc46ef11ede),
    (0x1f0208e107fce01800040, 0x54183504013f045060941014fc15430450a011f9f3ce00641e47e78f3811907d421e4be013d1e3d4007180),
    (0x1f0208e107fce37c601800040, 0x53f844fe15438419478651f4de787280),
    (0x1f0208e107fce498801800040, 0x150001400151000649e1927ca01e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_38 : Array (Nat × Nat) := #[ (0x1fef2fe307ef24988254412c2, 0x400c00c00138705084074f0),
    (0x1f7e68e10498837c607c60040, 0x400800c60d38001980066024ea007480),
    (0x1f0208e107fce498848080040, 0x10020031801976865db1d1693b9e),
    (0x1f020bfd68e107fce49880040, 0x433005140945005120c66da4e37068db4e36868de),
    (0x1f0208e107fce498807c60040, 0x10c601188019c0139001b8091d80),
    (0x1f9a8f7e68e10498837c60040, 0x431005180545815120856bc4cb6844bc40ef9335a),
    (0x1f0208e107fce37c609880040, 0x10c6005b3c132f1363c4daf05e9e),
    (0x1f0208e10498837c609800040, 0x546005140146800c404330019ef0733c48079211e),
    (0x1ffdef0208e10498837c60040, 0x5478051c0d33da12168585b16179345a),
    (0x1f0208e10498837c60fce0040, 0x5209e1a078739e4ec7921bc),
    (0x1f0208e10498837c608080040, 0x116b684b3c176f1481e),
    (0x1f0208e10498837c607c60786, 0x11d2013800468840080),
    (0x1f0208e104fce498837c60040, 0x5181e1b2791cbc1b5793c1e),
    (0x1f0208e10498837c601c60040, 0x5070041c0449004d201131e),
    (0x1f0208e10498831c607c60040, 0x1002011900464046d80478051e00),
    (0x1c0208e10498837c607c60040, 0x150e0148801b1746c5f4e974765d) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_39 : Array (Nat × Nat) := #[ (0x1f020c0208e10498807c60040, 0x5440345f7549001af746bdf),
    (0x1f0208e106dcc130212c2, 0x5480048a85480148a8005104ac013b80002c14a00527c54a01527c148e0525813b804520000b045200f170010000240),
    (0x1f0208e104988484837c60040, 0x100e1004803d078f41f3c5012b1e),
    (0x1fe3080c24988254412c200c2, 0x1062013b90003011490),
    (0x1f020c9988e10498837c60040, 0x11ab6922bc1d569225e),
    (0x1f020cf988e10480837c60040, 0x4340011568575a4116d49c0),
    (0x1f0208e10480837c609880040, 0x4008016f684d5a528785f5a),
    (0x1f0208e106dcc12c20300, 0x10dfa0378152f414b8052c0123a152a003f100dfa000b001140ec800084405104c000e400002c03781002c004003b3400240),
    (0x1f020cf98254412c208400040, 0x54c000fe0c138004e60fc0c3903037e00de4800bc),
    (0x1f0208e10498837c608400040, 0x153000c70000e0403840120033003d878ec9e3b281301e),
    (0x1f0208e1049883fc637c60040, 0x15320041da13d6c4f5e4c56931da),
    (0x1f020cf9837c608000040, 0x524033daf042034c80d30bc53200f73c14401245a3da00425a532f0f700144f1325a4c2014c3c530014b0c),
    (0x1f020cf9837c612c208000040, 0x4428314601010025d089abc535694b8c),
    (0x1f020cf983fc637c6254412c2, 0x1002f10b9214a550be014b8d4c80),
    (0x1f0208e10498837c607800040, 0x54580516094d800c404310411ef106bc41af91280),
    (0x1f020c8188e10498837c60040, 0x1123694e3c1636858dc) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_40 : Array (Nat × Nat) := #[ (0x1f9a88e10498837c609880040, 0x100200340114af0433c40a790b9e),
    (0x1fe30f9a88e10498837c60040, 0x10ce014f0253c014e804176905dc406f101be),
    (0x1f020cf988e1037c609880040, 0x43400110f10d3c408f1061e),
    (0x1f0208e104988480037c60040, 0x54f0053c0433800ce0550001576855db117694f9e),
    (0x1ffb8f0208e10498837c60040, 0x15440150804456904da4136d04de),
    (0x1f0208e10498837c60f980040, 0x111af1053c414f9123c),
    (0x1f0208e10498837c601880040, 0x1128784a1f43279141e),
    (0x1f0208e106dcc12c203c202c2, 0x452880a8010b800e08400b0),
    (0x1f0208e1049883fce37c60040, 0x45a5a12b6c5d5e4d56935da),
    (0x1f0208e104f98498837c60040, 0x1166f10c3c44ef124de),
    (0x1f0208e10418837c609880040, 0x40080130784c1f436790d9f),
    (0x1b0208e10498837c609880040, 0x54d02170f04dbc43a790f41),
    (0x18e107e304988254412c20040, 0x153401008034800c902),
    (0x18e107e30498837c6254412c2, 0x552dc548015186546c14d00),
    (0x1f020ab544988254412c202c2, 0x5538602585530d),
    (0x1f0208e106ccc254412c200c0, 0x5548055069541b02590fd10) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_41 : Array (Nat × Nat) := #[ (0x18e107ef27e304988254412c2, 0x10130030000be015490),
    (0x18e107e304988254412c200c2, 0x55500),
    (0x1f0208e104988378612c20786, 0x42b004ba2555da),
    (0x1d5648e104988254412c20040, 0x102168ae002b8080960),
    (0x19ed27e304988254412c2, 0x14ac40300055a29520655a515200559a0096854e1151b654e4951b0),
    (0x1d5648e10498837c6254412c2, 0x55660),
    (0x1f0207e304988254412c202c2, 0x40881),
    (0x1f0209cd24988254402c2, 0x102345560001220054954a09571e54a315718),
    (0x1f0209cd24988254412c202c2, 0x55600),
    (0x1f0208e105b4a254400800040, 0x4ad062b41d2e80),
    (0x1f0208e105bca498837860040, 0x13e108f843),
    (0x1f0208e104988378602c20040, 0x1002012e0c3e230f88e),
    (0x1f0208e104988488837860040, 0x13e769579e),
    (0x1fe308e107ef24988254412c2, 0x40580003015490),
    (0x1f564d5648e10498812c20040, 0x155708c15a2b630ad8e),
    (0x1fe309ed27e304988254412c2, 0x430003f4003210561c090f0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_42 : Array (Nat × Nat) := #[ (0x1fe307e304988254412c202c2, 0x1562009500556c43000305242f80),
    (0x1f0209ed29cd24988254402c2, 0x40088),
    (0x1fef28e107e304988254412c2, 0x1),
    (0x1f0208e104988378612c207c6, 0x1563d5580055768090c),
    (0x1f0208e10498837c617c60040, 0x4933c1e96c7a5e55768c142),
    (0x1f5648e10498837c617c612c2, 0x400b30e9803c48),
    (0x1f0208e105bca37c601800040, 0x10c60159025640c7e1e1f87c9000),
    (0x1f2e28e10498837c607c60040, 0x400801fa007e82560009080),
    (0x1f2e28e10498837c602c20040, 0x400800da6c3a0c1f2307c8e558303c0c),
    (0x1f9a8f2e28e10498837c60040, 0x10d2015981239687bbc41ef951da),
    (0x1f0208e105bca37c609880040, 0x11f6f07c3c54ef08e9e),
    (0x1f0208e10498837c608800040, 0x1566015a000d20433001fd088f3c49891099e),
    (0x1f020dfda8e10498837c60040, 0x11ff0881db20779525a),
    (0x1f0208e10498837c60bca0040, 0x149a9080a423e7956a4),
    (0x1f0208e10498837c608880040, 0x121f08803c20a915a9e),
    (0x1f0208e104988350402c20040, 0x10da6c00803fa30858c21638018c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_43 : Array (Nat × Nat) := #[ (0x1f0208e10498837c613820040, 0x4862a218acff5e),
    (0x1f0208e104bca498837c60040, 0x13f69083a4213795724),
    (0x1f0208e10498837c600c20040, 0x13f818fe07210195286),
    (0x1f0208e106dcc134212c2, 0x55a8049e855a8149e80c15e0b4615c80571655c81571615be056c0000b00da1811d8010000240),
    (0x1f0208e10498848c837c60040, 0x403843e878fa1f04719579e),
    (0x1f5648e10498822c212c202c2, 0x41b0c002cc3689),
    (0x1f0208e10488837c601800040, 0x10c6015d00574040080228788a1f56c78949e),
    (0x1d0208e10498837c607c60040, 0x55b8022b748adf56374955d),
    (0x1f020cb988e10498837c60040, 0x121b6927bc24b69275e),
    (0x1f020cf988e10488837c60040, 0x434002216893da4216d5c46),
    (0x1f0208e10488837c609880040, 0x400802270888bc57278945a),
    (0x1f0208e106dcc4988134212c2, 0x400b00da1802da),
    (0x1f1a08e10498837c612c20040, 0x55d84574615902276309d0c49439540c),
    (0x1f0208e107fce12c201800040, 0x1576115d85278789e1f55278a000),
    (0x1f0208e105a8a498837c60040, 0x49eaa27aaca0aa),
    (0x1f0208e106dcc2544130212c2, 0x40590002c002cc) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_44 : Array (Nat × Nat) := #[ (0x1f0208e105aca498837c60040, 0x127d089f4328519555a),
    (0x1f0209ed24988254412c20300, 0x152e00960001724028300a340088),
    (0x1f0208e10498837c602800040, 0x55e000d204348425e49088c42238c20c),
    (0x1f020ca988e10498837c60040, 0x1261695ebc26f689bdc),
    (0x1f0208e10498837c61bca0040, 0x1270f098c327379535a),
    (0x1f0208e106ccc498812c20040, 0x4aea42ba94fd16),
    (0x1f2e28e107e304988254412c2, 0x430004baa02d10),
    (0x1f0208e1049883786254402c2, 0x1557c80480),
    (0x18e107e304988254412c202c2, 0x40968554000849),
    (0x1f0208e107ece4988254412c2, 0x42f90),
    (0x1f564f2e28e10498837c60040, 0x4038003e6c0f8328af0a2be),
    (0x1f0208e106dcc12c201800040, 0x4318057c095f0303e00a39e28e7c2a80),
    (0x1f0208e106dcc2544134212c2, 0x1021782d1857e5802cc),
    (0x1f0208e104908488837c60040, 0x4008029168a45b57f695ff2),
    (0x1f1a08e104988254412c20040, 0x157c095f1a0c400a580294012802),
    (0x1f0208e1049882544130212c2, 0x10c8000060) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_45 : Array (Nat × Nat) := #[ (0x1f2e28e10498827c612c20040, 0x4398c2bc30af0e581b03a12),
    (0x1fe30f564af54498812c20040, 0x40c010300013842c6183aa50ea90af86),
    (0x1f0208e105bca254408800040, 0x1584680c1d58260b03c2c8f0b28c),
    (0x1f0208e106dcc498817c60040, 0x12cef0b16d2e9d961c2),
    (0x1f0208e10498837c6154412c2, 0x42d09),
    (0x1f0209ed24988254402800040, 0x158a640c1b58860b48c42430c200),
    (0x1f020cf98254412c208800040, 0x5598058e0d630004e60b52430a91098c),
    (0x1f0208e1049882dc412c20040, 0x158c0160980cc00b6a430c4cb796),
    (0x1f8a08e104988254412c20040, 0x158e0d611a56800b70c30e012882),
    (0x1f0208e104988254412c20342, 0x156a000060),
    (0x1f0208e1039a8254412c2, 0x15928160003037cc100590bd6198591ad6180),
    (0x1f0208e104988278612c20040, 0x10020023ec3ee34fb90),
    (0x1f0208e1079a839a8254412c2, 0x130400355f),
    (0x1f0208e10498835c602c20040, 0x400803fe30bc0c2e239640c),
    (0x1e0208e10498827c612c20040, 0x159430b9752e5dd64f5),
    (0x1f020d0208e10498817c60040, 0x13117565a12e774b9df) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_46 : Array (Nat × Nat) := #[ (0x1f0208cd24988254412c202c2, 0x56060),
    (0x1f0208e1049882544178612c2, 0x4c142),
    (0x1f0208e10498825c612c20040, 0x400802ee30bb8d2ec596666),
    (0x1e0608e104988254412c202c2, 0x101721650c),
    (0x1f020e0608e104988254402c2, 0x10178165b9),
    (0x1f0208e1049883282254402c2, 0x157e300063),
    (0x1f0208e106dcc4988154412c2, 0x1002c15c3c),
    (0x1f0208e1049882544134202c2, 0x1572000060),
    (0x1f3208e104988254412c20300, 0x54a8052a680100071a0c5b0070a8c58807070c58e07004c5c8),
    (0x1f0208e10498827c412c20040, 0x158861621a00200cb0c34c4cd316),
    (0x1f2a08e104988254412c20040, 0x158a65629c57800cb80428010a02),
    (0x1f0208e10498825441dcc12c2, 0x55eb1),
    (0x1fe30f9a8cf98254412c20040, 0x4120304808120053a010a8042a090a83),
    (0x1f9a88e104800254412c20040, 0x4120259c09671a53c00cada3296d6692),
    (0x1f0208e1049882544130012c2, 0x153e00bc802f2043b100ec59669c59a740060),
    (0x1f0208e106d44498812c20040, 0x159c09670354000d4123504ccc16) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_47 : Array (Nat × Nat) := #[ (0x1f0208e104988254412800040, 0x5679842c490b1342c591180),
    (0x1f020dab88e10498812c20040, 0x551003356968123356ccd5e),
    (0x1f2e28ed24988254412c200c2, 0x10f0002f00),
    (0x1f0e29ed24988254402c2, 0x15a98569805a409689e5a4316898),
    (0x1f0e2f0209ed24988254402c2, 0x40088),
    (0x1f0e29ed24988254412c202c2, 0x56501),
    (0x1f2e2af548ed24988254412c2, 0x15a4356abc),
    (0x1f020af54498833c6254402c2, 0x43a61),
    (0x1f0208e106dcc36c6254400c0, 0x56b345acd43a64),
    (0x1f2a28e10498837c612c207c6, 0x43a0c),
    (0x1f9a88e1049883fce254412c2, 0x400bd),
    (0x1f020af544988254412c203c6, 0x15ae002d4d),
    (0x1f5648e106dcc498817c612c2, 0x156bb56b845b1996aa0),
    (0x1f0209ed2498835c6254402c2, 0x1002216912),
    (0x1f2e2e5648e104988254402c2, 0x10bf216cd4),
    (0x1f2e28ed24988254410c202c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_48 : Array (Nat × Nat) := #[ (0x1f0208e105bca2544120200c0, 0x56d105b4441110),
    (0x1f5648e104988254413c612c2, 0x56e000b5316de0),
    (0x1f2e28e104988254412c20042, 0x15ba016e820ec30c212),
    (0x1f2e28e10498837c6254400c2, 0x15bc716e8c),
    (0x1f2e28e1049882544124200c2, 0x56f805b6102d10),
    (0x1f2e29ed24988254400c2, 0x10412411010092410480440002485ba016e1e5ba196e18),
    (0x1f2e29ed24988254412c200c2, 0x100a040280),
    (0x1f2e29ed28e104988254400c2, 0x100ba00428),
    (0x1f2e28c104988254412c200c2, 0x10f00001e8581802310),
    (0x1f0209ed28c104988254400c2, 0x4c160),
    (0x1f0208e105bca2544124200c0, 0x423005c0117005018400086),
    (0x1f2e29ed24988254402c200c2, 0x10b2000600),
    (0x1f2e28c104988254410c202c2, 0x1558003a01),
    (0x1f2e28e1049883504254402c2, 0x101830369b),
    (0x1f0208e106dcc5bca134212c2, 0x41046),
    (0x1f2e29ed24988254410c202c2, 0x43c00) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_49 : Array (Nat × Nat) := #[ (0x1f2e2af549ed24988254402c2, 0x56e86571856ab6),
    (0x1f2e28e10498837c6214402c2, 0x1572cc3c0c),
    (0x1f0208e106dcc37c6244400c0, 0x42d0656c1970b45c2d43c4c),
    (0x1f2e29ed270e24988254402c2, 0x156e843c00),
    (0x1f2e28e107fce4988254402c2, 0x55ec9),
    (0x1f2e28e10498831c6254402c2, 0x15b0655ab3),
    (0x1f2e28e10498835c6254402c2, 0x568990a0cd6f8c),
    (0x1f0208e105bca2544124200c2, 0x569005a4040086),
    (0x1e2208e104988254410c202c2, 0x1024056981),
    (0x1f2e2e0608e104988254402c2, 0x1015216a6c),
    (0x1f7e6e0208e104988254402c2, 0x43048),
    (0x1e0208e1070e24988254402c2, 0x43089),
    (0x1f5648e104988254415c612c2, 0x400b3),
    (0x1f2e28e10498833c6254402c2, 0x55ab3),
    (0x1f2e2ae504988254412c202c2, 0x5710c5c2183b1b5ac183109),
    (0x1f0208e107fce2544244400c0, 0x10d40031b05c531714d) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_50 : Array (Nat × Nat) := #[ (0x1f2e2e5248e104988254402c2, 0x42fc8),
    (0x1f2e28e104988254412c207c6, 0x1004000089),
    (0x1f2e28e104988254417c602c2, 0x4321b),
    (0x1f2a28e10498837c6254402c2, 0x565b3),
    (0x1fe30f2e28ed24988254412c2, 0x42f000a0403cb0),
    (0x1f5648e104988254417c602c2, 0x10e7203a60),
    (0x1f0208e10498836c6254400c0, 0x10b41971ca5c72c2f4c),
    (0x1f2a28e104988254412c207c6, 0x100400398c),
    (0x1fe30f2e29ed24988254402c2, 0x10b200060006c003c00),
    (0x1f2e28e10498837c6054402c2, 0x43a0c57f203c0c),
    (0x1f0208e10498837c6244400c0, 0x15c8d172350b3300080),
    (0x1f0209ed270e24988254402c2, 0x10e8000088),
    (0x1f0208e10498837c6250400c0, 0x572e05cb840664),
    (0x1f0208e105bca2544244400c0, 0x10d401734c5cd341b4c002182818),
    (0x1f020ae504988254412c202c2, 0x15cc31720602b8d718d),
    (0x1fe30f9a8cf9837c6254412c2, 0x104a0c128204a0174de5d00174db5d00974da5d00d73805ce0973835ce61739a5ce6d4e80) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_51 : Array (Nat × Nat) := #[ (0x1f020cf98af546dcc12c202c2, 0x104c20130604c0176005d81976085d7c975095d791750f5d7857511),
    (0x1f9a8f5648e106dcc12c200c0, 0x1056008f0723c0577000eab8b1880eaa0b18e5da2175e0),
    (0x1fef2f9a8cf98254412c2, 0x15ea216eb65e80d79831e20d7a895bad97a025e60878825e45974005e30d78025e30978035dfc175f05d8497398),
    (0x1fe30f9a8dfdacf98254412c2, 0x416035ee197b045ee217b012060881805dfb1770c),
    (0x1fe30f9a8cf98254412c200c2, 0x4878121e0016805f4017c800ea6d7c020ea697c03),
    (0x1f020af549ed2498807c6, 0x15fa6178805fa0178985f37577805f9c08eb25f9188e885d2097d9e),
    (0x1f020af549ed2498837c607c6, 0x417005f575778023e688f825ba348e9a5bb248e82),
    (0x1fe30f9a8cf98c988254412c2, 0x491012440011210448018000f078905a),
    (0x1ffb8fe30f9a8cf98254412c2, 0x10f0783c200600c3c21060081800),
    (0x1fe30f2e29ed24988254400c2, 0x41101044001880041841060),
    (0x1fe30f9a8cf985bca254412c2, 0x419810660029805ee197c825f20d7fb05fdb57f6c),
    (0x1f020cf989ed25bca254402c2, 0x1068081a000a8316e83),
    (0x1fe30f9a8cf98254412c202c2, 0x1052000e020380180826020180000ea757c800ea6d7c825d7b17c03),
    (0x1f0208e105bca37c612c200c0, 0x4230608c018110604456076581c03c10),
    (0x1f0208e106dcc5bca37c600c0, 0x41a8606a0028806070181c1),
    (0x1f564f2e28e10498837c607c6, 0x4290028260a0800f0303c48) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_52 : Array (Nat × Nat) := #[ (0x1fe30f7e69ed24988254412c2, 0x128800c00a),
    (0x1f020af549ed2498812c207c6, 0x1603bd7f000b0083abd),
    (0x1ff74f2e29ed24988254412c2, 0x47b011ec016e86601817f9e),
    (0x1f0208e106dcc5bca498807c6, 0x43c5a),
    (0x1f0208e105bca37c6254400c0, 0x58234608d41058),
    (0x1fe30f020af54498817c612c2, 0x1426297c8c60cf5829e),
    (0x1f020cf988e105bca254400c2, 0x1002183acd),
    (0x1fe30f0209c104988254402c2, 0x42329),
    (0x1f5648e10498837c6154412c2, 0x4320360f8c3c48),
    (0x1fe30f9a8cf98254412c2, 0x43c200f07810050400c02030f0843c1e040101002008083c210f08010010400002005d7197c985d70d7c9a5d7097c9b5d7c17c805d7b57c825d7b17c83),
    (0x1fe30f2e29ed24988254412c2, 0x100a040280010403c00),
    (0x1fe30f020bfd64988254402c2, 0x1082018423600197cc9),
    (0x1fe30f02096524988254402c2, 0x108ca5758a),
    (0x1fe30f5649ed24988254402c2, 0x16120180065f32182b6),
    (0x1f020af549ed24988250402c2, 0x108c083ad5),
    (0x1ff74f0209ed24988254402c2, 0x102a002d025f2c18355) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_53 : Array (Nat × Nat) := #[ (0x1f020b6309ed24988254402c2, 0x15d7600088),
    (0x1f0208e105bca250400c0, 0x5876561a01866461d9186816199585e4614001b6406a000258),
    (0x1f0208e106dcc5bca250400c0, 0x162189886361f901070),
    (0x1f0208e105bca250412c200c0, 0x16239188e5593900290),
    (0x1f5648e10498837c607c602c2, 0x4232160e603c48),
    (0x1f0208e10498837c6124200c0, 0x16244189110b2400080),
    (0x1f0208e105bca2544250400c0, 0x16279189e506d900418),
    (0x1fe30f9a8af546dcc12c2, 0x1630f58c3262fb58be262d898c40630c18bf062f818b6062bc18a0062bb58a0262b898a0d62b818a10),
    (0x1fe30f9a89ed25bca254412c2, 0x58c94632497c83),
    (0x1fe30f020cf985bca254402c2, 0x58d805f3458d19),
    (0x1fe30f9a8af545bca254412c2, 0x15d00d738c6284173ca629258e00),
    (0x1f020cf98af545bca254402c2, 0x5760863d958ebb),
    (0x1fe30fbeacf985bca254412c2, 0x1640018f805ea197f6d),
    (0x1fe30f9a88e105bca254400c2, 0x590805f34182b2),
    (0x1fe30f020af54498812c207c6, 0x10b4817c8c),
    (0x1f020cf988e106dcc37c600c0, 0x4b2066480191d6239d99147) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_54 : Array (Nat × Nat) := #[ (0x1f5648e105bca498837c607c6, 0x592825bb298c02),
    (0x1fe30fdec9ed24988254412c2, 0x164c0178045e0497448628698a24),
    (0x1f020cf98af54498812c207c6, 0x594805e2618a80650019395),
    (0x1ffb8f5649ed24988254412c2, 0x578075ce2178305cecd8a1e),
    (0x1f020af548e105bca498807c6, 0x578985e2098a80),
    (0x1f020af54498812c20780, 0x1637cd8d8b632f18c8062c01982765e01970665abd960065600b2b26436c2d20300f195001e25590890b520c000654f078bd),
    (0x1f020af54498837c612c20780, 0x590db62e0198866402d79bd),
    (0x1f5648e10498837c612c201c6, 0x15ea058c00650116ec8),
    (0x1f0209ed28e105bca254400c0, 0x1664e979cd587d819c0),
    (0x1f2e28e106dcc498812c207c6, 0x57f02),
    (0x1fdecf2e28e104988254412c2, 0x10ec00c2015f2c97cbc),
    (0x1f0209ed24988254412c20780, 0x16320984e766600a2051ec342d0c),
    (0x1f2e28e104988254412c201c6, 0x57b98000202d10),
    (0x1f020af548e105bca254400c0, 0x1566c99a4c002182bb263f3429d8),
    (0x1fe30f9a8cb98254412c2, 0x56fa02e8157e5323b783c216768010012120002006756d83005d7097c9b673c19c0066fb59b0066bc98f01),
    (0x1f020cf989ed24bca254402c2, 0x41a005aac19d83) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_55 : Array (Nat × Nat) := #[ (0x1f020af549ed2498817c612c2, 0x40402),
    (0x1f020cf98af54498817c612c2, 0x1650018f1566cf58ea1),
    (0x1f0208e106dcc5bca254400c2, 0x10b4019e58),
    (0x1f020af549c104988254402c2, 0x55c61),
    (0x1f5648e106dcc4988154412c2, 0x10a1557e1d),
    (0x1f0208e105bca254402c200c0, 0x4230067c099e82590201a08),
    (0x1f0208e106dcc5bca254400c0, 0x5904a6412c1070),
    (0x1f0209ed24988254402c20042, 0x56e806760d6d8002a182d0c),
    (0x1f5648e10498837c612c207c6, 0x10b4843c48),
    (0x1fe30f5649ed24988254412c2, 0x1650297c8d5f3218d1e),
    (0x1f0208e106dcc5bca214402c2, 0x59fc1),
    (0x1f0208e106dcc5bca054400c0, 0x5a0ca680c88eb0),
    (0x1f020cf985bca51ca254402c2, 0x57e3d),
    (0x1f020af549ed24988054402c2, 0x57580),
    (0x1f020dfdaaf544988254402c2, 0x15d8019c55),
    (0x1f020af5496524988254402c2, 0x59c90) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_56 : Array (Nat × Nat) := #[ (0x1f020efdc9ed24988254402c2, 0x168400c20066d2d9b55),
    (0x1f020a6549ed24988254402c2, 0x10b4099bcc),
    (0x1f0208e105bca25440dcc02c2, 0x1674c02d00),
    (0x1fe30f2e29e524988254412c2, 0x4218100a002c105be003cb0687996ab4),
    (0x1e020af549ed24988254402c2, 0x154721a1ef),
    (0x1f0208e105bca2544054400c0, 0x5a2b2688c82a18002182c18),
    (0x1fe30f9a89e524988254412c2, 0x12cb197c83),
    (0x1fd6cf2e28e104988254412c2, 0x400000b40d7c3c),
    (0x1f0208e106dcc498812c207c6, 0x15d6082d1e),
    (0x1f020ec30af544988254402c2, 0x5808c),
    (0x1f0208e108a105bca254400c0, 0x169119a3c668c9814c6),
    (0x1f0208e108c105bca254400c0, 0x1695a9a4ea5bc800e70),
    (0x1f0208e105b0a254400c0, 0x169885a58069881a581305d82d00614008b00),
    (0x1f9a88e1039a8254412c2, 0x10b57cc0df0acf42fa06a10da79869cada6986a1b5a78069d9da680),
    (0x1f0208e105bca5b0a254400c0, 0x16a3a9a8eb617908bf6),
    (0x1fe30cb88254412c2, 0x16c94db19e6c401b0dc6c119af986bc01aecc6b909ad9c6b40167306b3c1ac006ae01ab106abc9aa056a601a91269181a212668016380) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_57 : Array (Nat × Nat) := #[ (0x1f0e08e105bca254400c0, 0x4c0210b401b3a06cc01b2b26a3a9a58062791868061990ac06440608c80230e0791c),
    (0x1f020af54498817c212c2, 0x16dc01b68f69dc1b61a0b0102b866b7bdb5806d4fd67276d389b18d6c4f5b40268bb5a38b63ef5631e2ff802d48),
    (0x1f0208ed08e105bca254400c0, 0x16ce81a62061d908d20),
    (0x1f0208e106dcc12c2014000c0, 0x16e001ab006ac0428806de61b799002c02a80),
    (0x1f0208e107fce5bca254400c0, 0x5b8006af31abcd6e3c01858),
    (0x1f0208e105bca2544240400c0, 0x16b131ac4d063302818),
    (0x1f0208e105bca5a8a254400c0, 0x5ac926b24c2b12002182912),
    (0x1f0208e106dcc12c2050000c0, 0x5ba006ba0015816d001b9ca6e529b618),
    (0x1f020dfda8e105bca254400c0, 0x16e899af4c69bd9b14d69fd81658),
    (0x1f0208e10498837c607c600c0, 0x5b4806c00017026a069a732),
    (0x1f0208e1084105bca254400c0, 0x16bf49b1d26ea8016d8),
    (0x1fe30f0208e105bca254400c0, 0x54f406db61b5526d54c12d8),
    (0x1f0208e105bca25440e1000c0, 0x16b6e1b5a004ce1b720),
    (0x1f0208e105b0a254412c200c0, 0x10b40185006ec21bb095939023f6),
    (0x1f9a8f0208e1039a8254412c2, 0x1616802d5f),
    (0x1f2e29e504988254412c2, 0x572e9083a5a4e86f01979c86ee11a56667a11993658a7989e0623818660624498230604307918) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_58 : Array (Nat × Nat) := #[ (0x1f0e08e105bca254412c200c0, 0x161a01bc826ec2188e4236216d10),
    (0x1f020af544988254417c212c2, 0x161cacc21867d85a4935e6f56200),
    (0x1f0208e106dcc5bca25c400c0, 0x5bd506f544a0e0),
    (0x1f0208e106dcc5b0a254400c0, 0x5bde26f78d87e4),
    (0x1f9a8cf988e1039a8254412c2, 0x4c1800a17890bd),
    (0x1f0208e106d0c5bca254400c0, 0x108c01be606f984a0e0),
    (0x1fa20cf985bca254412c2, 0x170d4dc2865e81595135b549ac056ae14be807084dc1cd70401c09870001bfe56fdb9be8c5c39972666805d9198),
    (0x1f0e08e106dcc5bca254400c0, 0x5c3b26f981bde262189bd50),
    (0x1f020cf98af54498817c212c2, 0x1650008e15713c9c3095e8f5c40c683cd9121),
    (0x1f0208e106dcc5bca014000c0, 0x16e001be866fa1dbeb06fac4901e),
    (0x1f0208e106dcc37c6364600c0, 0x10b419bf046fc14909c),
    (0x1f020cf98254412c20c0000c0, 0x164801c08023c01c40071540c2d02c9419408),
    (0x1f020efdc8e105bca254400c0, 0x5c14a5e93481f0),
    (0x1f0208e105bca25440dcc00c0, 0x5c4c8709208fb0),
    (0x1f0208e1082105bca254400c0, 0x170701c3407168087c0),
    (0x1f020cf988e1039a8254412c2, 0x4c0df61e8000bc) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_59 : Array (Nat × Nat) := #[ (0x1f564f2e29e504988254412c2, 0x12a405b79b6f98d6d0c6af20bf836218581bc),
    (0x1f2e2ec308e104988254400c2, 0x5b8e0),
    (0x1f2e29ed2498825440ed200c2, 0x10a420a0a0),
    (0x1f9a88e106dcc25441fce12c2, 0x42d515ae49c660),
    (0x1f2e2d2a28e10498837c607c6, 0x171a003c0c),
    (0x1f5648e107fce498812c207c6, 0x1716f57a84),
    (0x1f5648e10498831c612c207c6, 0x59280718042d21),
    (0x1f5648e104988354412c207c6, 0x5c698000542d21),
    (0x1fffcf2e28e104988254412c2, 0x4cb8071c0174305d0c9743c),
    (0x1f0208e106dcc498812c201c6, 0x15d2002d1e),
    (0x1fe30f5649e524988254412c2, 0x165029750d671218ec2),
    (0x1f5ecf2e28e104988254412c2, 0x10ec00c20163d31753c),
    (0x1fe30f5649e504988254412c2, 0x130c65940a6e530b18d71f219142),
    (0x1f9a8f5649e504988254412c2, 0x130ec5c54f6e725768a7219d91d5),
    (0x1f020cf988e107fce254400c0, 0x5ba005dc05c86871f35c8f0),
    (0x1f0209ed24988254402c0, 0x5cb5172a01ca49727c5c900610182d0230079bb801e32d84000b430c0186ee1878d5) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_60 : Array (Nat × Nat) := #[ (0x1f0209ed24988254412c202c0, 0x161019840072e0566711ec0c7b0d),
    (0x1f020efdc9ed24988254402c0, 0x5cc485e92d7a55),
    (0x1f9a88e107fce254412c20fce, 0x4c2215ea497ae0),
    (0x1f7e68e106dcc498812c207c6, 0x15de097a82),
    (0x1ffb8f7e68e104988254412c2, 0x5cc805e01978085e0c17832),
    (0x1f020efdc8e10498812c207c6, 0x15e2017882),
    (0x1f020cf988e10254412c20fce, 0x16848179005e460c220),
    (0x1f2e2f0e08e104988254412c2, 0x4c2015e73179da),
    (0x1fdecf0e08e104988254412c2, 0x15e9317a5a),
    (0x1f7e68e104988254412c201c6, 0x57a805ea603b20),
    (0x1f5648e106dcc498812c207c6, 0x57f1a56bb57b82),
    (0x1f020af549ed24988254402c0, 0x1735202d02641357b55),
    (0x1f9a88e105bca254412c20fce, 0x10b49d7bc8),
    (0x1f564f0e08e104988254412c2, 0x1000002d1b63f317b5a),
    (0x1fe30f9a88e524988254412c2, 0x10b5717c03),
    (0x1fe30f5648ed24988254412c2, 0x509cc5f03582bc) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_61 : Array (Nat × Nat) := #[ (0x1f564ec308e104988254400c2, 0x15f419c8e0),
    (0x1f020af54498812c207c601c6, 0x57a80718002d20),
    (0x1f0208e105bca254412c20342, 0x15f8002d0f),
    (0x1f020cf988e1025441fce12c2, 0x57d803088193b5),
    (0x1f0208e1061cc498812c207c6, 0x57e9a),
    (0x1f020cf988e105bca254400c0, 0x17374000865ed3419f6),
    (0x1f0208e10498837c6054400c0, 0x173b21ce48069280080),
    (0x1f0209ed2498831c6254402c2, 0x40088),
    (0x1f9a8e5248e104988254402c2, 0x58088),
    (0x1f0208e1086105bca254400c0, 0x174149cfd273c800e58),
    (0x1f0208e105bca4988250400c0, 0x5d0e07438402f2),
    (0x1f0208e1049883706254400c0, 0x10d419d11c74474c1f0),
    (0x1f0208e10498837c6178612c2, 0x40080),
    (0x1f6209ed24988254412c2, 0x175051d38174dadd28074985d1915c1a00ae87419dce05736d9611e5cd857212640c15f18),
    (0x1f0e08e10498837c6254400c0, 0x175321d0e629329d11c5cb80792a2fb50ac00),
    (0x1f0208e106dcc498817c212c2, 0x42d1e73bc9cf905ed016086) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_62 : Array (Nat × Nat) := #[ (0x1f0208e107fce4988254400c0, 0x10c6c1d3e074f85d570),
    (0x1f0208e1049883646254400c0, 0x4350675071d41d),
    (0x1f0e08e10498837c6254412c2, 0x5d0e6608d172e05c048ac00),
    (0x1f6209ed2498837c6254412c2, 0x10ef71d3817565173615c2495900),
    (0x1f0208e106dcc3646254400c0, 0x175671d59d),
    (0x1f7e68e104988254412c207c6, 0x40100),
    (0x1f5648e10498827c612c207c6, 0x400b3),
    (0x1f5648e10498825441fce12c2, 0x400b3),
    (0x1f020af54498831c6254402c2, 0x1),
    (0x1d2a28e104988254412c207c6, 0x1),
    (0x1d2a28e10498837c612c207c6, 0x1),
    (0x1f020ec308e104988254400c2, 0x5d560),
    (0x1f2e2be309ed24988254412c2, 0x100a003c00),
    (0x1ffdef0208e104988254412c2, 0x17580111a1),
    (0x1f0208e104988254412c20fce, 0x1),
    (0x1f8a08e10498837c6254412c2, 0x59a03736c95a00) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_63 : Array (Nat × Nat) := #[ (0x1f0208e10498837c6254402c0, 0x175b20a249289300080),
    (0x1f2e28e104988254412c20fce, 0x1004000089),
    (0x1f0208e104988254412c201c6, 0x1),
    (0x1f9a8f0628e104988254412c2, 0x10040000bd),
    (0x1f0208e105aca2544134212c2, 0x1),
    (0x1f0209ed2498825c6254402c2, 0x56e1800221d712),
    (0x1f0e29ed24988254402c200c2, 0x10f0001080),
    (0x1f0209ed2498827c6254400c2, 0x568980a0c99d8d),
    (0x1f0209ed249882544024200c2, 0x15be05690275c100088),
    (0x1f0209c104988254402c200c2, 0x15a6000900),
    (0x1f2e2e2208e104988254400c2, 0x1015216a60),
    (0x1f0209c108e104988254400c2, 0x15970005e1),
    (0x1f0208e1048882544134202c2, 0x15720001da),
    (0x1f0208e1049883282054402c2, 0x157e3001c8),
    (0x1f0208e107d4c4988254402c2, 0x527c9),
    (0x1f0208e1049883104254402c2, 0x1006315ab3) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_64 : Array (Nat × Nat) := #[ (0x1f5648e1049883544154412c2, 0x1007d400b3),
    (0x1f0209ed290c24988254402c2, 0x5d7800e8000088),
    (0x1f0208e105bca2544134202c2, 0x1760080086),
    (0x1f020af5449883bc6254412c2, 0x1002c9d861),
    (0x1f0208e107fce2544134212c2, 0x102179d796),
    (0x1f0208e104988328212c207c6, 0x58380),
    (0x1f0e28e10498837c6254400c2, 0x5d948762719d92),
    (0x1fe30f02096d24988254402c2, 0x108ca43ab0),
    (0x1f630f0209ed24988254402c2, 0x1002203ae1),
    (0x1f0208e106dcc498817c600c0, 0x5da3c76754ba76),
    (0x1f1648e10498837c612c207c6, 0x56fe0),
    (0x1f564be309ed24988254412c2, 0x59b12671818eda),
    (0x1f020af5496d24988254402c2, 0x5dad5),
    (0x1f564ee309ed24988254412c2, 0x5db0a60ca982f2),
    (0x1f0208e106dcc498817c602c2, 0x5dbde),
    (0x1f0208e105bca2dcc254400c0, 0x5dcc87712084f0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_65 : Array (Nat × Nat) := #[ (0x1f5648e10498833c612c203c6, 0x10b4859dc8),
    (0x1f020cf988e103fce254412c2, 0x4c22063c2d8f35),
    (0x1f0208e106dcc498812c203c6, 0x166a002d1e),
    (0x1f020a7549ed24988254402c2, 0x10b409dd55),
    (0x1f0208e105bca2dcc254402c2, 0x10b401ddd8),
    (0x1f020efdc8e10498817c612c2, 0x1670f59c40),
    (0x1f0208e1069cc498812c207c6, 0x59c9a),
    (0x1f0208ed2498831c6254402c2, 0x56c19),
    (0x1f0209ed24988254421c602c2, 0x401805ae640088),
    (0x1f0208e105bca254400c20042, 0x1676119d8575c01d7010ee000086),
    (0x1f0208e1049883704254400c2, 0x43b8676271d89d),
    (0x1f0208e10498837c6178212c2, 0x40080),
    (0x1f0208e106dcc498813c612c2, 0x10b4799e40),
    (0x1f0208e10498837c625440042, 0x1779c80080),
    (0x1f0208e10498837c6244400c2, 0x40080),
    (0x1f0208e10498837c6054400c2, 0x40080) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_66 : Array (Nat × Nat) := #[ (0x1f0208e107fce4988254400c2, 0x5def0),
    (0x1f0208e1049883646254400c2, 0x1),
    (0x1f0208e1049883584254402c2, 0x40a8c5bc65d89b),
    (0x1f0e28e10498837c6254402c2, 0x1765216f92),
    (0x1f0208c10498837c6254400c2, 0x561e0),
    (0x1f020af149ed24988254402c2, 0x40088),
    (0x1f0208e105a8a4988250402c2, 0x1),
    (0x1f0208e107fce4988214402c2, 0x1),
    (0x1f0208e1049883646214402c2, 0x1),
    (0x1f0208a10498837c6214402c2, 0x55386),
    (0x1f020af548e10498815c612c2, 0x400b2),
    (0x1f0209a928e104988214402c2, 0x1),
    (0x1f0208e107fce4988054402c2, 0x1),
    (0x1f0208e10498831c6054402c2, 0x1),
    (0x1f0208e104908250412c200c0, 0x108c00230677d81df610079001f2),
    (0x1f7e68e10498837c6054402c2, 0x10e831d78c0e921d7c8) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_67 : Array (Nat × Nat) := #[ (0x1fe30e0208c104988254400c2, 0x161fa187e9),
    (0x1e0208c104988254412c200c2, 0x1593a164e9),
    (0x1d0208e10498837c6054402c2, 0x1),
    (0x1f0208e1049882504124200c0, 0x423000d419df8477e140190),
    (0x1f0208f90498837c6254402c2, 0x178009a00e766cc3101),
    (0x1f1a08e10498837c6254402c2, 0x178209a088769283100),
    (0x1f0208e107fce4988054400c0, 0x10c6c1e0c878121e148),
    (0x1f0208e107d0c4988254402c2, 0x55ec9),
    (0x1fdec8e10498825441dcc12c2, 0x1),
    (0x1f020bfd6498831c6254402c2, 0x1),
    (0x1ffdef0208e104988254402c2, 0x1786016869),
    (0x1f0208e1071ce4988254402c2, 0x1),
    (0x1f0208e104988250412c202c0, 0x5840061008c20c7898020e1083903b12),
    (0x1f0208e104908254412c20042, 0x56660),
    (0x1f5648e10498825441dcc12c2, 0x400b3),
    (0x1f0208e1075ce4988254402c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_68 : Array (Nat × Nat) := #[ (0x1f0208e1049882544124201c6, 0x1),
    (0x1f020ec3086104988254400c2, 0x5e158),
    (0x1f0208e1049882504120200c0, 0x178a00c086),
    (0x1f020be104988254402c2, 0x177eb5df0062231d080618307b695ca0078e0),
    (0x1f0e08e104988250412c200c0, 0x161a00bf8678d81df6008b88a90c),
    (0x1f0208e1075444988254402c2, 0x161c08c04b),
    (0x1f020be10498837c6254402c2, 0x178e018806640c43103),
    (0x1f0208e107fce4988250400c0, 0x431b078f81e3e1),
    (0x1f0208e1065644988254402c2, 0x1),
    (0x1f0208cd24988254412c200c2, 0x179180c091),
    (0x1f0208e1062e24988254402c2, 0x4c130),
    (0x1f0e28c104988254412c200c2, 0x179181e290),
    (0x1f0208c1049882544124200c2, 0x56405),
    (0x1f020ee309ed24988254402c2, 0x178aa40088),
    (0x1f0208e106dcc498815c612c2, 0x10b4799fc0),
    (0x1f020ae549ed24988254402c2, 0x10b409daf5) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_69 : Array (Nat × Nat) := #[ (0x1f0208e1077ce4988254402c2, 0x1),
    (0x1f0208e1049883180254402c2, 0x1792002082612318d8802a31941976d5c3b61),
    (0x1f0208a104988254412c201c6, 0x1),
    (0x1f0209ed28f544988254402c2, 0x10b409dbf3),
    (0x1f0208e1049883fce254402c2, 0x1),
    (0x1f020be309ed24988254402c2, 0x401800eb800088),
    (0x1e2208e104988254412c200c2, 0x1017216500),
    (0x1e0208e1049882544154402c2, 0x5579b),
    (0x1f5648e1049882544154402c2, 0x1),
    (0x1f0208e104988254417c600c0, 0x10b419e5c87952421e4),
    (0x1f0e28e104988254412c207c6, 0x15b0600100),
    (0x1f5648e104988254412c203c6, 0x56b80000c82d4c),
    (0x1f9a8e5648e104988254402c2, 0x5a188),
    (0x1f0208e1049882544178212c2, 0x56f005bc083b60),
    (0x1e2e28e10498837c6254402c2, 0x557b3),
    (0x1f564e2e28e104988254402c2, 0x555600c121e654) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_70 : Array (Nat × Nat) := #[ (0x1fe30e0208ed24988254402c2, 0x5e648),
    (0x1e0208e107fce4988254402c2, 0x55248),
    (0x1e0208e10498831c6254402c2, 0x55699),
    (0x1e0208e104988254417c602c2, 0x55548),
    (0x1f0208e1049082544124200c0, 0x14ba01e286),
    (0x1f0208f504988254412c202c2, 0x168821ce0c02b85e50d),
    (0x1f1608e104988254412c202c2, 0x5a28873a30003002b81e58c),
    (0x1f020be104988254412c202c2, 0x5898c5ca00a201),
    (0x1f020cf989e524988254402c2, 0x4350c),
    (0x1f0208e105b8a254400c0, 0x179e85e70079b31e7a079c05e6cd302002d0078a00bd80),
    (0x1f0208e105b8a254412c200c0, 0x10b401e2807a011e805021d82f16),
    (0x1f0208e106dcc5b8a254400c0, 0x17a329e8cb),
    (0x1e5648e10498837c612c207c6, 0x43521),
    (0x1f0209ed28e104988254403c6, 0x40088),
    (0x1ff74f0e28e104988254412c2, 0x400007a411835a),
    (0x1f0208e106d4c498812c207c6, 0x4351e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_71 : Array (Nat × Nat) := #[ (0x1f0208e1049883746124200c0, 0x17a629e98b),
    (0x1f0208e1049883746254400c0, 0x17a871ea1d),
    (0x1d2e28e104988254412c207c6, 0x1),
    (0x1f0208e104988254417c600c2, 0x1),
    (0x1fe30f0209e524988254402c2, 0x4018008ca43ac8),
    (0x1f0209e504988254402c2, 0x12894570001e321df800ee31ea187a619e6dd),
    (0x1f0e08e1049882544124200c0, 0x12fe01e7067aa11000477e103e0a0ee403b00),
    (0x1f0208e10498835c4254402c2, 0x130065e79b),
    (0x1f0209e504988254412c202c2, 0x15c001df80624307b000838de815),
    (0x1f564f0209e504988254402c2, 0x55d330ee31d3e364125e8d7),
    (0x1f020e7e68e104988254402c2, 0x42fc8),
    (0x1d7e68e104988254412c207c6, 0x1),
    (0x1f020ed6c8e104988254402c2, 0x1),
    (0x1f0208e104988254415c212c2, 0x5cf0068c003b60),
    (0x1f0208e10498833c2254402c2, 0x173e31a388),
    (0x1f020af104988254412c202c2, 0x174031a408) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_72 : Array (Nat × Nat) := #[ (0x1f0208e10498825441fce12c2, 0x1),
    (0x1f0208e104988254410c202c0, 0x4c2007a409e90c7ac040a8302a340100),
    (0x1f020ed2c8e104988254402c2, 0x1),
    (0x1f0208e104988254413c602c2, 0x1),
    (0x1f0208e105b88254400c2, 0x17a885eb8079b41ea207ae05e6d1),
    (0x1f0e08e1049882544120200c0, 0x179c01e7067b040bd102f4583b00),
    (0x1f0208e1049883744254400c2, 0x179e71e79d),
    (0x1f0208e105b8a2544120200c0, 0x17ae41eb91),
    (0x1f0208e105b88254412c200c2, 0x15b4016d017a021e809),
    (0x1f2a08e10498837c6254412c2, 0x59931664d15e00),
    (0x1f0208ed04988254412c202c2, 0x167a099e8c0839dec8508385ec93),
    (0x1f020ee104988254412c202c2, 0x169409a50c),
    (0x1f0208ed04988254412c202c0, 0x130801bb826ee31ed800839ded0308385ed0d),
    (0x1f2a08e104988254412c20042, 0x16f005bc047b801ee02),
    (0x1f0208e1072c24988254402c2, 0x169209a48c),
    (0x1f1a08e10498837c6254412c2, 0x43bda74e119008640c83100) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_73 : Array (Nat × Nat) := #[ (0x1f0208e104dc8254412c200c0, 0x5a90630a01d1867bc69ee8502b90b790),
    (0x1f5e4f0e08e104988254412c2, 0x4c29b6a731d25a),
    (0x1f6208e104988254412c200c2, 0x5aa0674a01e580),
    (0x1f0208e10498833c2254403c2, 0x174c19aa80),
    (0x1fef0f0e08e104988254412c2, 0x550407c1c1ef806b531ad5a),
    (0x1f5208e104988254412c202c2, 0x16b619ad88),
    (0x1f0208e104988254417c207c2, 0x16b801ae02),
    (0x1f0e08ed04988254412c2, 0x178d99ea8475339bc826cac9e3607aa49d4c86f231b2bc),
    (0x1f0e08ed04988254412c200c0, 0x5b3006cc183b010ec01e3662fc01e3602fc19ec10),
    (0x1f5208e104988254417c212c2, 0x16ce01b382),
    (0x1f0e08e104988254412c202c2, 0x59f0267c30010008399f08208381f08c),
    (0x1fe30f0e08e104988254412c2, 0x10040000c07c1c1f1106d549b55c),
    (0x1f0208e104988254417c202c2, 0x16d601b582),
    (0x1f0208e107fc64988254412c2, 0x16da09b683446795000),
    (0x1f0208e104988254412c207c2, 0x5b7006dc083b60),
    (0x1f0208e104bca254412c200c0, 0x42d007c209ec85599b82190) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_74 : Array (Nat × Nat) := #[ (0x1f0208e1049882544120000c0, 0x5f1007c419f1107c4451180),
    (0x1f020ec308e104988254400c0, 0x5f07077b81f071),
    (0x1fe30f0208e105b88254400c2, 0x14f901d3f07a349e8d3),
    (0x1fe30f2209e104988254412c2, 0x42a9024801f1e0041801061),
    (0x1f4609ed28e504988254412c2, 0x4bd497c831900c6de09bd3c),
    (0x1f0208e107fce49c8254400c0, 0x5b8007c929f24b7cbc1f1f0),
    (0x1f020be104988254412c207c6, 0x16f801be184f601d380082602080),
    (0x1fe70f5649e504988254412c2, 0x17ba01958a7d071f3877cd21bfbc),
    (0x1f6208e10498837c6254400c2, 0x17d205c006769203102),
    (0x1f7e6be104988254412c2, 0x5f51575055f4987cc49e01c72079f5637518df4807cd81e004720d971605c4495d98576013f00),
    (0x1f7e6be10498837c6254412c2, 0x10ef75d5955c449d5e35c5813f80),
    (0x1f0e08e107fce4988254412c2, 0x5403078f99abcc78f81abda),
    (0x1fc208e104988254412c200c0, 0x170201c08671401c50673221f58030e68c3a4),
    (0x1f6208e107fce4988254412c2, 0x170419c130),
    (0x1f0208f904988254412c207c6, 0x170809c21a0ef6df605),
    (0x1f0208e106d88254412c200c2, 0x170619c187) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_75 : Array (Nat × Nat) := #[ (0x1f0208f904988254412c20780, 0x5958065409959865469f71e0ef6df6837ba35eec9),
    (0x1f6208e104988254412c201c6, 0x5c28070a61f780),
    (0x1f0208e10498836c2254400c2, 0x170c19c307),
    (0x1f1a08f90498837c6254412c2, 0x5ec5a7e009c38e70f294080),
    (0x1f0e08e107fce4988254400c0, 0x541307e121f8e878f99f24a78f81f254),
    (0x1f0208e10498825441ec200c0, 0x171001c40630a00c2867d741f6c930d90c372),
    (0x1f1a08e104988254412c207c6, 0x5c4827126801000ef69f782),
    (0x1f0208e104988254412c20780, 0x5940065009941865069cc800ec7c3b220ec483b60),
    (0x1f020efdc8e10498817c212c2, 0x541bc783d1c7bd783c9c7c0),
    (0x18e1049883fb8254412c2, 0x178511c89878509c89a785b9c880785b1c882),
    (0x1f0208e107f0e4988254400c0, 0x542b07e3a1f8e97cbc1f2f6),
    (0x1ffb88e1049883fb8254412c2, 0x5433c),
    (0x1f0208e107fce3646254400c0, 0x431b07d471f51d),
    (0x1f0208e1049883fb8254412c2, 0x5b8806e209445a),
    (0x1c7e68e10498837c6254412c2, 0x54380),
    (0x1f0208e10498825441fce00c0, 0x5f7c87d985f93a) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_76 : Array (Nat × Nat) := #[ (0x1f0208e1049882544134412c2, 0x43b1671671c59d),
    (0x1fdec8e10498825441fce12c2, 0x1),
    (0x1f7e6d2a28e10498812c207c6, 0x5f980),
    (0x1f0208e104988254412800042, 0x5fa807e849fa137e8580100),
    (0x1f2e08e104988254412c2, 0x5fbe97ec01e2687ac05d6d072e05ca4978999eb0475b39cb8472931e2607ac49d6c872e49ca5a),
    (0x1f2e08e104988254412c202c0, 0x5ca8072a09ca8c00401e2687b601e2667b609e2607b631fa89),
    (0x1f0208e10498837c2254412c2, 0x172c31cb0d72c4111987ee496780),
    (0x1f020e0208e104988254402c0, 0x17efa5de60),
    (0x1fe208e107fce4988254412c2, 0x5fac07f005cc0073019cc30),
    (0x1ffdef0208e104988254402c0, 0x5fd007f3a5fc60),
    (0x1ffee8e104988254412c20fce, 0x17f6000100),
    (0x1f0208e104988254412c0, 0x1787a5fb00787a1fb0178799fb0478781fb12),
    (0x1f0208e104988254412c212c0, 0x1787a5c700787a1c70178799c70478781c71232e00cb8132e10cb92),
    (0x1fffcf0208e104988254412c0, 0x5fdc87f725fdcc7f769d660),
    (0x1fffef0208e104988254412c2, 0x5d60075805d60475849d660),
    (0x1f0208e104988254412c20002, 0x51180) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_77 : Array (Nat × Nat) := #[ (0x18e104988254412c20fde, 0x1),
    (0x1f0208e104988254412c20fde, 0x1),
    (0x1ffde8e104988254412c20fde, 0x511a1),
    (0x1f7e68e104988254412c20fce, 0x40100),
    (0x1f020efdc8e104988254412c0, 0x17f721fd69),
    (0x18e107fce4988254412c20fde, 0x1),
    (0x1f0208e10498825441fde12c2, 0x175801fe00),
    (0x1f0208e104988254412c201ce, 0x55140),
    (0x18e104988254412c20fdc02c2, 0x168401a10268431fe007fb21feca7fb51d600),
    (0x1f020ed388e10498825440042, 0x5fce0),
    (0x1f0208e104988254412c612c2, 0x1),
    (0x1f0628e104988254412c20042, 0x100401ff007fc09fa12),
    (0x1f0208e104988254412820042, 0x40100),
    (0x1ffb8f0628e104988254412c2, 0x100401fa12),
    (0x1f0208e1049883780254412c2, 0x173201cc8173211930c64c35931032e49934864d25934c32f815080),
    (0x1f0208e104988254412c20046, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_78 : Array (Nat × Nat) := #[ (0x1fdecf0e28e104988254412c2, 0x10ec01fec966d319b5a),
    (0x1f0208e107fde4988254412c2, 0x5d600),
    (0x1f564d2a28e10498812c207c6, 0x17e6002f8c),
    (0x1fe30f7e6bfd64988254412c2, 0x174e05d3800ae114480),
    (0x1f0208e107fce4988254402c0, 0x545307ff21d3e1),
    (0x1ffb8f0208e105bca254400c2, 0x10ee00008660d31834d),
    (0x1f0208e1049882544124000c2, 0x1800003b867a411e9057e8400100),
    (0x1f020ed348e104988254400c2, 0x1),
    (0x1f020bfd64988254412c20780, 0x15160200817e4bdd383),
    (0x1f0209ed26dcc4988254402c0, 0x1518c20149002202bb063f2d8fd5),
    (0x1f9a08e10498837c6254412c2, 0x18040e005a7fe09cd08734c94680),
    (0x1f0208e106dcc4988254412c0, 0x54730),
    (0x18e10498837c6254412c20fde, 0x54780),
    (0x1f1e68e104988254412c201c6, 0x1004020180),
    (0x1f9a8f1e68e104988254412c2, 0x43b1e808f4c21f64e5993e4),
    (0x1f0208e1073ce4988254402c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_79 : Array (Nat × Nat) := #[ (0x1fe30f1e68e104988254412c2, 0x10040000c0),
    (0x1f0208e10498825441fce02c2, 0x1),
    (0x1f0208e1049883fde254412c2, 0x5d600),
    (0x1f0208e104988254412c203ce, 0x1),
    (0x1f0208e104988254413ce12c2, 0x1),
    (0x1f1e68e104988254412c207c6, 0x171801c618004020180),
    (0x1f020a4308e104988254400c2, 0x5f932),
    (0x18e104988254412c20f9807c6, 0x594806520994986526a020080862023c808f9d600),
    (0x1f0208e1065cc498812c207c6, 0x59b9a),
    (0x1f0208e10498825441dce12c2, 0x1),
    (0x1f0208e1049882dcc12c207c6, 0x59d18),
    (0x1f0209ed2498825440c1000c2, 0x42b08),
    (0x1f020ed748e104988254400c2, 0x1),
    (0x1f0e2ec308e104988254400c2, 0x180d8202f0),
    (0x1f020ecf28e104988254400c2, 0x180d820361),
    (0x1c7e68e104988254412c207c6, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_80 : Array (Nat × Nat) := #[ (0x1f0628e104988254412c202c2, 0x56d805b608010080e060384),
    (0x1f564f0628e104988254412c2, 0x400000b46d9e5a),
    (0x1f0208e10498832c6254402c2, 0x1),
    (0x1f0208e10498837ce254412c2, 0x1),
    (0x1f0208e104988254412c202c6, 0x1),
    (0x1f0208e1049883546254402c2, 0x1),
    (0x1f1648e104988254413c612c2, 0x10d5320460),
    (0x1f0208e1049ca2544124200c2, 0x1810120405),
    (0x1f0628e104988254412c200c2, 0x175c00010080e05ff02),
    (0x1f0e28e104988254412c20042, 0x167610000680e01e912),
    (0x1f0208e1049082544124200c2, 0x55280),
    (0x1f0e28ed24988254412c2, 0x181211d94e81249d948),
    (0x1f0e28ed24988254412c200c2, 0x1),
    (0x1f5248e104988254417c612c2, 0x1),
    (0x1f0e28e1049882544124200c2, 0x60484810103510),
    (0x1f0208e1049883746254400c2, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_81 : Array (Nat × Nat) := #[ (0x1f0208e1049882544120200c2, 0x40100),
    (0x1f2628e1049882544124200c2, 0x1814016900),
    (0x1f2628e104988254412c200c2, 0x15be056900000220382),
    (0x1f0208e1049882544134612c2, 0x1),
    (0x1f0208e10498836c6254400c2, 0x1),
    (0x1f0208e104988254413c600c2, 0x1),
    (0x1fe30f0e28ed24988254412c2, 0x10c84202f0),
    (0x1f0208e10498837c6014400c2, 0x40080),
    (0x1f0208e1049883600254400c2, 0x605806421990870ee19db5876d643b64),
    (0x1f7a08e104988254412c2, 0x179311e499666f9999865c19e4c27927199bc666699708793b9e48166759998065cc1e4ec7921199d4666099732),
    (0x1f7a08e104988254412c20780, 0x5978065e09979865e68010081771f71e81769f7208166df70c8160df748),
    (0x1f0208e107ec24988254412c2, 0x166009980366031980d),
    (0x1f7a08e10498837c6254412c2, 0x605dc8020605da8021198866622198b0662c94d80),
    (0x1f020af549e524988254402c2, 0x60655),
    (0x1f020ee30af544988254402c2, 0x5a18c),
    (0x1f0208e105bca4dcc254400c0, 0x6074a81b2c9cf0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_82 : Array (Nat × Nat) := #[ (0x1f2e28e10498833c6254403c6, 0x42d39),
    (0x1f0208e105bca4988254403c6, 0x166a002d36),
    (0x1fe30f2629e524988254412c2, 0x10860421800b04205000eb203ac9),
    (0x1f2e28e104988254412c203c6, 0x1004000089),
    (0x1f3e68e104988254412c203c6, 0x40100),
    (0x1f0208e104988254412c207ce, 0x1),
    (0x1f0208e107dce4988254402c2, 0x1),
    (0x1f020edec8e104988254402c2, 0x1),
    (0x1f0208e104988254412c200c6, 0x1),
    (0x1e0208e1072e24988254402c2, 0x555c8),
    (0x1f1648e104988254417c612c2, 0x15a20207e0),
    (0x1f0e28ed24988254412c202c2, 0x43a00),
    (0x1f2a28e104988250412c202c2, 0x10e830398c),
    (0x1f2628e104988254410c202c2, 0x6078281e060481),
    (0x1f0208e104bca254412c20342, 0x182008350f),
    (0x1f0208e1065cc498817c612c2, 0x5dac0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_83 : Array (Nat × Nat) := #[ (0x1f0208e106d4c498817c612c2, 0x4351e),
    (0x1f0208e10498836c6214402c2, 0x1),
    (0x1f0209ad28e104988214402c2, 0x1),
    (0x1f0208e10498833c6054402c2, 0x1),
    (0x1f0208e10498830c6254402c2, 0x1),
    (0x1e0208e10498833c6254402c2, 0x55348),
    (0x1f020e1248e104988254402c2, 0x1),
    (0x1f0208e1049882544150402c2, 0x100630321b),
    (0x1f0208e105b8a2544130212c2, 0x53b800e6403500),
    (0x1f0208e1049882dcc17c612c2, 0x5dbc0),
    (0x1f0208e104988254411c602c2, 0x1),
    (0x1f7e68e104988254417c602c2, 0x10e7213b9b),
    (0x1f0208e104988214417c602c2, 0x1),
    (0x1d0208e104988254417c602c2, 0x1),
    (0x1f0208f904988254417c612c2, 0x1770083bdb8221606b3),
    (0x1f1a08e104988254417c612c2, 0x1772083bda8240a0732) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_84 : Array (Nat × Nat) := #[ (0x1f0208e1049883fce254400c0, 0x609488238609b4),
    (0x1f1648e104988254412c203c6, 0x100400354c),
    (0x1f0208e104988254417ce12c2, 0x1),
    (0x1f0208e1049883146254402c2, 0x1),
    (0x1f0208e1061644988254402c2, 0x1),
    (0x1f0208e1065244988254402c2, 0x1),
    (0x1f020ac308e104988254400c2, 0x609b8),
    (0x1f524f0e28e104988254412c2, 0x100400351b),
    (0x1f0209e524988254402c200c2, 0x56f8082a020780006020a00),
    (0x1f0208e1069cc498817c612c2, 0x60640),
    (0x1f0208ed2498835c6254402c2, 0x15a2660a8c),
    (0x1f0208e105b8a4988250402c2, 0x1),
    (0x1e0208e10498835c6254402c2, 0x55719),
    (0x1f020ee308ed24988254402c2, 0x56cc8),
    (0x1fc30f0e28e104988254412c2, 0x1004016cc9),
    (0x1f464f0e28e104988254412c2, 0x100001dd5a) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_85 : Array (Nat × Nat) := #[ (0x1f0208e1049883bce254412c2, 0x1),
    (0x1f164f0e28e104988254412c2, 0x100001ddda),
    (0x1f0e28e10498835c6254402c2, 0x6050c),
    (0x1f0208e104bca2544124200c2, 0x182a020784),
    (0x1f0e28ed24988254410c202c2, 0x43a000e8043980),
    (0x1f0e28c104988254410c202c2, 0x60b00),
    (0x1d5648e104988254417c612c2, 0x404b3022320b60),
    (0x1f020d5648e10498817c612c2, 0x409750c031e63c),
    (0x1f0208e105b88254402c200c2, 0x15b401eb8182e21e982),
    (0x1f0208e105b8a2544124200c0, 0x42d0078a020b8482e141090),
    (0x1f0628e104988254410c202c2, 0x56d808100a0a03),
    (0x1e0e28e104988254412c202c2, 0x405c8593a1e461),
    (0x1e2e28e104988254412c200c2, 0x52e90),
    (0x1f020e0e28e104988254402c2, 0x13058405e0),
    (0x1f0209cd28e104988254400c2, 0x555e1),
    (0x1e2e28e104988254410c202c2, 0x60b010122405c8) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5_86 : Array (Nat × Nat) := #[ (0x1f0208e1049883786250402c2, 0x555f2),
    (0x1e020d0208e104988054402c2, 0x1),
    (0x1f0208e1049883346254402c2, 0x1),
    (0x1f0208e104988254415c602c2, 0x1),
    (0x1f0208e1060e24988254402c2, 0x10ac240830),
    (0x1f020e1648e104988254402c2, 0x1),
    (0x1f0208e104988254412c20346, 0x1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock5 (b : Nat) : Array (Nat × Nat) :=
  if b < 43 then
    if b < 21 then
      if b < 10 then
        if b < 5 then
          if b < 2 then
            if b < 1 then
              certificateBlock5_0
            else
              certificateBlock5_1
          else
            if b < 3 then
              certificateBlock5_2
            else
              if b < 4 then
                certificateBlock5_3
              else
                certificateBlock5_4
        else
          if b < 7 then
            if b < 6 then
              certificateBlock5_5
            else
              certificateBlock5_6
          else
            if b < 8 then
              certificateBlock5_7
            else
              if b < 9 then
                certificateBlock5_8
              else
                certificateBlock5_9
      else
        if b < 15 then
          if b < 12 then
            if b < 11 then
              certificateBlock5_10
            else
              certificateBlock5_11
          else
            if b < 13 then
              certificateBlock5_12
            else
              if b < 14 then
                certificateBlock5_13
              else
                certificateBlock5_14
        else
          if b < 18 then
            if b < 16 then
              certificateBlock5_15
            else
              if b < 17 then
                certificateBlock5_16
              else
                certificateBlock5_17
          else
            if b < 19 then
              certificateBlock5_18
            else
              if b < 20 then
                certificateBlock5_19
              else
                certificateBlock5_20
    else
      if b < 32 then
        if b < 26 then
          if b < 23 then
            if b < 22 then
              certificateBlock5_21
            else
              certificateBlock5_22
          else
            if b < 24 then
              certificateBlock5_23
            else
              if b < 25 then
                certificateBlock5_24
              else
                certificateBlock5_25
        else
          if b < 29 then
            if b < 27 then
              certificateBlock5_26
            else
              if b < 28 then
                certificateBlock5_27
              else
                certificateBlock5_28
          else
            if b < 30 then
              certificateBlock5_29
            else
              if b < 31 then
                certificateBlock5_30
              else
                certificateBlock5_31
      else
        if b < 37 then
          if b < 34 then
            if b < 33 then
              certificateBlock5_32
            else
              certificateBlock5_33
          else
            if b < 35 then
              certificateBlock5_34
            else
              if b < 36 then
                certificateBlock5_35
              else
                certificateBlock5_36
        else
          if b < 40 then
            if b < 38 then
              certificateBlock5_37
            else
              if b < 39 then
                certificateBlock5_38
              else
                certificateBlock5_39
          else
            if b < 41 then
              certificateBlock5_40
            else
              if b < 42 then
                certificateBlock5_41
              else
                certificateBlock5_42
  else
    if b < 65 then
      if b < 54 then
        if b < 48 then
          if b < 45 then
            if b < 44 then
              certificateBlock5_43
            else
              certificateBlock5_44
          else
            if b < 46 then
              certificateBlock5_45
            else
              if b < 47 then
                certificateBlock5_46
              else
                certificateBlock5_47
        else
          if b < 51 then
            if b < 49 then
              certificateBlock5_48
            else
              if b < 50 then
                certificateBlock5_49
              else
                certificateBlock5_50
          else
            if b < 52 then
              certificateBlock5_51
            else
              if b < 53 then
                certificateBlock5_52
              else
                certificateBlock5_53
      else
        if b < 59 then
          if b < 56 then
            if b < 55 then
              certificateBlock5_54
            else
              certificateBlock5_55
          else
            if b < 57 then
              certificateBlock5_56
            else
              if b < 58 then
                certificateBlock5_57
              else
                certificateBlock5_58
        else
          if b < 62 then
            if b < 60 then
              certificateBlock5_59
            else
              if b < 61 then
                certificateBlock5_60
              else
                certificateBlock5_61
          else
            if b < 63 then
              certificateBlock5_62
            else
              if b < 64 then
                certificateBlock5_63
              else
                certificateBlock5_64
    else
      if b < 76 then
        if b < 70 then
          if b < 67 then
            if b < 66 then
              certificateBlock5_65
            else
              certificateBlock5_66
          else
            if b < 68 then
              certificateBlock5_67
            else
              if b < 69 then
                certificateBlock5_68
              else
                certificateBlock5_69
        else
          if b < 73 then
            if b < 71 then
              certificateBlock5_70
            else
              if b < 72 then
                certificateBlock5_71
              else
                certificateBlock5_72
          else
            if b < 74 then
              certificateBlock5_73
            else
              if b < 75 then
                certificateBlock5_74
              else
                certificateBlock5_75
      else
        if b < 81 then
          if b < 78 then
            if b < 77 then
              certificateBlock5_76
            else
              certificateBlock5_77
          else
            if b < 79 then
              certificateBlock5_78
            else
              if b < 80 then
                certificateBlock5_79
              else
                certificateBlock5_80
        else
          if b < 84 then
            if b < 82 then
              certificateBlock5_81
            else
              if b < 83 then
                certificateBlock5_82
              else
                certificateBlock5_83
          else
            if b < 85 then
              certificateBlock5_84
            else
              if b < 86 then
                certificateBlock5_85
              else
                certificateBlock5_86
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_0 : Array (Nat × Nat) := #[ (0x1f0208e104988254412c2, 0x10048401200030000400048c011e002f4003d00488011f002f0003c004b40118002cc0033004b00119002c80032004a8011c002c00030005a40100002240009005a00101002200008005980104002180006005800112002000000),
    (0x1f0208e104988254412c20040, 0x100660018001060040000e00032100a00020000c80028100804031e00a100204005800198004480180),
    (0x1f0208e104988254412c202c2, 0x101da4070001600018901a00060801a08060601a300600002240580005a0050001280000800598050201278000600580050c012600000000240189),
    (0x1f0208e104988254412c212820040, 0x4088002000040001e48079301e580712),
    (0x1f0208e104988250412820040, 0x40a9802a000a0002654090002650090102648090401d80018001c480198),
    (0x1e0208e104988254412c202c2, 0x40e80016000e01036200e04036180e12036000d69032000c4802e040b7102e100b6f02e480b69006840889),
    (0x1f0208e104988250412c212820040, 0x1020000f8003c480f1303c580112),
    (0x1f0209e104988254402c2, 0x1075441ca0070001ba906c8c1a9e0681819bd06400189f0601817bc06cb41a980680019b30641818990600017b205ca8171c05a00163005600156905200144804e00130004a001208047b411020421810060478c110c042001000),
    (0x1f0608e104988254412820040, 0x108260200007e001f15006001e94078001d9207a481e02076500f6002400079200a000200),
    (0x1f0208e1049883544254402c2, 0x40bdd09e84270009a08270209a00262d072601c0c096e418ac0946c248e05ee018aa09474248c05ed824150062423b308c00229b08800060008600130c084301200),
    (0x1f0208e1049c84988254412820040, 0x4280007a481e9302648031e),
    (0x1f0208e10498837c60040, 0x42c830b2082c040af002c850b2002c010aef42c840b2042c000aef02b030aa002a030a60c2b020aa042a020a6082b000aa102a000a600280308a841f8005168280208a801f810516c280008a781f840517829000a3680a00),
    (0x1f0208e10498837c612820040, 0x42f1b0ba002e030b6242f1a0ba042e020b6202f180ba102e000b618041800600231508000149208c5020010524c23120801014960b4480a80016480400),
    (0x1f0208e10498837c612c20040, 0x10bc6c30800c00c2d890bc6830810c0082d880bc6030840c0002d8602060019808e8420800544823a008204151308e782084054582fda03e000c5a016480800),
    (0x1f0208e10498837c6254412820040, 0x1056481593056580d1203a480080),
    (0x1f0208e1049882544124200800040, 0x10b60032860401010050481000000c81832070c6183100) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_1 : Array (Nat × Nat) := #[ (0x1f0208e105b8a4988254412820040, 0x432800b80010920424c06120845804aa),
    (0x1f0208e1049882544128202820040, 0x42e800cc00131204448111401430068c),
    (0x1f0208e1049884908254412820040, 0x10bc6011e60479c2192088480166),
    (0x1f0208e104988250412c200800040, 0x10d2002d860d06034190ce00199e0667c2586000182780),
    (0x1f0208e106dcc4988254412820040, 0x10d2603018068481a1302c481c160378000b0),
    (0x1f0208e104988250412c202c20040, 0x10c2003500098001b0006c080100038300b8c),
    (0x1f0208e1049884888254412820040, 0x10bc001aaa06aac1caa0d648012a),
    (0x1f0208e1049882544128208000040, 0x10e0002bbc0de0037000da60164205f0817c4000f03612),
    (0x1f020cf988e104988254412820040, 0x438000b000169209a4824930925800bc),
    (0x1f0208e1049882544128209880040, 0x10b20018a405c90251e004782712),
    (0x1f0208e104988254412820040, 0x4041802000038007c5424000e4481f1409004391307c4824040e4580760022000112000003880),
    (0x1f0208e104988254412c202c20040, 0x10c20001980d4003a000e600398201a30050c),
    (0x1f0208e104988254417c612c2, 0x102cb44100102644002102704000005a43f800fc0c0009015703e810f8203da0015683e840f8183d9e000cc01120020001180f4003ce00f0043be20f0103be00ed8035180eb800548),
    (0x1f0208e10498827c6254412c202c2, 0x401890180041921046001600ea483500),
    (0x1f0208e104988254412c200c2, 0x102e04448002e004481110004386110184380012843a80012803a8100598430010a78000600580430610a6000000f6404210),
    (0x1f0208e104988254412c202c200c2, 0x44500112000b800ea043b000c4400008) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_2 : Array (Nat × Nat) := #[ (0x1f0208e1049882544250412c202c2, 0x40e0c018000b8c006600498),
    (0x1f2e28e104988254412c202c2, 0x103a0007001180045881180845861183045800022401000e200448010480448210478448c104600409020240389),
    (0x1f0208e10498837c6254412c2, 0x4055d0fe003f030f684055c0fe043f020f680055a0fe103f000f678061811a54061911a50061c11a48059200448060011b8c060111b88060411b8005e00058005e0016480418010000380),
    (0x1f2e2f0208e104988254412c202c2, 0x101da40e80020240421),
    (0x1f0208e10498837c6254402c2, 0x40bdd09e844a00126084a0212600490012230480011e38480211e30461201a3046e31160043801008043821007847330880005e01143004180c2000380),
    (0x1f0208e10498837c6254412c202c2, 0x40d801160046120c2004ab3112480400),
    (0x1f0208e104988254410c202c2, 0x4076903804418000624060811804440310218440d1020006091180007680380041810062044021021c440c102040189006200101004003880),
    (0x1f0208e104988254412c210c202c2, 0x40e01118000e001180407000ec0007010ec040009000200500),
    (0x1f020e0208e104988254412c202c2, 0x40e80022244b09),
    (0x1f0208e104988254412c209880040, 0x42c80134784c9e130784b9e),
    (0x1f0208e106dcc4988254412c202c2, 0x42cb011040498011e08478c0ff8043080f8c03d80019983b84019803b92),
    (0x1f0208e1049882544214412c202c2, 0x4480001a303c0001b243c1901524050c136040000),
    (0x1f0208e1049884888254412c20040, 0x42f0013aa84eab138a84a9e),
    (0x1f564f0208e104988254412c202c2, 0x10bccc4f000c40c0de91223004e9014303f030000046800198c3c92),
    (0x1f0208e104988254412c2054402c2, 0x4490001a303d0001b203d1801520050c0fe000000),
    (0x1f0209e104988254412c202c2, 0x40f6903c00158014c00148009024218804c0012801544011ed1521054060401811e315248540004000538914c00150014bc4520114624511013bb45084140784f8d13b8c5092140604f8300a242409) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_3 : Array (Nat × Nat) := #[ (0x1f0608e104988254412c212820040, 0x40900080002080004485592156500f12),
    (0x1f0208e1049883544254412c202c2, 0x4098008c0006000c40c218015a48128c04800239b12acc050c0020000001398c5212158545103),
    (0x1f0208e10498837c612c212820040, 0x102200000014c48531314c580c92),
    (0x1f0208e10498837c6254412c20040, 0x102060080014e00538114e104b00),
    (0x1f0208e104988254412c200800040, 0x42d800b6184f8013e04510013e184f87144183d80),
    (0x1f0208e105b8a4988254412c20040, 0x10060032800b800502a140ac0086158100b60),
    (0x1f0208e104988254412c202820040, 0x42e800d400520c14230508e02e300100),
    (0x1f0208e105bca4988254412820040, 0x42d800c00054121504c1296036480086),
    (0x1f0208e1049882544128202c20040, 0x4308002200330000000568c15230548e038300100),
    (0x1f0608e104988254412c20040, 0x109060240008260208007e00032100000388016080578015c00581e15e08570201f8024180e5800792090003912),
    (0x1fe30c988254412c2, 0x117f005f1e17a005e5a177185d18172605c4c16f685b1c16a605a60177c05d00172005c1016fc85b0416a005a12167805992164005880),
    (0x1f2e29e104988254412c2, 0x46f091bb406e001b6406d0b1b3386c061ae946b281aa7c6a061a7086d151b3206c001ae6c6b2e1aa646a001a6d0692a1a47068b01a0c015e9053a4396919fa0676819a00660019600654819240641018f98636618a10620418618613618218601e18f80636018a486212186006130182006018),
    (0x1f0608e10498837c6254412c2, 0x4775d1da0076001d60c755c1d20474021ce80755a1d21074001ce78732d1cb2072121c66c712c1c26470141bee0712a1c27070121bed8531201e4873691ca3072601c60c71681c20470621be8071661c21070601be78536001f8053600578014e0056485312052482098082001f80),
    (0x1f0a08e104988254412c20040, 0x41998040106f9818210601c0d06032001f4607c801f0007b861ec007a801e88079801e400789e1e008778213b8034180e6483200),
    (0x1f0a08e10498837c6254412c2, 0x122174879a21c1886892197085812140884a01436884041d018839e20c6082922086481922047080921f6483992200087fe61fc047ee60699854041c1986184184d07e6013b807e601f6487d181f2007c00),
    (0x1f0208e504988254412c202c2, 0x48f6923a007d800c8248e0d236008d021fc181b0015230708018a30620c232247d80139a08c0722e048b0213b9c8a82228784f8701f841b000e584508c22660890c2224c028113e243209) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_4 : Array (Nat × Nat) := #[ (0x1f020ae104988254412c202c2, 0x4118006a00638c1c400630c23ba48f001f800340925404948025010938624c308100232847e0024ba89201246cc910a1339c86042427890070e78c750c23e604f9b13e843409),
    (0x1f0208e1049c8254412c200c0, 0x109e189580268009980264001b8015418718019218640626284980025e0898a026004978313998278601f901b800e590510625c609680258400284148409580),
    (0x1f2e2f0608e104988254412c2, 0x111230520c27424925021c089ca8270849b882742c924e21c009ca52708c9b8626c5452481d8008b1b018b4468026ba44e6926ba4448c2680c99832640c8d811ff888d841ff801c6004a48726019648655a),
    (0x1f2208e104988254412c200c2, 0x127e040b811120095900740013011ca006681198048e00200188e06200005188112009f2027a009e0013bb08c02276784f8c13b888c0c276604f8222c409590),
    (0x1f0208e10498832c2254402c2, 0x40bdd27f749a8009e84a18028420a1822841821ad07200678c1cc00670c01a300600147a49a80135a888012828091221359c880428278911f22ce427a10e98c770c28060511b),
    (0x1f8208e104988254412c20040, 0x416040580468041a00458830de60378029660a58029400a4bc29000a38c28c80a28028800a31e28a08a202133803798132483780),
    (0x1f8208e10498837c6254412c2, 0x105a88169f1a21068811640caa5d2a600a93c2a2848adc2a004852029e808ada2a010851e29e78a71829b08939920710939c20708a61213248a70029bb09381207b89384207b0a66013380a66029848a59829600a500),
    (0x1f0208f104988254412c202c2, 0x4170c05c08690c1a40859882b7a4ad802980037892b404ac802500882062503082002b024a60024ba0ab812acc491080e79c86022aa784f9f0e784860c2aa604f99240243789),
    (0x1f0208e1049882d4412c20040, 0x4178405e0469821a6005a000da0037002c660b1002c200b0212be00a23c2bc80ae802b84caf1e2ba08ae1624b803680134483700),
    (0x1f9e8f0608e104988254412c2, 0x12cc784d1e2d6f4aba02a400b55c2d284b41e2ce8c92a32ce8cb31e2c6fcb13d2c2f4ac9f29a10b2c3230c887182c864a14526ec094aa20a70b2ed2302087002c804a16f26e1894e620a101860060486a601a8485ada),
    (0x1f1208e104988254412c202c2, 0x4188c062086a8c1aa085b082e000b7802cc0037092b400a7082540883062543083002dcc0b300133a0ab802da8090080e79892022d8784f9e0e780920c2d8604f98244243709),
    (0x1f0208e104988254413c203c2, 0x4195a065306b061ac005b802dfa4b8692ce0036a12e600b480286109c06286489c002dd84b380135a0aa002e4809120149c888022e2788b3614990880c2e2608b302448436a1),
    (0x1f0608e504988254412c2, 0x4c2a130a80c20030640c12330278c0012fef4c1223027cc0002fef0bf2d2fb20be192f66cbf2c2fb24be182f668bd2a2f270bc302eec0bf692fa30be012f60cbf682fa34be002f608bd662f210bc062ee1855e007780559207648bb002eb20ba8c2e8f05780),
    (0x1f0608e504988254412c20040, 0x1078601e0031460c50031200582100a04020116080028000800c41e30e00c300157801e18077805592078001d92),
    (0x1f1208e104988254413c212c2, 0x41eaa07a70ca8632a00ca00131a44d002dcc0c981133a0c901322209008143c84e842327883b6143904e922326083b0321a4c28030920c789303a0c70131b20bfa031998bf042f938c59e31980bf122f920c59815f2002b0),
    (0x1f0608e1049c84988254412c20040, 0x4cb0000c78c41e07b801e92) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_5 : Array (Nat × Nat) := #[ (0x1f0208e104988254413c212c2, 0x41f2a07c70238608e002280005a44b80330240009005a04b81330200008015680104002183d9e015300112002003d98135a44c0032f849121135a04c0132f8091200e9984e0414798511e0e9804e1214780511800b800030),
    (0x1f0208e1049c84988254412c20040, 0x4280016078581f07d801f12),
    (0x1f0608e10498837c60040, 0x13540cd48235008d3c035414d48035000d3bd34c10d30134a00d23c3460cd10034200d00333e08cf0133a08ce0233e00cf0433a00ce000a00c22a100e00cb0232880c4802e8f0cb0032878c4822e8f8cd8033568cc80),
    (0x1f0608e10498837c612c20040, 0x136a6cda0036600d90336268d80135e08d70836260d80435e00d70608060241808e84040032a80c5002ea30ca9e31408ba8e35a30d600356305312080001492),
    (0x1f0608e10498837c6254412c20040, 0x108060200000200bb002ec08db00057801592),
    (0x1f0608e104988254412c200800040, 0x4dc0035c187b001e604db8000018bb8631618199e040488380),
    (0x1f0608e105bca4988254412c20040, 0x137000d78000218bc06140a8be02069805412),
    (0x1f0208e504988254412c202c20040, 0x4d80009064dc803180001002f2001b0015230508c),
    (0x1f0608e1049884888254412c20040, 0x4d880004a8bd2a2fca8dd1e046a81aaa),
    (0x1f0208e1049c8254412c200c00040, 0x137a00d90037808de0309070dd802f600bd810f6001b80154185106),
    (0x1f2e2f0608e104988254412c20040, 0x137a0cd9801580000892f804be04071801292),
    (0x1f0608e104988254412c202820040, 0x136800df0001430be8c2fa381d0c04c483a00),
    (0x1f0208e1049c84888254412c20040, 0x4da802fca8bf2b004a85292087801caa),
    (0x1f0608e104988254412c208000040, 0x4e000348f0a4002be00af98000f0bfbc2fef8166c05908df9e),
    (0x1f060cf988e104988254412c20040, 0x138000d280002f0c8bc31a00c68205b801692),
    (0x1f0208e504988254412c209880040, 0x4d30030278011e31c78174e05c90c91e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_6 : Array (Nat × Nat) := #[ (0x1f0208e504988254412c208000040, 0x4e08034ef0a2802ba00ae982fef0003c31ef017ec05f08c99e),
    (0x1f9e8f0608e104988254412c20040, 0x138204d40032e00cc3d30004c202061801812),
    (0x1f0608e104988254412c209880040, 0x4d48000478c09e30a7818ce06290e11e),
    (0x1f0208e1049c8254412c209c80040, 0x4d50032078c11e12e781964064584c1e),
    (0x1f0208e10498825c412c20040, 0x4258004810e41838e00e31800660e28438860040000e00e1a136e00778c38680db811de34971e37600961014b9833800e8483180),
    (0x1f0208e104988254413c212c20040, 0x4e4800100031983880078801e204970012a184e12),
    (0x1f0208e10498837c6254413c212c2, 0x4e580015300592394603a6026a48e200),
    (0x1f0208e10498832c2254412c202c2, 0x101600e68c398009a800f6845121),
    (0x1f0608e104988254412c202c2, 0x1399a4070001600eb033aa00ea083aa08ea0609800568c3a600e90c3a230032100400388014830518001600028013ba0e80039e804f8813b98e80239e784f8601f8026000e580520c27c60e70c278300280144243189),
    (0x1f060f0208e104988254412c202c2, 0x407690c40ce6690c624ec0c01430008900000518007d8ceba1),
    (0x1f0208e10498825441ac212c20040, 0x13b40001982c40037183b200a30c2bc30af0e12e484c12),
    (0x1f9a8f0608e104988254412c2, 0x4059e1347802802dc0000bd00c8438803cef4aba03cc00b55c3ca84f23c3c68c4c233c48c059e3b2fc043d00ef4f09f3c010b2c33a06887183bf24064511ac0ef2a3ba70b2ed3a00887003be34066f11a18ef663ba1024e009248ee603b848edda),
    (0x1f0209ed28e104988254413c212c2, 0x4f480005a0003033020f401010204d683c604ec88),
    (0x1f0208e104988254413c202c2, 0x4250609400f8863e200f80001da4f7803dc0001893da00f60801a08060601a30060032f84f180135a0f5803d48091200e99888022e278511e0e980880c2e2605118327443600),
    (0x1f0208e104988254413c212c202c2, 0x4f98001c00b3003de00f1803e4049121),
    (0x1f120f0208e104988254412c202c2, 0x4fa883e80001893dfa4370933024cbb0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_7 : Array (Nat × Nat) := #[ (0x1f0208e104988254412c200c0, 0x109e1831003941899802640027800c418e5002661899063ee84fb001ea00fba03ec047a8100598278600000031e22c00020400018016009e00000600c608b06008480000014404200),
    (0x1f0208e10498825c4254412c200c0, 0x4fc8010800e5003ac189a063f060fc1907d989718005804e6000a485100),
    (0x1f0209e108e104988254412c200c2, 0x4fd00108409f8038a20eba8002205609),
    (0x1f0208e1049883fc6254412c2, 0x109a88269f4000900003fe00055d3fc00fe830f68443400fe043f023f880433d0fe103f003f878f6183c8b4a11926eb0a11c26ea8fd9212e48f6003c9a4a10126fa0a10426f98fde012f80b3602cc48b1182c400b080),
    (0x1f0209fd28e104988254413c212c2, 0x50080005a0fd812c420e1683dc04b188),
    (0x1f0208e104988254412c203c2, 0x109ca8271c40a19028040800b7e93e9a4f4000da84f6813ca00a18427018a19227000cc093f600016840601012000020055a01408049e0f678054c0143004980f66000090da84003000c009280009800100),
    (0x1f0208e104988254413c212c203c2, 0x503003e9a4fd802e1a4f10000024912100b804c00),
    (0x1f0208e106dcc13c212c2, 0x50ba142e810b0042b010a29426c10901423450a28426c5090042340faf140c01020040204ff893b424faf040c05020140200ff883b421086041f81051041201070041a00faf116dc4f9803e000f4813b704ed0916884faf016dc0f9813e004f4803b700ed0816881066041781051017c41048017b01040040e00283007f8003b0),
    (0x1f0208e106dcc254413c212c2, 0x50faf43c610e81438e50fae43c650e80438e0232a07ca90280400250281400210de04346044cc3f530e6963960099983f26099181abacf8803b93469a11aba8f8813b93069a0433806e901b9310c003a590ec643a390679639a58671619730e58019500e39839200e300083800430),
    (0x1f0208e106dcc4988254413c212c2, 0x4232a08c7028304478005100fc01110011a10e53611a48e5304438077101d98110003a79873041c930e4063a78073121c968e400),
    (0x1f0208e104b884988254412c20040, 0x14386112801e890e1a43ee791204),
    (0x1f020af548e104988254413c212c2, 0x144ac90e800fba8050d0fc091400019a09b9910f30469444f88880d21d81130220da0eec93a9887fda),
    (0x1f0208e10498825c4254412c202c2, 0x50f001104006003aa488d8c07d991498005804308012603d8013980e81222e485100),
    (0x1f0208e1065444988254412c202c2, 0x50f8201a30a10025448ef0c12f84050c4566400001318492124550c9101),
    (0x1f020c9888e104988254412c20040, 0x142a0117002c16916aa2c16d1604),
    (0x1fe30f0208e104988254413c212c2, 0x145d010b000ffc101803fa403d90019c4f220019c0f2212a7c0f5803cd80a89029dc4f04829dc0f049) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_8 : Array (Nat × Nat) := #[ (0x1f0208e1049882d44254412c202c2, 0x50b8001a30f6002b448f08c12f80050c40460000013180ab9245f089100),
    (0x1f0208f108e104988254413c212c2, 0x51880005a0010133020f900131a0e1012dcc49108385a04c012dd80912030ba0c28146124c788),
    (0x1f0208e1049c8498837c60040, 0x42c85478011d810aef42c84478051d800aef0d485474011c8534efcd484474051c8434ef82b00470102a0046e00d18046c10d08446a01189f32c00ca1e46278cb013287d1a1e46601191e),
    (0x1f0208e1049c8498837c612c20040, 0x10bc602e840c001200036a611f84366111f0632a78ca9f47a782312),
    (0x1f0208e1049c8254412c200800040, 0x42d8047c1878021e00cdd8031618c587000182586048488b00),
    (0x1f0608e104988254412c202c20040, 0x147e00000009060df0000400c60031808260015a30520c),
    (0x1f0208e104988254412c200c00040, 0x4de80480007b001ec04028400660510020e00838122c0027800c4180006),
    (0x1f0208e105bca4988254412c20040, 0x42d800c0008c862321c04aa146100612),
    (0x1f9a8f0608e104988254412c20040, 0x400000ae051c802dc0000bd31a051802093802492),
    (0x1f0208e1049c8254412c209880040, 0x51d0030a78c71e00478253609478929e),
    (0x1f0208e104988254412c208000040, 0x42b800aef09000244009118240f0913c244f8f90c),
    (0x1f020cfd88e104988254412c20040, 0x1382011d80322f000bc2dc04b70409b802692),
    (0x1f0208e104988254412c209c80040, 0x147800028438478c91e24a78276009c48011e),
    (0x1f0208e10498837860040, 0x148e0d238248c1122c048e15238048c0522bd48e11238148c0122bc4880d21804840d20834880921814840920824880121844840120804660d192133201198246480cc8146601191e3321029000a3680380),
    (0x1fe307e304988254412c2, 0x4294000f000a404a701294049c79289e4a07925da49f0107c049c79269e4987925da4a719294649c6128984a06125cc49f1907c649c6126984986125cc494a9251c492c124304a7c1297049c0128804a001259049fc107f049c012680498012590495992504492192406495812512492012400),
    (0x1f0208e10498837c637860040, 0x522034ac012a834820d22024ac052a824820922004ac112a80482002b03470012a030a60c2b02470052a020a6082b00470112a000a6011a2133600cd5a46880cd813356d1a1e33610cd5e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_9 : Array (Nat × Nat) := #[ (0x1f0208e10498837c601800040, 0x52c804b0012f804bc012e804b80d2d804b4012e024b6052d010ac012c800aa112c004227cce0017079089e338045c1f410791a8040e79259e482012b9e46e01069e),
    (0x1f0208e107fce498837c60040, 0x14d41534804d00533834d41134814d00133824cc0132854cc0532844c2102a844c80131814c80531804c4002b004c40130844be012f004ba01092133a005cda42480ce811736d305a4a801265a41278d08417b7928da4aa01285a),
    (0x1f0208e10498837c607c60040, 0x538004de0130804b00d37004c80937024c8002a034c2002b024da0136020a6082b004da0936000a60029834b00d060046c01058042608cf0017601098033c085d824a6012b004a4013580470010780),
    (0x1f0208e104988480837c60040, 0x14ec013a814ec053a800b21535004e80c2bbd0b21135014e8082bbc0a6012c804e01137844c4012c804c4002a004296ccf80175690a5a33e045d5b41568d18017d6939da4e401389e49d692200),
    (0x1f020cf98254412c208000040, 0x438180e0013e184f8013d8042a0cd2001620d240348a00ed1834e005a003b400d39816861175a38000a53c4f4f0e0802c2f02cec0e0602cc20e0013cbc4f0013b8c),
    (0x1f020cf988e10498837c60040, 0x5430350a0142005060d41025020540010b20541005021140040b2114004500053e3e4f8f13d804fe0136834d0013f004ea0932814ea01328442c84d280165693ebc47600ffbc3d2811c813b76cf49e47210edde493692300),
    (0x1f0208e10498837c609880040, 0x151615458050000383d5140141004ec0133000b00540000b2114300512082bbc0aef4383d0aa1135005100029803eaf0d48016cf10bbc34c0059bc3e6791d003e079253c48e01439e47801021e),
    (0x18e107e304988254412c2, 0x103f000a40034842f800a2000ca0530894ba252c7d4abc5287949bc52501489e5207947da530b14bac52c654ab25286149b25251948985206147cc51d09473451ac14630531a14be852c054a88528014988525c1488052001479051db1470a51a19460651d89471451a014600),
    (0x1f0208e104988378612c20040, 0x54e1b536014d03532254e1a536054d02532214e18536114d00532180a9800660290001000038002a011ea135800d58c47a80d601356351e9e35810d5900bf680400032480a80),
    (0x1fe308e107e304988254412c2, 0x10b4840d21011000fc001100294000f002d21016802d2054701489e5447947da54289501f53e794f3c437014e9e5471948985446147cc542b1501953e614f32437194e98547c14880544014790543a1500153e014f08437c14e80),
    (0x1f0208e10498837c6378612c20040, 0x40a9802060080035a30d68d35a402d12),
    (0x1f0208e105bca254400800040, 0x14386cd700180710e1a35c04601d53c714c80392611f0038c61128d370007c0644a30dc011f01d522a0ca002f1e0d201200637a009900),
    (0x1f0208e105bca254412c200800040, 0x10d200608418215499c38e007c861f21c35120c2489980),
    (0x1f0208e105bca498837c60040, 0x155c75568055805558355c7156815580155825540154855540554845501030840ac002e9c0a800e20054e11530043a84d780185090ea035e04614354aa82e0039678d984195794fda534014a5a),
    (0x1f0208e105bca498837c612c20040, 0x10bc615404186486193104a8659652aa84592),
    (0x1f0208e10498837c602c20040, 0x10c00d54000bc695900562082d880bc615902562002d865606d57803b0311f803a2310f0836000620c43c18d80218839508c536014b8c114302e80) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_10 : Array (Nat × Nat) := #[ (0x1f0208e10498837c612c202c20040, 0x554000ce0c2d893a430628c18a394c0c118484492),
    (0x1f0208e104988488837c60040, 0x1574015c81574055c800b21557005700c2bbd0b2115701570082bbc0b6c034b056e115b000ac01521c0a8002d8643f6cd88018d690fda36204635b39b68da8019d695aaa56801599e541694e00),
    (0x1f0208e104988490837c612c20040, 0x434860c00063f218fcc67f2576d94b72),
    (0x1f0208e10498837c612c201800040, 0x157a015b1854c015e005780430840b6c0e2000b6186b9e1ae7d0c1e51e790d06),
    (0x1f0208e107fce498837c612c20040, 0x55e8057c606c121b04d4eda1b859515a),
    (0x1f0208e10498837c612c207c60040, 0x55b9854e002d890ba6152000c2010c801b4006d02546010d80),
    (0x1f0208e104988480837c612c20040, 0x1580006cda1b36c6eda57e7948da),
    (0x1f020cf984988254412c208000040, 0x53e3c1a00546031a6006998296f0b13c3b2f1609e),
    (0x1f020cf988e10498837c612c20040, 0x14f80161985640d5600584015c9a552055c985521068c2400f0ee133b85946da),
    (0x1f0208e10498837c612c209880040, 0x55d1855400308455c6162000b6186aa41a490f89e51c91029e),
    (0x1f0208e1049883786254412c2, 0x1015751180592843da1015711181592803da0015691184592783d9e59175639858d7562b959171639958d7162b859169639c58d6962b603248011203e0000000bf680080035800160591d5638058dd562a1591d1638158dd162a0591c9638458dc9629e03380016003e6000000bfc80080034480112033800d60034480c920bfc82fda0a3680f9803e000a00),
    (0x1f0208e1049883786254412c20040, 0x40400006600418006000a9802a00290036c00db0136c100080035800d12),
    (0x1f0208e10498837c63786254412c2, 0x1000000c920164804000338005e0010602d600b4482900),
    (0x1f0208e10498837c6254400800040, 0x11f4607d19388606f9e1be7ce41e58a78e500),
    (0x1f0208e106dcc498837c612c20040, 0x45100596015f180ba102a004800165041c04870131c859635a),
    (0x1f0208e10498837c6254402c20040, 0x408180ba0152183a60070801c2096380) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_11 : Array (Nat × Nat) := #[ (0x1f0208e104988488837c612c20040, 0x4350459a002b000c21160000b618712a1c4ac732a59879645a),
    (0x1f0208e104988254412c201800040, 0x5658059660298059c0167011440051181ce78739f440791100),
    (0x1f0208e107fce4988254412c20040, 0x42a001d0007401592787604),
    (0x1f0208e104988254412c207c60040, 0x42a800d40035184420074801d2091180),
    (0x1f0208e1049884808254412c20040, 0x42b001d568755b1dd69679e),
    (0x1f0208e10498837c6254417c612c2, 0x55280000cc0592018603b605480044e0),
    (0x1f2e28e104988254412c202c20040, 0x554000000168000b60c3b0c1f6007d8211830448c),
    (0x1f0208e106dcc4988488812c20040, 0x1000002d981f8a87e2b26aa8471e),
    (0x1f020af548e106dcc498812c20040, 0x491005a46969185a20c7e92101a07f93101987f96),
    (0x1f0208e105bca4988254402c20040, 0x42d805a660ea061fc18408c23608438c),
    (0x1f564f2e28e104988254412c20040, 0x100a00de9b37a0d65000f3203c8c202008082123804892),
    (0x1f0208e105bca4888254412c20040, 0x10b600812a204ac3d2a5a8484912),
    (0x1f0208e105a8a4988254412c20040, 0x4018057c0084122104c049226c484f60),
    (0x1f9a8f2e28e104988254412c20040, 0x113e016b015aa05689a552009b860ee3081803ba084792),
    (0x1f0208e105bca254412c209880040, 0x555000b600831e208783c24120489c1e),
    (0x1f0208e104988254412c208800040, 0x56b005a40155805b0004f815ae009118212909ca444c91140c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_12 : Array (Nat × Nat) := #[ (0x1f020dfda8e104988254412c20040, 0x155800850c0f908870121c104992),
    (0x1f0208e104988254412c20bca0040, 0x155a011386216189d06128483ea4),
    (0x1f0208e104988254412c208880040, 0x55700248908624220916c9e),
    (0x1f0208e10498827c612c20040, 0x56f985bc0168000ca256e815a6696e845a66001980ca2552180100003803ae84df002783114a037200889345278dc82222596e6c5b6016d6c0ec483300),
    (0x1f0208e10498827c612c202c20040, 0x10c201680000660328939c30890c22439700c106483a92),
    (0x1f0208e104988254417c612c20040, 0x404000cc61520027c008980226097080),
    (0x1f0208e104bca4988254412c20040, 0x156200e79e2287842a422e104092),
    (0x1f0208e104988254412c200c20040, 0x15640001985c400e8003a0048a80110184306),
    (0x1f0208e104988254410c202c20040, 0x15ba016e8100000ea803aa048d0011034440c),
    (0x1e0208e104988254412c202c20040, 0x549985bc01718023a008e82038480b92),
    (0x1f020e0208e104988254402c20040, 0x158a6d6f98399a5720023da48f6b),
    (0x1f0208e1049882544134212c2, 0x1088a8359c5760166005660001695b20115a10002401685b20515a000020012a088a80104002184700000c0054c01440049c0f66173805cc7573815cc7171e65c99847000ce7972925a87000300ce78000614a700300009800104),
    (0x1f0208e10498848c8254412c20040, 0x40284006615a0037478dd1f14a48012a089803592),
    (0x1f0208e104988254422c212c202c2, 0x55a80016000189138004703000cc33a1),
    (0x1f0208e105aca4988254412c20040, 0x40198580008f9223e4c3f92280483d12),
    (0x1f0208e1049084888254412c20040, 0x100001668024d68935b5caa972e6) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_13 : Array (Nat × Nat) := #[ (0x1f020cb988e104988254412c20040, 0x55c002430915bc283091504),
    (0x1f020cf988e104888254412c20040, 0x10ae015c8024f08a1423bcad7312),
    (0x1f0208e104888254412c209880040, 0x15740000002549094245ce78a1aa),
    (0x1f0208e104988254412c20300, 0x4362a0d87160a4582693b800d9a036015834160804ee6916a15d000a380005a03668000c0035032600023100020012a0d8a8000800c90c99a00828003000470361c00020031a326900214000c001010d804003000c00c9d0009800008),
    (0x1f0208e104988254412c208400040, 0x53c004f200a40000a04028400660910000600911837e78c99e3268036600d848003c),
    (0x1f0208e1049883fc637c6254412c2, 0x53e80000f0f4122cc48f4602cd813d00),
    (0x1f0208e104988254412c202800040, 0x56a805aa0961005d4004f8113e11748029e30ef8c3be38fe00),
    (0x1f020ca988e104988254412c20040, 0x561802a10975922cb08b2c4),
    (0x1f9a88e104988254412c209880040, 0x54000000002b812cc78a61e3c678f41e),
    (0x1fe30f9a88e104988254412c20040, 0x490005da0976805d80140803c8f0f23e3c000f002),
    (0x1f020cf988e10254412c209880040, 0x1504002b8029cf0f63c3c278f29e),
    (0x1f0208e1049884800254412c20040, 0x576805da0490002400577805de6141802d568b55b2a369771e),
    (0x1ffb8f0208e104988254412c20040, 0x578805e06178985e00142003fb68f3003cc04f304),
    (0x1f0208e104988254412c20f980040, 0x542802a6f0f3bc3cef8ff3c),
    (0x1f0208e104988254412c201880040, 0x543002ae78ab9f3d679019e),
    (0x1f0208e104988254412c203c202c2, 0x543802cc00018913000f4000da840030) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_14 : Array (Nat × Nat) := #[ (0x1f0208e10498825441bca12c20040, 0x158800b6062aa18b886136303c12),
    (0x1f0208e104f984988254412c20040, 0x544802daf0f53c404f11784),
    (0x1f020cf988e104988254412c20040, 0x10ae002c002b0f0cc3c32e04cb84),
    (0x1f0208e104188254412c209880040, 0x15140000002b478ad1f3da78f69f),
    (0x1b0208e104988254412c209880040, 0x15160146022de78ad9e3de78fa23),
    (0x1f5648e104988254417c612c2, 0x15fcb40b2d5fa657e025fa717e00019a4471b5f6057d085f6117d06010cc2e3300ecd5280016617ce35f00d7b815ed297b845ed217ae05e98179e054a0168185e52044c8),
    (0x1f2e28e10498827c6254412c202c2, 0x40809116017f8c01261790c5a0002e09),
    (0x1f2e28e104988254412c200c2, 0x5848102e05840011405838060c0182806080181866081981801462052000082041205e4018100602798106602609990600409910),
    (0x1f2e28e104988254412c202c200c2, 0x585800140184005e4002e890e8218510),
    (0x1f2e28e1049882544250412c202c2, 0x161830458000581840c104602f21),
    (0x1f2e28e10498837c6254402c2, 0x1613749a8062a018a0262a098a0062631891b62201880e62209880c61e30460c11b8c0600606017e20606097e1e61ccd8680566cd838c61631828c54a615400),
    (0x1f2e28e10498837c6254412c202c2, 0x40d8061e315400002015db360c303009),
    (0x1f2e28e104988254410c202c2, 0x1632218c0011621878062e0d8b0662e358b000182406806180045015e8057f805e60582025fa1d820c5fa043089020240389016004501),
    (0x1f2e28e104988254412c210c202c2, 0x40e016180187805c62001015ea043089010244480),
    (0x1f2e2e0208e104988254402c2, 0x4058001c018d806342184d15fc218d826341984d35fc198d8c6340184dd5fc0005e901da42d690b40028c8612057f71612117f6f612497f69),
    (0x1f2e2e0208e104988254412c202c2, 0x401690bf200821) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_15 : Array (Nat × Nat) := #[ (0x1f2e28e106dcc4988254412c202c2, 0x5403062e418a0062009880c002c181085f4c17b025ec302c09),
    (0x1f2e28e1049882544214412c202c2, 0x162200460c63a0001195ee64448c638602c89),
    (0x1f0208e106dcc2544244412c200c0, 0x43d800a6c18f80624017c0063c718f1d119309a9c113304718),
    (0x1f7e6f2e28e104988254412c202c2, 0x163e6d9000634003cc80fc0c2a09),
    (0x1fe308e104988254412c20e1000c2, 0x1014002b406448190a0),
    (0x1f2e28e1070e24988254412c202c2, 0x58d806260184d1118003f895f2240621112002a89),
    (0x1f564f0208e104988254417c612c2, 0x57f2d0b8cc0169014303f0312a6c066964260043911a5593e364c0d92806492191e3),
    (0x1f0209ed28e104988254412c200c2, 0x58380612002e8800ca0e510),
    (0x1f2e2f0208e10498837c6254402c2, 0x40bdd1380184dd65885958c6546d948065031663360e483003),
    (0x1f0209ed28e104988254410c202c2, 0x40d8864621720903a040808010800088),
    (0x1f564f2e28e104988254412c202c2, 0x10e801969b640018503037a5940c0f320448c002cc48e0648303021),
    (0x1f2e28e104988254412c2054402c2, 0x594800ec30460c64400011864a602f09112319080),
    (0x1f2e28e1070204988254412c202c2, 0x40e516134408090048430a1),
    (0x1f0208e1049882544244412c200c0, 0x5968065400310664c01971c65c743a1c01b304e1c01530000612a600000),
    (0x1f7e6f0208e104988254412c202c2, 0x44f006340004e9),
    (0x1f0208e104988254412c20e1000c2, 0x10f4803f88) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_16 : Array (Nat × Nat) := #[ (0x1f0208e1070e24988254412c202c2, 0x43b0063601958002f44068013dc19389004840008012240500),
    (0x1fe30f9a8cf98254412c2, 0x59ca060a819c9e60a799c0066e0c65051940c14036728582a167279829e670019b82194106502050099ca160a859ca060a819c0066e00650119400140066d199ac666861999c6646198cc66d0d9ac36686999996646998c966d099ac26686d99986646d98c866dc19af066801998466401989066db59aed66809998166409988d66db19aec6680d99806640d988c66181981265e017600),
    (0x1fe30f2e29ed24988254412c2, 0x160f4183001c80465810540583d160c00720019600150060f4583d039644e59008a41a1c068419a08b68019a08a6801da1c668401a09568001a094680059ff067201830060a019c3067c419e90651a448e9651a048e8679999d84674d9689e679819d92674c16898),
    (0x1f564f2e28e10498837c6254412c2, 0x114e00448c08e6c44c808e0d83c86886d838c6880d9460650496500),
    (0x1fe30f0209ed24988254402c2, 0x16528049086114445000700012800e40184516a821a9a96a4a5a8a96a001a78669c8da68669801a5866a019a78069cb5a68069819a58054bc445000c0a0308800e21a55165001a4b0691c5a38068c11a29e68c49a298),
    (0x1fe30f0209ed24988254412c202c2, 0x407806aca445006aa419400112040408694016a71),
    (0x1fe30f5649ed24988254412c2, 0x1606987f99607447f806cf2db38e6ccd5b30a6ca29b2406c601b1356c201b10a6c265b0466bf35882d11eb5af146bb25ae1268065990d6b675ad0c6c1c5af906bd8dae8c6b985a00066521886811fa1ad846b4ddace16b249ac316b019ab9e),
    (0x1f9a8f2e28e10498837c6254412c2, 0x48c806da95b6026d60443dd6d479a35a68011a10c6d255ac0a60609b40d69b999d32620495480),
    (0x1f020af549ed24988254402c2, 0x170409a780608348d8070201c0006fe01bf006fa01ac8c622b0480e6f831bd9a6f409ad8c6f34588006f189bb866ec09ba8226409ba716e601b9026e279a70068c31b8186de19b755),
    (0x1f020af549ed24988254412c202c2, 0x4398070a69c20062001820d6ea09a70067619810726609737112385c18d),
    (0x1fe30f020af544988254412c202c2, 0x44e807174dc54d67819c480709a5a5806b21840716d46dbc8171191c3b911f8dc30d),
    (0x1f0208e105bca254400c0, 0x173805ce007360176c073405cc8673005cba773401cc8773001cba671405c2806da056b3371401c2816da016b3272c01ca8072801c99872405c8a172001c7cc72401c8a072005c7cd71c01c6f671801ab006a201200600e18fc8008a60640005160de80),
    (0x1f0208e105bca254412c200c0, 0x5c5816ea01b4015aa25c5806ea05b4005aa21960609e19ab006a601a8806aa19a20067a00de8074285d00073e11d0a074005cf8573dd9ce805b5d9a980010182398192001510112418000),
    (0x1f0208e106dcc5bca254400c0, 0x5d70175a01d60175745d70075a05d60075741ca8060001ca0026801bd806be1dbd816be19890665419d50675201d42174e01d34a75081d38174d2dbc6074a01d27674601a9000c078e5b0744006570),
    (0x1f0208e106dcc5bca254412c200c0, 0x122c01c98074a01800072801a90067c01d80476015d7f6123907210),
    (0x1f7e6f564f2e28e104988254412c2, 0x11123044c81d801bc157286dbc637280d9c3c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_17 : Array (Nat × Nat) := #[ (0x1fe30f2e28e104988254412c200c2, 0x114801caa87620180106720051a064801bb10),
    (0x1f5648e10498837c612c207c6, 0x176375db8076c01da8276c09da8076861d5036f81db0026f829b0006278195e011a5445986ce01d9a06ce09d99e6ec85d2a12648583c87652182c854a01aa00),
    (0x1f564f0208e10498837c612c207c6, 0x49b0076375d2a172c25aa0067e0044920186099a160f80488c),
    (0x1fe30f9a88e10498837c6254412c2, 0x4ac0073771cdda65e01dcde77079dcdb77081b95c6c27db95a6c289b18c6c639ad076b429b1c86c729ad316b4d14080),
    (0x1f020cf98af544988254412c202c2, 0x113201ce4e7392198006fc01bf066b601ad86711b1ddb171189ddb711f9ddd0311f85dd0d),
    (0x1f020cf988e106dcc254412c200c0, 0x49c8075601cb8066205df006be01de84101b89bb477815c46011f907f90),
    (0x1fdecf2e28e104988254412c2, 0x179321810879001e3801ea01e34977001e28978821e1b5710d5bf1f6c629e1c37110dbf196c651e16160421e08178005df81629a449e970005b0d069799a78468139a102664c9a5e069e49a04868431993c),
    (0x1fbeaf564f2e28e104988254412c2, 0x5b60c79a6087007862ddf257984de59976a55d61b6b841e56d7300d99c2),
    (0x1fe30f5648e104988254412c200c2, 0x124801cd5275d319a067a001ae866d4683bca70ee1e78011f89e70c),
    (0x1f0208e106dcc498812c207c6, 0x17a801e28070479af0270295b10262a704a1c713d5b4806fe35b2026a1c9a61068601a08266a09b52b78601dc807a681e96d270c044da7a208999e75a78991e10f204000),
    (0x1f0208e106dcc498837c612c207c6, 0x17a175e18027401db0475a79b018732019b02604509c186ce11bb1e60780478c),
    (0x1f0608e104988254412c2, 0x492a113480b7022450092a313478b700244f44ca21327cac3c240f04e2d14920519822c6c4eac0e6648cb213ec84eaa0e6708cb013ec04e6914830518022c0c4ee80e6048c8813e204ee60e6108c8613e1807e00e58007920e4485380055801512051680280),
    (0x1f564f2e2f0608e104988254412c2, 0x114920520c1d801db952686c45ad6ec6ddbe32680c45e96ec0d9bda),
    (0x1f9a8f564f2e28e104988254412c2, 0x5b50032ec1b51832e19b51e32e01e5357ab3de50b7aa95e5437ab25e5157aa6d9d10795b5ea8d7958dea83675319d5a),
    (0x1f0208e105bca498837c6254402c2, 0x4498013001eb827ac79eb8c7ac619d88606103006606483000),
    (0x1f9a8f5648e104988254412c202c2, 0x113401eccf7b3259e087b019ec0069a09a68c0ef39b5180ef21b51e11f99e78211f81e78c) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_18 : Array (Nat × Nat) := #[ (0x1f564f0208e10498837c6254402c2, 0x40bdd07c01ed2165260416901061a5481178c301b),
    (0x1f0208e10498837c6254400c0, 0x17c201f0007b21deb007aa1d69337b219eb017aa19693265a1995006ec1965b66141831067be85ef007bb21efa07bc05eec97b418041808ed8718005591ee1c7b60005e065800de86268180418480000380),
    (0x1f0208e10498837c6254412c200c0, 0x5ed066880196006141920007c401f10114e11709c146480400),
    (0x1f0208e106dcc498837c6254400c0, 0x110801f0007c80196866240153307c721f1c96438065e4117803018),
    (0x1f0208e107fce498837c6254412c2, 0x101569f2847c0799092643802a00),
    (0x1f2e28e104988254412c207c6, 0x17d455f4807ca01f21b7d065b4827d071b480641a44f697ae05e51a7ae11e51865649bc18002243f800e201f28001601b6007ce81b6027ce78448c10460040957c2403897cc600580),
    (0x1f2e2f0208e104988254412c207c6, 0x5f4957c26d906957c2405480fc0c0100010843ce0),
    (0x1f2e28e10498837c6254412c207c6, 0x17d775f2807d401899254e00008039485830c0c0244580),
    (0x1f0208e106dcc498837c6254402c2, 0x11104049807d009889c554c190e039401f664117803018),
    (0x1f0208e107fce4988254412c2, 0x110d05f7007da04fe2110d01f7017da00fe2012679b5231267db5227ca103f8412661b52d12665b52c7ca483f9212601b56912605b5687cb803fe0),
    (0x1fe30f0208e104988254412c200c2, 0x10ad01f580108403f100f2003c81),
    (0x1f020af548e104988254412c200c0, 0x1556c9b6807aa19f7b2013a00006330c8000079a048cb401988cb92),
    (0x1f020dfda8e10498837c6254412c2, 0x17e56843337da00fb807e249f81868035a010628495600),
    (0x1f0208e105bca4988254412c207c6, 0x5a0827b1a5e51862a1156865b30c43320f8184b806d810e51e0ef800606),
    (0x1f020af548e104988254412c200c2, 0x5573268c1804e810c183e32000003b8101989f992),
    (0x1f0208e10498837c627c6254402c2, 0x4018910648450c54a61fa33017815218) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_19 : Array (Nat × Nat) := #[ (0x1f0209ed24988254402c200c2, 0x160e05858060a01fd017f201fc007ee19fc067ee017a007ec01798004a0013000e401bb807ea19bb867ea0030880ba200388),
    (0x1f0209ed28e104988254402c200c2, 0x583807f60184800ba21918807c200420),
    (0x1f0208e1049883504254402c2, 0x102f7427a17fe01ff087fe09ff067fa61a38c7f8cdb98e7f8d5b98c00625578004e301f000e431663361a0159b311ccc06007f631fc8c7e8cd5780),
    (0x1f0208e105bca2544134212c2, 0x6029280801e90080685e90180680062a088a844901047201006e87601016e8718ce65c99a0096690715806010180386800700584),
    (0x1f0208e10498837c63504254402c2, 0x163048308004a3187337f449581b),
    (0x1f0208e106dcc498817c612c2, 0x182cde0a8082879a28282695b88262c70409c71001b52b8240608887a5b49c301136a08042667a079e2647a070081b76060d81772056681202047280e41f65a6e009b74080d8043c8),
    (0x1f0208e105bca498827c6254402c2, 0x5ff8c126020c027ac7a0b8c6de217e187ee09588680c496998),
    (0x1f0208e10498837c6254400c2, 0x61080840020f8068c1e0f8168c1a0f006e4198b8611018402180c00402080c060e808387a0d9c8340005e0832180418564000380),
    (0x1f0208e10498837c6254402c200c2, 0x581808480203017f03159008460211026ee303080),
    (0x1f5648e1070204988254412c202c2, 0x42f3384c86125169c9c3c511268440091214612a7),
    (0x1f564f2e28e104988254412c2, 0x111320448c14660518000801c4336d409c4096d469c4356d401c40b6d46045ad018b5bc1511321bb1b2666c991b11e65bc9411e71bc926f18c448c6ec0c99832640c45e9019a447816f34047846f33848e012249a54869431a4bc),
    (0x1f0208e10498837c6214402c2, 0x6140084e020f9881030478e622660f1b8263201087f82047cb622020f81811260f028272601337f8cc45491143030990c2000380),
    (0x1f0208e10498837c6214412c202c2, 0x614996220046120c20173b3112480400),
    (0x1f564f0208e104988214412c202c2, 0x42f338566614cb80e3040cb1266c479910f2e1501),
    (0x1f0208e10498837c6054402c2, 0x618dd86176178085c8616808580a168285800488c652620f98828220f9a8281a008c7fa0048c8652020f80828ca0f82828c200c87fa6045481143030980c2000380),
    (0x1f0208e10498837c612c2054402c2, 0x619186520046120c2017298112480400) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_20 : Array (Nat × Nat) := #[ (0x1f564f0208e104988250412c202c2, 0x10bcce19838658c488c02e300198123803c92),
    (0x1f0208e106dcc498812c2054400c0, 0x61b006f60029b0812021ab0868c04a48121208d9a10f209c30),
    (0x1f0208e107fce4988254402c2, 0x187b061e21876021d0085819a58284e19bf08872084a0285801a58c84e01bf0e872304a0c6d5a58a00840020aa0871a61b80),
    (0x1f0208e107fce498837c6254402c2, 0x61c8286c79eb8c87da42a00),
    (0x1f0208e10498831c6254402c2, 0x102f7427a11260a1c808800e1f8685a01a60c85639f40085009bf8c1103440807106d8a8084c220b808420a0b197fe003c00),
    (0x1f0208e10498837c631c6254402c2, 0x620dc87201be066084c480081465e93310e002a81),
    (0x1fe30f02086104988254412c200c2, 0x42b408820049a884a8a150a),
    (0x1f0208e104988250412c200c0, 0x185c0219807b401a9806a201960026618990688b8e22008878222e28880621e185c00019807d801b800e5904e6022c18021202e422100),
    (0x1f0208e106dcc4988250412c200c0, 0x10a6c2210088e01a9006ec1a236088d84496004b9051aa),
    (0x1f7e6f0208e10498837c6254402c2, 0x40bdd88e85958c85e004169808cc2a03),
    (0x1f0208e10498837c6254407c602c2, 0x16a80027a11143049006f06202980aa0044e0),
    (0x1f0208c104988254412c200c2, 0x618806100184801120626008481a2606848000b70896022568892016d6087a0a246e87a32246809e422110),
    (0x1fe30f0208c104988254412c200c2, 0x42b4088442180089ba1d7e0),
    (0x1f020cf988e10498837c6254402c2, 0x1504f2200387401bf066fc220f1b70031ad866b6220e80822f205e7817a82c00),
    (0x1f0208e106dcc4988214412c202c2, 0x10b2c213806f402060c12926283112126279b10f262701),
    (0x1f9a8f0208e10498837c6254402c2, 0x1572f6295b8a202125d6960a0f9a69e31a68c6b22043826d585bcc881bac2c01) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_21 : Array (Nat × Nat) := #[ (0x1f0208e106dcc498812c2054402c2, 0x185801be820b2c20700129222a3012122299a10f21c400),
    (0x1f0208e106dcc4988250412c202c2, 0x42cb089841a70211e321e8809e0049608ab903b92),
    (0x1f0209ed24988254412c202c200c2, 0x5858060c022b015ea0007806aa400408),
    (0x1f0208e1049883504254412c202c2, 0x4078c8afa58680018000189630495780576cc00808ac483383),
    (0x1f0208e105bca49882544134212c2, 0x18b0718700004a8062a0161171e66339958060107851e6),
    (0x1f0208e106dcc4988254417c612c2, 0x62e2d5f8018b1c562c16ced014403f0012e622d84394d84692018c22d608b201c1cc847816980),
    (0x1f0208e10498837c6254412c200c2, 0x61201606021200606058b86564022e9c604480400),
    (0x1f0208e105bca498837c6254412c2, 0x4055a015303f0000c01908439479909239461a510116103006116483000),
    (0x1f0208e10498837c6254410c202c2, 0x10360211806084c3080036061181608483081002004380),
    (0x1e0208e10498837c6254402c2, 0x631806340231008c20a31028c20219188c1d614997083a149c7083186120384a2fe98bc014a48848062e71848122e6f8b1a62be9),
    (0x1e0208e10498837c6254412c202c2, 0x44580618494a980d7a58412),
    (0x1f564e0208e104988254412c202c2, 0x42f336340232038658c3d6902e4963481258e26f5),
    (0x1f0208e104988254412c2054400c0, 0x5c2807ac0031068b20233188ca60399a01b204c1801520000612e600000),
    (0x1f0208e107fce4988254412c202c2, 0x630806280175e9),
    (0x1f0208e10498831c6254412c202c2, 0x18c4018a8084c21eb800f000068013da22d015b2cc0008012040500),
    (0x1f0208e1086104988254412c200c2, 0x10f0884d8a) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_22 : Array (Nat × Nat) := #[ (0x1f0208e1049882544250412c200c0, 0x16ac02320665800e5008cf8233e101f904e60006600318),
    (0x1f0208e104988254412c207c602c2, 0x1006243d00642000548),
    (0x1f0208e108c104988254412c200c2, 0x16120170a0),
    (0x1fe30f0e28e104988254412c2, 0x405a00ea0000c0012843880644843d217cc2405a058104044000f0237c08dc1a36a370efa12a279e1e37c68dc0236ad70ee212ac79e0636700ea0235908d4423490019c4468889ba192018d01206ee8d04a06e8),
    (0x1fe30f0208ed24988254412c202c2, 0x401000bd0238108c00048800ea043508648000670),
    (0x1f2e2f0208e104988254417c612c2, 0x639158e26c0169015203f03642000409644016009),
    (0x1f9a8f0208e104988254417c612c2, 0x1570f5a2820fbd5f9027da051407019bdb51e10f6dc3a38e60a376079f21c34c),
    (0x1f524f0208e104988254412c202c2, 0x44f000062631e90fc0c3cc8),
    (0x1fe30f0208e104988254410c202c2, 0x159b000b08006240df1122000b09006204881037c000c0),
    (0x1f020af548e104988254410c202c2, 0x1574c8440d1260847808d0304f010c4080de88e83400b2),
    (0x1f0208e1049882544124200c0, 0x13941985002640219801080238808e00234868ee2e3b008ea123b8a8ec063a8501d9a32003ac00018686600018607c1055000e44042000061801040f6003880),
    (0x1f0208e104988254412c2124200c0, 0x632006140219806aa00998009e0235068f0123c0501c103a0401e400510000180000),
    (0x1f0208e106dcc49882544124200c0, 0x55b3010801f0006ec0235868f2123c8513c100de60704000b0),
    (0x1f020e5248e104988254402c2, 0x100624076984c85ec028a52e3e0884c8dec008a5363e0602f740b0085665c48e85671c48c643a590008f78e3d007d6323963),
    (0x1f020e5248e104988254412c202c2, 0x4070064001649b),
    (0x1f564f020e5248e104988254402c2, 0x10c40c0de956f8d845d7d631f2e36f18e3669) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_23 : Array (Nat × Nat) := #[ (0x1f0208e1086104988254412c200c0, 0x5ec807141a3fa28fc8a3ea0134884ea8),
    (0x1fdecf0208e104988254412c202c2, 0x19040240818c3a5a78269e32406910c21f6810f601b5001279e3704127863712),
    (0x1f0208e104988254412c2054400c2, 0x60f801101a398001b2241980152043060fa600000),
    (0x1f0208e1071644988254412c202c2, 0x631698a52c31036a031c4330fb44050c9000c00001298e37b9),
    (0x1f0208e1049882544120200c0, 0x6388690e0234808e20243868d21a431190a02421090c4242819084621062560221002561805100f6003880),
    (0x1f0208e104988254412c2120200c0, 0x18841980008840180068d402350691042441102e58521002e405216),
    (0x1f0e08e104988254412c2, 0x192c864aa09280177c09268e494e9221a48258fe8a329f7def16c3c926b6494892202481b8feb232997dec96c3265ca9971c91ec1673091da6468878e024601917a245019122175088cf9a21e68f0123a847c419eece73e11c7cc1ec1a33e0887823c128ea49f1007bb21cf9271f687b00),
    (0x1f0e08e104988254412c200c0, 0x622068ec01ef0674001c800888023b067bc01d00672018fba10f6003880932824c0092e0233e68881a21e61ec00fc1e2600097821ec1a33e08880221e01ec18fc1826018978c1ec02441090a024210),
    (0x1f0208e104988254417c212c2, 0x188ab23b997be09d0807220222aa8ee71ef8074209c882005a64f0093a240009015704b81330203da0015684b84330183d9e10ccc011200200fe1892ba64e009378177a18cda23f0179b896ba08cd9a3f0479b816b9e93582471278f8174983ed803dc8),
    (0x1f0208ed08e104988254412c200c0, 0x172401c9069328222ec2628222e22629a4310),
    (0x1f0209ed28e104988254412c200c0, 0x561086d001b4069122042a878e048c8a232504390),
    (0x1f0208e104988254412c202c200c0, 0x16ea01ba8609e1a4f8009e024f869340245000e608398c110404308),
    (0x1f0208e108c104988254412c200c0, 0x5c5807161a45e891da22ea013ba84ef4),
    (0x1f0208e106dcc4988254412c200c0, 0x10a6c042007c001bb006ec1a47b091ec43fe001998519c0198051aa),
    (0x1fe30f0208e104988254412c200c0, 0x150702508094001cd807361a4ec0936024d812b100ac46),
    (0x1f0208e104988254412c20e1000c0, 0x5ce007381a4aa0938804ca01329a4f20) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_24 : Array (Nat × Nat) := #[ (0x1f0208e106dcc49882544120200c0, 0x14b2c1f0008d60235869444251117d64000b0),
    (0x1f0208e106dcc49c8254412c200c0, 0x5c9802560252806ec01d1069486a521b26d80066604b925190),
    (0x1f0208e104988254412c207c6, 0x113cb5909812865c40212871c40013da5908012805c41a12811c4180fc0df28001571f900900803da001569f902900783d9e000cc050c012600118000240548012000100),
    (0x1f0208e106d0c4988254412c200c0, 0x109e1827804b0c1f00074a01d28694d825361002c09b6026d99f590),
    (0x1f0208e10498837c6254412c207c6, 0x17d775f2806f001bc180aa003da1112480618113800600),
    (0x1f1a08e10498837c6254412c2, 0x6595d96209e41e9600657dc95c06568295882445a9456a425a94c12559e9541254843ec7a541a94eaa1a1977aaa3caa88c71d82a7c669d30863c4997129500a53e686805dee68f39a230476199f18274cc98f6065d818f6063c495e18578012d00),
    (0x1f0e08e106dcc4988254412c200c0, 0x52db090a025a0074e01d386002c259b094d8223669486a2360948925110),
    (0x1f020cf988e104988254417c212c2, 0x52e3c90c6e5c0075001d4027e56805030fc325b8010f709b9f10f689ba296db25903791825a8c86bb9de4986bb1de4c),
    (0x1f0208e107fce4988254400c0, 0x186c19df0186c1ddf0097801f08086c01df0786c05df0697819f08663e198f8057ad95eb04bac25c219680254e0970825a01953865df0974025cf088e1a528088e025286),
    (0x1f0208e107fce4988254412c200c0, 0x14bec223867280223807281a5580956065ef01d8107612),
    (0x1f0208e107fce6dcc4988254400c0, 0x110801f20063e01f20663e192f3095582556197d81f2e0),
    (0x1f0208e104988254412c20c0000c0, 0x5d58075619d5d07575a5600272009c8696a02565096b409cd02735a5b88),
    (0x1f020efdc8e104988254412c200c0, 0x5d6007581a56c8901a1e40112798871c12780872a),
    (0x1f0208e104988254412c20dcc00c0, 0x5d68075a18420097e025b3095cc04a66274c04a60274d9f948),
    (0x1f0208e1082104988254412c200c0, 0x5d70075c1a57a8964a26010248a0922e),
    (0x1f7e68e104988254412c207c6, 0x661007d2021c997860a1c9c7860261187d2621c817866a1c84786603f030fe0038807920260a07920a609e) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_25 : Array (Nat × Nat) := #[ (0x1f7e6f0208e104988254412c207c6, 0x17d255f4e3),
    (0x1f0208e104988254412c202c0, 0x663805e0261e0890201f80878001df808781a40827e019e00277e0a1e0090231f80078031df8c98c866280988000168878203d803ee8246001ea0400080059a1e060f608fb9e918087a84000180160878003d8c3ee62460c1ea48000010c266189),
    (0x1f020efdc8e104988254412c202c0, 0x6618999201e08078209e08c99121f760127a1e40112799e40412781e412),
    (0x1ffdef0208e104988254412c2, 0x19a40268809a00267a199c0266a19988665a199405f70187481dc2199411f70487479dc2399449f71287461dc2d99581f76087401dc69),
    (0x1ffdef0208e107fce4988254412c2, 0x19aa026a2110d0265019928269849a64a69e0),
    (0x1f0208e104988254412c20fce, 0x19b08178c09048df89e8767de300904b5f89887665e306905a5f88087605e3307da06650010d026b809ac80fe20000f5f90290078011e000cdf90c90060011800025f948900000100),
    (0x1f0208e107fce4988254412c20fce, 0x19b306650078401e106784c0fe2179210499e792484998793804980),
    (0x1f0208e104988254412c20042, 0x187a0d810087a09810187a0181049b8020e8010a866d8010a826d8110a7a6d840058267809b46000003f84a6180),
    (0x1ffb8f0208e104988254412c20042, 0x19b20261807da4a6e809ba066e84),
    (0x1ffb8f0208e10498837c6254412c2, 0x66bda9be0267009bc02105d78802105c78806105a788120e9877049b08c6c235b09083a01dc606c321b0c96c3314200),
    (0x1f020efdc8e104988254412c202c2, 0x66c0098fa66e0987401c00070009c00c7dd8267809c320fe00127a270011279a7004127827012),
    (0x1f7e6f2e28e104988254412c207c6, 0x5f515984025e1b9c46000890fc0c2a09),
    (0x1f7e68e10498837c6254412c207c6, 0x17d775f5007d461308000201f021),
    (0x1fef2f0208e104988254412c200c2, 0x14c501f58000301f010),
    (0x1f020bfd68e107fce4988254412c2, 0x110d00433d7da00cc009a60672209a612721e9c60d3180),
    (0x1f0208e107fce4988254412c207c6, 0x176a01da984c802605d79211f01e126604980) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_26 : Array (Nat × Nat) := #[ (0x1ff74f0208e104988254412c200c2, 0x673809cc0272860f9c043067da1000008dc023701127926e92),
    (0x1f9a8f7e68e10498837c6254412c2, 0x191e02749f7920a740110f7672da9c609b4956b821b4e36b8c93280),
    (0x1f0208e107fce6dcc4988254402c2, 0x111041f4027d03133307cb81f000),
    (0x1f0208e106dcc4988254412c202c0, 0x14cec274809cc42720079609e58c9d4c247b10ff800008330c03d8001999e68401981e692),
    (0x1ffdef0208e10498837c6254412c2, 0x19d80275a17e569f8927e3813400),
    (0x1f0208e10498837c6254412c20fce, 0x673dd9a601e606798c134800f684433c0f8003f806d84806186d9800600),
    (0x1f020cf988e104988254412c20042, 0x14d4f03e3c7e605f984),
    (0x1f0208e104988254417c612c207c6, 0x113da5f2807cc6000090eb803d00),
    (0x1f0208e104988254412c20ed200c2, 0x10ea0593887c2400120),
    (0x1f0208e10498825441fce12c2, 0x18f88df38687e7de9808f8b5f38087e65e986005a5f7007da04000910d0279819e420fe20000f43e840f818011e000cc3e920f80001189e20278609de0677609db81f948),
    (0x1f0208e104fce4988254412c207c6, 0x198278055a9da125f9e),
    (0x1f0208e104988254412c201c6, 0x18a405b6188a401b61988061dc808a465b6008a461b60188001dc989008676809008276810156a6f809e8783d9e0f730430610a6005180f640433010a000500),
    (0x1f0208e104988254412c207c601c6, 0x5e8807a261e4809ed7276819ea003da0),
    (0x1f020b6308e104988254412c200c2, 0x67b001084237c09004237c1),
    (0x1f020cf988e104988254412c207c6, 0x67b809437542bc8426de2806c401b1028420de2986c461b11a7e56a6f809e4f25b8010f72770110f6a7704),
    (0x1f0208e1061cc4988254412c202c2, 0x111042778070209c08c7e52443089f2043d801299e7c31129867c37) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_27 : Array (Nat × Nat) := #[ (0x1f9a8f0208e104988254412c207c6, 0x1586f5af026bc6842dd7e409f6810f679b51e10f6e7804),
    (0x1f0208e104988254412c20dcc02c2, 0x170401c1061104278801299a7d30129827d367e52043087dc003d80),
    (0x1f0208e106d0c4988254412c202c2, 0x1126003e30),
    (0x1f0209ed24988254412c20ed200c2, 0x5d9009f60045005f2209b0872c440620),
    (0x1f0208e106dcc498825441fce12c2, 0x67e2998201d9807661936300f74405100fc003fb08b61006368b64806309eb825f80),
    (0x1f0208e10498837c6254412c201c6, 0x19ed75e4809ed71e4816ce01b3816ce61b3994da025b84604484398605804380),
    (0x1f0208e10498831c6254412c207c6, 0x5f5dd9ea01db0076c044a1976c61db191280537007d7727a810f6843da000201f900128604a00),
    (0x1f020ec308e104988254400c2, 0x620817a01a7b009f81a20807a01e20877a0027b069f80220867a00639719fa027ff09fc025ce08e5c27e81),
    (0x1fe30f020ec308e104988254400c2, 0x11084137f07cbc2367097dc23671),
    (0x1f020ec308e104988254412c200c2, 0x102e05387002e01d880762065ee0),
    (0x1f0208e104988254413c612c2, 0x1890b58080890b18081a0a720e00005a43e800f8240009005a03e810f82000080156a8204a06183d9e0f730011200200051890601f9e190605f9e0a041280e0a018171189b7804330),
    (0x1f0208e10498825c6254412c200c2, 0x1108404380a0e1a8318a0c6401609b6497100),
    (0x1f0208e104988254412c200c20042, 0x60c80a1202848187a026d84a100284019cc180006),
    (0x1f0208e1049882544250412c200c2, 0x6850610e021e86006604298),
    (0x1f0e28e104988254412c200c2, 0x40b811120225805e406870080c1a870680c0004a1014003880a1a828600a16028480a0c7a8486a0c62351090e423490),
    (0x1f0208ed28e104988254412c200c2, 0x1a1a823890) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_28 : Array (Nat × Nat) := #[ (0x1f0208e1049882544124200c2, 0x62601a22022600a2204438662e028800a1e00408ba1c00408aa1c040766a140283800061a6e06a0a104210006180104014003880),
    (0x1f0208e104988254412c2124200c2, 0x6260160802260060806850062e000b81a24000b80a24040704a00103d90000184300),
    (0x1f0208e106dcc4988254412c200c2, 0x54330a200210006e401b9060ff826780a06c03d800199a8084019828092),
    (0x1f0208e1049882544244412c200c2, 0x60f001101a8a0001b32811c015304306a26600000),
    (0x1fe30f0208e104988254413c612c2, 0x53a400ffc1f9007da103d90019c5c3a0019c1c3a1a2a026ee079d21e749),
    (0x1fe30f0e28e104988254412c200c2, 0x405000ad027e8090e4000c0a2c023590),
    (0x1fe30f0208e10498837c6254400c2, 0x53ac09ec1a8c00a2e0272866ba19ae876d59206e881ba42c04),
    (0x1fe30f0208e1049882544124200c2, 0x53b407d60042101264234048d01400c0),
    (0x1f0208e104988254412c2014400c2, 0x68b801101a8a80110c28a9810cc043067e4000000),
    (0x1f0208e104988254412c20780, 0x628c48a265b5be6d661b2808a30a289c6d6f1b59a6ca0a28ee8a205b5d66d601b2988a3b228846d751b5826ca6a8da1a34028c80015728c5c0f678fbbe960007a9f0f680055aa31683da03eef258021ea883d9e0146e8c1b0f630fb98960f07a920f7200503a300c3dc83ee0258541eb803d8c),
    (0x1f0208e10498837c6254412c20780, 0x68c5c9d0028c5a9d009b3006cc09b3186cc693f00a3802478191e11f90310e6de39210e0de3e0),
    (0x1fe30f0208e104988254412c201c6, 0x14ff01f6849e0027801),
    (0x1f564f0e28e104988254412c2, 0x444c8a1218519822e0002009f4ce370071025b51a9f0d67000a428dddb063ab43c2da40b444c8a3e6c999b2646e299970c4a279c7744a890c93e0c066911a028f685ec068e84817822ae08e849f66070649b75a),
    (0x1f020af548ed24988254412c202c2, 0x4398070a6a888d11e01b78c5ec02848793e0806688ab86910d),
    (0x1f0208e105bca4988254417c612c2, 0x5b8020156843320f8180300a4610e51e63a116206),
    (0x1f0208e1049883fce254412c2, 0x1a4e8d7d00a4c7e088001575f7007da043da110d0292819c208fe20000f43f840fc00011e8a861c3ad8a065ddaca48483e928a801c3e98a005dde8a49803ee0) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_29 : Array (Nat × Nat) := #[ (0x1f0208e106fce4988254412c202c2, 0x10062449805f4c03fe0),
    (0x1f0208e1049883fce37c6254412c2, 0x110cf29192a47814400),
    (0x1f0208e104988254412c202c20042, 0x16ee01bb82604021e82a12061e80a12128000902483d8c),
    (0x1f020cf988e104988254417c612c2, 0x544bca1e6e0a806e201b8827e56a94039c2325b8010f71dd9f10f69dda2a280e706077525dd4c),
    (0x1f020cf988e10498837c6254412c2, 0x10b0f1f95a7e40df68096e0043dc6d47c43da6d488439b6d449bc8d6f24043836d581bcc96f3302c00),
    (0x1f0208e106dcc4988254410c202c2, 0x1514c26e09a4c028e82a3a326e08a4c068e83a3a3400b0),
    (0x1e0208e106dcc4988254412c202c2, 0x1516c285108c201c2027083146c887a4293e9a3dae8f75),
    (0x1f0208e1072e24988254412c202c2, 0x40580a52000bd1004843521),
    (0x1f0e28e104988254412c202c2, 0x694e901c0005801060296081060191885ea017980a5a0a1186a5a3211800128401000e20005800ea0296080ea0286a0a56028580a240a951ea243295180d4243309),
    (0x1f0e2f0208e104988254412c202c2, 0x101da40680a53a433095e800000800224050002dc286a1),
    (0x1f0208e10498833c6254402c2, 0x102f7427a1128004982a680a2806a6602038ca64397b80a620a060c01a3006000ef8d8e808e6069820a280a979ea5ccdff800ed843519),
    (0x1f0208e10498833c6254412c202c2, 0x69a8063a016cb3),
    (0x1f164f0208e104988254412c202c2, 0x69b000c40e9ae98103042d1014303e09000003b981038e9839),
    (0x1f0208e104988254417c602c2, 0x1a7a019280a78020702a780a070001da63180a76000189a74022a08a740a2a0601a3006000f38191008e6029ca08e60a9c9e0ed803518a70ce9b80),
    (0x1f0208e104988254417c612c202c2, 0x101c02318064401679b),
    (0x1f0208e1049882dcc254412c200c0, 0x6078010802a000a3e1a9fb0a7cc040e62e2c03ee00f1808baa) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_30 : Array (Nat × Nat) := #[ (0x1f0208e105fce4988254417c612c2, 0x10156a9204a807aa0e6),
    (0x1f0208e104988254412c203c6, 0x1a8ab62d80a88b17d80a86720900a6da69180a74063680a681290800f8269200005a1f9009008000080156a9402a84783d9e0f730050c01260051800024433010a000100),
    (0x1f0208e10498833c6254412c203c6, 0x6a35da48020800a40003da1a13843c00),
    (0x1f020be308e104988254412c200c2, 0x6a3001084298400f842a3a1),
    (0x1f7e6f0208e104988254417c612c2, 0x63915005a5f28064f8e9d80),
    (0x1f0208e10498835c6254402c2, 0x102f7427a1128004982a860a9300a66623a0ca7866340ca62728e8ca1c4c440d1006d8b00a9622a500a1e0aa499088000600a90316e80),
    (0x1f0208e10498835c6254412c202c2, 0x1a98018b00a96217e80018000680a5a496e8002da2951912acc0008002000500a24483501),
    (0x1f0208e1075644988254412c202c2, 0x6a669a8a0031038aa3040331372c050c0f80c00000f18ea3ad),
    (0x1f020e5648e104988254402c2, 0x1006240769a96862e02a88029382a968e2e00a880a9380a58b56f69897740bdda64668f0ea64728f0c1058d7f0013c023d00a7b8ea68c),
    (0x1f020e5648e104988254412c202c2, 0x407005bf8d7f0013c00068ca7b8e268c0ff8c050c5926c00000f58ea712),
    (0x1f0208e1065cc4988254412c202c2, 0x11104228008260a278c0fb844308aa0643d801039e97b10f186a792),
    (0x1f0208e1049882dcc254412c202c2, 0x18280044108a802298c1039a9cb00fb804308900603d800f182a892),
    (0x1f0208e106d4c4988254412c202c2, 0x4068c12602128c0ff80050c0f8c000000f582a392),
    (0x1f0208ed24988254412c202c200c2, 0x445005e4000b80a560001008e0403508),
    (0x1f0208e104dcc4988254417c612c2, 0x44000aa470055a014403e0612e62a0848b2d84036a839a2c80a4532a960),
    (0x1f0208e10498827c6254412c200c2, 0x5fb8010e02a986a54604ab2a12483500) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_31 : Array (Nat × Nat) := #[ (0x1f0e28e104988254410c202c2, 0x694e90380591885fe057980aa60ea906aa636a90001a004600aaa02aa00a220aa507a2232a5010cc243b00),
    (0x1f0e28e104988254412c210c202c2, 0x1038044600aaa017f8101c017a800040695810d4243a80),
    (0x1f0208ed28e104988254410c202c2, 0x40189018217a0101da294e80cc2004a0),
    (0x1f0208e10498827c6254410c202c2, 0x401890180288935fa06a601aa40687125ba040498),
    (0x1e0208e10498827c6254412c202c2, 0x1022240d80aaa4aab18896496f00),
    (0x1e564e0208e104988254412c202c2, 0x56fe3038498d005fc02307502e4a3d69aaf8ea6f5),
    (0x1f0208e10498827c6214412c202c2, 0x11200041925ee6406c90ea483500),
    (0x1f0208e10498827c612c2054402c2, 0x112400419264a6006c80ea483500),
    (0x1f0208e104988254421c612c202c2, 0x18300031100f0017d99a8ba2a099015240008136040500),
    (0x1f0208e10498825441242120200c0, 0x160002210090e1aac808e002ac10ab0441310014400104),
    (0x1f0208e10498825c6254412c202c2, 0x5fa800c4400600ab4498098891a28319005800008012600500a10497100),
    (0x1f0e28e104988254412c202c200c2, 0x17ec000500112022580a18000100a5602ac90),
    (0x1f0208e104988254412c2024200c2, 0x17f001fc02a24000b80a1006890202e0a8404000200006004004300),
    (0x1f0208c104988254412c202c200c2, 0x44500610003a81a582170008664001a0),
    (0x1f0208e1049882544124202c200c2, 0x1a90018200898028701a1402a9800140296820380aad040c4400100),
    (0x1f0208e104988254410c202c200c2, 0x44500114040500106004181006240188) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_32 : Array (Nat × Nat) := #[ (0x1e0208e104988254412c202c200c2, 0x6ae00862022581ab6023210),
    (0x1f020e0208e104988254402c200c2, 0x161206af01a53a6ae80),
    (0x1f0208c104988254410c202c2, 0x6b0f0aaa02b008abe054b8089816a58e8984ea588036258600a53a04181a140aa607a1432a601022200701),
    (0x1f0208c104988254412c210c202c2, 0x1ac3c18600118069608530003b01006800b80),
    (0x1f0208e108c104988254410c202c2, 0x158e2294e8022200168),
    (0x1f0208e1049882544250410c202c2, 0x6260d10202260c102040160),
    (0x1f020d0208e10498812c2054402c2, 0x6b080863754b0c036b40b18),
    (0x1d0208e104988254412c2054402c2, 0x61900590329e8003982319802f804f2d),
    (0x1f0208e1086104988254410c202c2, 0x1120203c08039480bd2006200122),
    (0x1f0208e10498825441282054402c2, 0x1124003d0003920011802f200180),
    (0x1f0208e1049882544244410c202c2, 0x6989c11036b102a6274440cac40c011c),
    (0x1f0208e104988254410c2054402c2, 0x6999811036b180a78600118110304a01),
    (0x1f0208e1049882544124210c202c2, 0x10380696800380296810381296820380a96840040044030381696830380e9685004044402004104400),
    (0x1e2e28e104988254412c202c2, 0x4070002a242d0001602af808bc22af828bc1aaf8c8bc000d6901c014b68ab802ab20526814b66ab80aab1e526794b60ab832ab18526600f8902a240a09),
    (0x1f020e2e28e104988254402c2, 0x4018902a242d0001da6b0218be22b2008f422b0238be1ab2028f41ab02d8be02b20c8f4002fe00b40028c8033a40769591a2af01aae8162a85919aaf04aae7962a559182af12aae61629b),
    (0x1e2e2e0208e104988254412c202c2, 0x1022240e800b4000aa1) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6_33 : Array (Nat × Nat) := #[ (0x1f0208a1049882544214412c202c2, 0x5470085202990e039869a9902f86b2ac),
    (0x1f020e2e28e104988254412c202c2, 0x4058001c002d0002a240769006242fc8005a40fa1),
    (0x1f0208e104988254415c612c2, 0x1acab58e00ac6661500ac4762700005a43e980f8cc0009004b03e810f82000320156ab304aa0783d9e000cc050d012640118ac6021519acba18e19ac4122719015200008012000101),
    (0x1f0208e104988254423c612c202c2, 0x1006243c00638600549) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock6 (b : Nat) : Array (Nat × Nat) :=
  if b < 17 then
    if b < 8 then
      if b < 4 then
        if b < 2 then
          if b < 1 then
            certificateBlock6_0
          else
            certificateBlock6_1
        else
          if b < 3 then
            certificateBlock6_2
          else
            certificateBlock6_3
      else
        if b < 6 then
          if b < 5 then
            certificateBlock6_4
          else
            certificateBlock6_5
        else
          if b < 7 then
            certificateBlock6_6
          else
            certificateBlock6_7
    else
      if b < 12 then
        if b < 10 then
          if b < 9 then
            certificateBlock6_8
          else
            certificateBlock6_9
        else
          if b < 11 then
            certificateBlock6_10
          else
            certificateBlock6_11
      else
        if b < 14 then
          if b < 13 then
            certificateBlock6_12
          else
            certificateBlock6_13
        else
          if b < 15 then
            certificateBlock6_14
          else
            if b < 16 then
              certificateBlock6_15
            else
              certificateBlock6_16
  else
    if b < 25 then
      if b < 21 then
        if b < 19 then
          if b < 18 then
            certificateBlock6_17
          else
            certificateBlock6_18
        else
          if b < 20 then
            certificateBlock6_19
          else
            certificateBlock6_20
      else
        if b < 23 then
          if b < 22 then
            certificateBlock6_21
          else
            certificateBlock6_22
        else
          if b < 24 then
            certificateBlock6_23
          else
            certificateBlock6_24
    else
      if b < 29 then
        if b < 27 then
          if b < 26 then
            certificateBlock6_25
          else
            certificateBlock6_26
        else
          if b < 28 then
            certificateBlock6_27
          else
            certificateBlock6_28
      else
        if b < 31 then
          if b < 30 then
            certificateBlock6_29
          else
            certificateBlock6_30
        else
          if b < 32 then
            certificateBlock6_31
          else
            if b < 33 then
              certificateBlock6_32
            else
              certificateBlock6_33
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock7_0 : Array (Nat × Nat) := #[ (0x1f0208e104988254412820040, 0x40c83032080c0402e100c85032000c0102e040c84032040c0002e000b0302a600a030266c0b0202a640a02026680b0002a700a0002660090302200080301e24090202204080201e20090002210080001e18070001a60060001600050301254040000e48050201250040100e4c050001248040400e58031800b800200006000112002000000),
    (0x1f0208e104988254412c202c2, 0x4102105c20168805900102305c181686058f4158805618150c052f0102d05c001680058cc158e056001502052c8158c056081500052c0140000ba40280046001080006240d0904020138004c001288048200d8804018138204c081286048180d8604000138c04c301280048000d80046001109042001008005a00f8003c000e88038800d88002201006005980f8203c080e86038780d86002181000005800f8c03c300e80038600d80002000189002240d09),
    (0x1f0208e104988254412c212820040, 0x40903070001b8301e240902070041b8201e200900070101b8001e18031800c00020001c00190001800161b06c001a830680c161a06c041a8206808161806c101a8006800198006400068006254180005e48189406004179306248180405e58141200c000292),
    (0x1f0608e104988254412c2, 0x425a10948024820910025a3094782480090f423a208e7c233c08af0222d0872021180826c202c07e641f3207ac8202a07e701f3007ac022690863021000820c206807e041f0807a20206607e101f0607a1817e000f80179200e481e00077801d92075681c80),
    (0x1f0608e104988254412c20040, 0x10c60c31020c20830040c61431000c20030010be102f810bc002e800b80c2d980b4602c9b0b0082b990ac682a9a0b0002b9c0ac602a980b86c2d800b4002c830b0682b810ac082a820b0602b840ac002a800606004180600004000a80029980a60029000a20c282100200000009e08272009a00260009e00271e09a0826020606017e00106003e0060001792010000392),
    (0x1f0208e104988254413c212c2, 0x11008440200fe003f400fa8c3e1e0f61c3d3d0fa883e1f0f6183d3c0fab43e180f6043d330fab03e190f6003d32062a804aa06270049c0f2003c060f0003b800a2c037e9005a43b000ea003a010e62435090022437e8005a03b010ea043a000e620350800220395a03d68338400410330604418389e0e078394c03d3033920044833000440038980e06037e9095a437000da0036010d78435090908437e8095a037010da0436000d78035080908034e60d19833840881033060859832860c87834e00d18033920884833000858032800c86028b00738000b0),
    (0x1f0208e1049c84988254412c20040, 0x414851180045811140414841180445801140031051120044050c00c31041120444040c008160006c70439810c602e0010a702d1c10860161806c10438010c002e1810a102d041080005180140041981060041001027c278009c78409e09e04271f063800518013801892014000492),
    (0x1f0208e10498837c60040, 0x44b0312c084a84129004b0512c004a81128f44b0412c044a80128f049831240048831200c49821240448821200849801241048801200041030ee8429000756841020ee8029010756c41000ee78290407578478011d684680),
    (0x1f0208e10498837c612c20040, 0x11520c54821501053c01521454801500453bd1521054811500053bc14c0c52801480c518314c08528114808518214c0052841480051801440c509b140004f8013c0c4e83138244d8914408509a140044f8113c084e82138204d88144005098140104f8413c004e80138184d8601c6006180346041830f08429800764841820f08029810764c41800f0782984076584d00133684c0012f681900042480600),
    (0x1f0208e10498837c6254412c20040, 0x11680c59801640c58831680859811640858821680059841640058801600c579815c0c569b16008579915c08569a16000579c15c0056980640001801606c578015c6c568316068578115c68568216060578415c6056800646001980646007180186007000640006000f2842a00078003ca00a8041e010f2782a04078105600156005500047800718046480700),
    (0x1f0208e104988254412c200800040, 0x4098601e005686138004d8002600078615a004e06136183d030aa181e800f4082a8707a0416180261832981081832000361007800f4342a8007a183d0c0aa041e870ca7842000c818161e026000d9201e18430610c003800),
    (0x1f0208e105bca4988254412c20040, 0x4611d18200600117e0c611c18204600017e085f0017a145f0117a105b04036105e0006c70590010c605d80174105c80170645c81170605b98058605b9816c105686138004d80028601b8015c604f0013a003da10ac001f060f6802b0107c1c5aaa06a000e2a0cc782d040841016e002860129206e001212),
    (0x1f0208e104988254412c202c20040, 0x46500192005b0001e0c6400172086402172000a80070005780140004f8010e0c5b0005868638018c081a0205860638218c001a00006600a80034601b0018a606200186001a0301e0c348010a0034000f8202b8007e003e060ae081f82040000a8004e301c0004c300f8c06c000f0c),
    (0x1f0208e1049884888254412c20040, 0x469001a20469011a2001485184006803114041484184046802114001a18026c0651c192705b80026c05b8010e606780176005a0003610670006800091802c0051181600050800fb0c2c00080a83ec20b004202b0cea82e00088a866aa19800659e04180091805c480b00),
    (0x1f0208e104988254412c208000040, 0x40bbe02ef0538214e004a0002e600b8014f5053bc128f03f030baf02280052100bbe052040bbc0d460303c0900035000c15024180fd682e8008af0353e0c000243c0d4f03002090f814ec02e6014c202e006a3c1a800698c),
    (0x1f020cf988e104988254412c20040, 0x11bc0c6e801b8006d831b4086c811b00414811b4006c841b01014841b0106c0114e085380128006b8018e6c60181ac60688217a64688017a706b9818e0c60001ac00689a17a04689817a100c18030005418150004a800fe842f0008cf06abc1160039bc0d88044010d604361e110103584055800c18054480c00) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock7_1 : Array (Nat × Nat) := #[ (0x1f0208e104988254412c209880040, 0x472051c8006c0002ef471801b400690017c60691817c000c98032005498152004b001c4046c00052106f001c2084500114040bbd0367061001c0601a180361061181c0001a000de78310009478403c0be00239e0dc7844800da7815ce032601592032006f9e118003a9e),
    (0x1f2e28e104988254412c202c2, 0x47a801e94079881e4a07a821e93879861e49478881e218780c1b0f07a8c1e92079801e46c788e1e20078021b0c8788c1e20878001b0c077801dc0002801d22076801d80075881d4205b081d21876821d80875861d4185b061d200768c1d83075801d4005b000460011090040000001d22074001ce0073081ca805b081d21874021ce0873061ca785b061d200740c1ce3073001ca605b00064240689018240589),
    (0x1f2e2f0208e104988254412c202c2, 0x1200007fd01fc207ea81f8007d881f4205bc0200087fce1fc187ea51f8087d861f4185bbd200307fc81fc007e9b1f8307d801f4005bb31dfa4140000ba477e91de00770001c241909018247c811f0207c841f0187c921f00016f01ee047b2010e4016ed1ee107b1e10e3416e31ee487b1810e0c198901c2406a1),
    (0x1f564f2e28e104988254412c2, 0x12212073c822030738c21e008e00084602100236008d33232cc8c2622e688b0222b488d09232248c5022e088b1a22aa08d35232d48c2422e608b0022b3c8d0b2322c8c4e22e008b1822a948a222287c89bc1b2f07c2d1d4b4122d2245488952212073c821e00871b21a6c861b2166c852c21264841920ec8831417ac8852a21270841c20ec0831217ac089632238c880c1ce30878021c0c86832180c85831f1a47569049a4856821204840120e20835017a20856621210840420e18834e17a1882e020980829220848818020520810c202f05d00),
    (0x1f0208e105bca498837c6254412c2, 0x4975325a1896012569c975225a1c960025698941e20e14941f20e10758404a10975d25a00960725684975c25a049606256807bda255680f5a255307bcc03d3092062480094800cc1833000a0007bda24c10938424a10920624478919e24278941820e4c941920e48939224c4892921ef30920024660911824260902a2407081922061081101d648129223fa48f0023b845c2123fa08f0123b805c201f59816e61f5987c041d610750415c784f0613a187d6005b807d601f04875921d448571813c004e80),
    (0x1f0208e10498837c6254402c2, 0x12a284a82029e0868c02a28ca81e29e0068bd29c88a71f29a006d3c29974a5dd29400a48029084a3a128d70a28028800a18228408a0a028d68a28228808a18028400a09e280b49f9827c009000208305db327ab09e19276009402210385f3227aa89e1c276089400210305f301f230761204c307c002758c7500273a09c0026e009b0826a805c88273989c0226e089b0626a785c862680099b3264007e6004380988c26030978015e00069813e000580),
    (0x1f0208e10498837c6254412c202c2, 0x4b15d2c2007f002c084afdc2bc00ae822b880afda2bc08ae802b8789f8020a309e00212389e0221230769204e30ade92b400ac801f00075801d4001b89273a0ac0023c085c8827398ac0223c005c861f98010001f9807c8c1da48761215e00500013e00ab831d60016e82ac00aaa010e2016e62ac08aa9e10e18aa332a60065b3047807b8c2a430739216a60198014000068010e241b89),
    (0x1f564f0208e104988254412c202c2, 0x11f66017002e600b9262e208b852272008f822e608b9242e200b84f272088f801d2b4102d1d2b47d98144e45833142cc9e80214389e8221430b7802dc00b68003e307f002d80cb5832d40cad692b600ace91f4000a092d204a7882d210a78628000b40c24000828c208305ae92ce000e69254300f8c03c3092331fc00948310e6c0d8000200aba11f4009d00055a897012cc80710a0559c97042cc78710704b8ca0000498c950c2ca60b20c2c648439b10e840a09),
    (0x1f0208e104988254412c200c0, 0x4bf812fe00bf001b700b8012b818958717ef4b8002b81c958617ef0b8072b800958117eccb8062b804958017ec87e861fa00be80162c0be012f600bd011ac24be002f604bd001ac20b00628e18b5802d40091062421886002160043062c000a3802d618b50624400908021818858610c00bc812f084bb802ec00bc802f080bb812ec04b00600598a38610c0000800e218281e082008d8410c1800862c000016028e0043060021838800a060208623648430000200ba8003c40ba00),
    (0x1f0208e106dcc4988254412c200c0, 0x4c70131a00c60131604c70031a04c60031600a08622a04a08722a0079001fa00a08022a1ca08122a1879061fa1879061e40051b6146c0483030600c0002ea00ba0031400c48031000a4062d800918621c00868029000b60624600870621a18c3a130c00c2b030e80c30130ac4c26030600c16004b98a4060499843980ccd8c08008470439e04b80a40004980439e0ccc0c086084a8439825440c000),
    (0x1f0208e107fce4988254412c2, 0x4cd2133480ccc01b900cc4132f04cb0032a00ca0132604c92132284cc4032f00cb0132a04ca0032600c92032280b8a32ba78a11e258f48b23180f4b8a22ba7ca11f258f08b22180f0c80431e10c1042e2b4ae9828460963322cb460332e2b0ae9928464963222cb0603232048c792304487f2a1fc709230164c0b8e92ba00a100258248b6918024b8e82ba04a101258208b6818020c86031f80c1601fd987f042481859061fd807f12248005900),
    (0x1f0208e107fce498837c6254412c2, 0x4d34134a00d20134684d34034a04d20034680d11e34214d11f34210ce0430810d05d33e00cf0131884d05c33e04cf0031880ceda255680f5a33b68c80433810c78431278c51e31078a19822e54a19922e50cd9224c4892922927087921e6487f12286008be3286048be233780936024b80a48421f8079e01fd8079e01e6485218148004880),
    (0x1f0208e104988254412c207c6, 0x4d92136280d8021af00d92336278d8001aef4d7a235e7cd7001baf0b72d2dab4b09824c609298178ccb9ac2bc64a21925a688c82182c8b9aa2bc70a21c25a608c80182c0b7692dba4b08024c00928017824b9e82bc04a20125a088c9a18220b9e62bc10a20425a008c9818218806020048c20016600c8002520cc78035b700f5c35800d58035408d4a031a80382035b680f5a35808d58235400d49e31a78381e178cc00b3350300f0c34e600e182c2600118178240089351200f4834e000e002c2000100),
    (0x1f0208e10498837c6254412c207c6, 0x4dcdd37174dbdd32000ce0031e00c1a135b70db0033e08c6a035b68db0233e00c69e2deb4a51822400939822200a29923408a29c234007a9220048b7e929400891824e00889828a048d1a28a108d181eb8080601eb807a9214a60528012400920333800955c36a00da202fa80955a36a08da1e2fa78bea130684382110ecc7b8c36630739216a60129829460121810e247bc83672073e016a001280294001200),
    (0x1f0208e104988254412c200c2, 0x47f811fe00950016900af812e4189707184f4af802e41c9706184f0af872e4009701184ccaf862e4049700184c8e18638600e1001bcc0b101296040f801ee04738006c24b100296000f811ee00738106c20de8638200e0002ac189b8618e18de8038218e0062ac009b8018e00df8103884df0037e000e2037c04de8600598de0032e00dd8637478638600218de8000580de0632e18dd8037460638000200ba900e040ba10),
    (0x1fe30f0208e104988254412c200c2, 0x47a001fe007a011fe047a011e800534114d0049c035a00e40634018c75a28c048c0628c008c0735a18e40034000c74c28c1c8c0028c188c0137000dc8036e00ce8030040ba902e840a60122000a60022004e38038c18e38638c00924033a0094902ca84e2802c600b2a038a04b181055c8d30438878711205590d3123886071042fa40c010) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock7_2 : Array (Nat × Nat) := #[ (0x1f020cf988e10498837c6254412c2, 0x138484d73c33200bf5d29af889811e07c151f29af089841e08815221e088781f150f8543c12af0e15d35c00ccbc2fc84dada39768d5da3960cda833560cd23c34800c980394f0e50039200ab5c38d709bdc36004963e342048b1f2f480ab5a38d689bda36010963c342108b222f478a69822708d84238c6cab1b26e6cd0c2258608b122f520a7c429e6483c420e64830d29f08a79c20f08839c20c40781205448a680227b0d86c38c0cab0326e0cd0ec258008b602f430a7ee29e0483ee20e04834929fb0a78420fb0838420d3078600558078601e0485418150004a80),
    (0x1f0208e106dcc4988254412c202c2, 0x4dea936200b8802f944e1a835e00cd002ff40a80621408a70622808789c05608a80021430a7002283078aa0563078aa1e27054b6152c04b303ada4eb001e0000c093aa00a68836400e39038240e01034400ae8028400bd802a218b48225018848221008a8802d230940021230840c3a8247800055a0e1003a680710830980d90030580d3083a420cb883a2c0e80039ec0be802f600380004b98a88604998970239c78e68239810439e04b80a88004980970c39c60e68c3984843981c4240c09),
    (0x1f0208e104988254412c20040, 0x10520c14821c41045040521414801c40445010521014811c40045000580c0d9810e6c1a1b058080d9910e681a1a058000d9c10e601a180586c0d8010e0c1a03058680d8110e081a02058600d8410e001a00006600d18006000d0006600069801a0005800a20c2821072008d800a2082820072048d810a200281e072108d84006600160034600180004480d00),
    (0x1f0208e104988254417c612c2, 0x4f6213d680b3021a100f6233d678b3001a0f4f5223d47ce9801c2f0f4ad3d0b40e981ec00728006accf3ac3cc64f2992aa089a8218cc8f3aa3cc70f29c2aa009a8018cc0b3e9005a4d38030400f2002520c670900224f1dc03d70f1013c204f00239e20efa00e080f1da03d68f1043c210f00039e18ef9e0e0781ab3002cceb92004485a80044000e9800460b3e93bc00ee802ca00b1e019c24ee683b604ed0139c08e6621c020ee663b610ed0439c00e6601c018ece03b180eb9216a00628018660dfc837d800f48),
    (0x1f0208e10498827c6254412c202c2, 0x4102d2c2007f00058ccafdc3f000e8022b880afda3f008e8002b878fb802c830fb0039a38fb0239a30f68c03e30fae93e800730002024f98026c08f98226c00100002024018903424978004a0012003e430f8923e0489780188007b181cc0072983cfa0f7803dc6863083cf98f7823dc6063063af80100000580ebe037e30f68c37c48629818800618006a240809),
    (0x1f0208e104988254412c202c200c2, 0x14020100001d00008893fa00ff8026200a90026000ff0027018ff06270007b811d00073802c400fe8029600df803da00df0106c20de863f800f78618e18de803f818f78018e001b0902224ec803f600ec0003a20f68004018e9003f4180d8604000e9063f4000d802d640fc902d4400d8806c200088),
    (0x1f0208e1049882544250412c202c2, 0x141260a00041124a88241130a880040b47fc82ce00163305638afc93d82014b205630afcc3d81814b0036000a8040f8d03631d200090940a009ce240a089ce040831018c404307e6002a007e6004a00120005b8c748005d88de803cf88162005d80de823cf80161e2c430fe8c29630ebe0006600a8003460ebe003a000e18058840909),
    (0x1f0208e10498837c6254412c2, 0x10548415203a81071400548c151e3a804713d05488151f3a800713c255740f5d30800c1002480c94832fa843821255700f5c30804c1012480894822fa803820255680f5a30810c1042480094802fa78381e05ab4129804860ab9b2745443b305ab0129904864ab9a2745043b205aa8129c04870ab982744843b00464810920044816e904a0012002ae0c9d6310e2416e804a0412012ae089d6210e2016e604a1012042ae009d6010e1811e00438001600478010e004648109206600069801a000580),
    (0x1f0208e104988254410c202c2, 0x5048941220b40019f01040141618b4871a4f504004161cb4861a4f1040741600b4811a4cd040641604b4801a4c9050641400ea801c6c1020100ba501013fe00f9013e0001c09034247c8004820760140a18ff033800cf9873ca18640640a00ff0d38034f9813ca0064001f20412091d801020000ba101003fe00f9003e0041c080342102863fc08e0023e618f2871901902803fc30e00c3e600f281190001c09034241c0803420138000404010000000ff80),
    (0x1f0208e104988254412c210c202c2, 0x502014060501011f20476801d8001c09408010180404007c801da04760107021028641800ac0619019028041818ac0019000140040604028003e00ec803e200ec000062412881da0410063820cf30603618100038234f300036000d880702012891da00140140600028103e04ec813e204ec0100620100738208f3070361c100138230f301036040d89070240d89006240089006200d88002200f8103e000f00),
    (0x1e0208e104988254412c202c2, 0x1403a503a03ea206571403ad039e3ea18656f42089081f3ac30723c403d503983ea006569420b108193ac087232420a9081c3ac0072301de0077000420103704060501012b420ac8819221036d4061101042b418ac861921903634064901122b400ac8019201078041da5068012f21037040000a5813e820f47119221036d40008a5843e818f46f19219036340030a5923e800f469192000309034840209),
    (0x1f020e0208e104988254412c202c2, 0x4018900c25025140e80ad88195c4b15105c20f48805901025340e78ad86195bcb15305c18f486058f5025d40e60ad80195a4b15d05c00f480058cc77e91de00770000c8403090082477e90460103f040804adf11942103ed40810adef1941903e340848ade91940011e91de0108e942200550905dc0b1013d3c4162805db4b1043d3bc162505d8cb1123d3a4161b006840321),
    (0x1f0208e1049882544214412c202c2, 0x5059827a01080e420007899032c9051b29c00102d2e460ee00058cc15021e264158c3866cf506052c014b2032c9084b42064788003225058127a65050229c650449410309e19278009d802bf25040c04e30130c3ec64ed803b4000d800546c7880041a0b9013b864160805724e1823d4c4148704f25044904d24af8c3b664fb003b4640d9903f24afc903d24af8c03e300f0c426650980424040d99036000080052240c89),
    (0x1f0208e104988254412c2054402c2, 0x5030040e007d9802ccd05982a009059a2a001031840e607d8002c2505802a06905822a0610498412009f9827e009f0005a007d9805638b9183d62014b205630b91a3d61814b0058cc0b3304e31048004c307fc83bc00fb983ba000d8005a607d8005728b9003d6c8148805720b9023d6c0148604f21049804d207f8c3bc60fb803ba600d98058240b0903f207fc803d207f8c03e300f0c2c260b080304000d98036000080) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock7 (b : Nat) : Array (Nat × Nat) :=
  if b < 1 then
    certificateBlock7_0
  else
    if b < 2 then
      certificateBlock7_1
    else
      certificateBlock7_2
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock8_0 : Array (Nat × Nat) := #[ (0x1f0208e104988254412c20040, 0x10200c080201e10070402014080001e04070102010080101e00070001a0c06180166c051b01a08061901668051a01a00061c01660051801a6c06000160c050301a68060101608050201a60060401600050000460001800400000001200041801000038000c0c02a100800018000c0802a000804018100c00029e0081001840046000e0000600100002480000),
    (0x1f0208e10498837c6254412c2, 0x10428410a00401007c00428c109e0400407bd04288109f0400007bc03f740f5d03a000e000360c0d03032840c2103f700f5c03a040e01036080d02032800c2003f680f5a03a100e04036000d00032780c1e02eb40b1802a600a1b0265405b302eb00b1902a640a1a0265005b202ea80b1c02a700a180264805b0024480892002480be902c000a800280c09e3016240be802c040a810280809e2016200be602c100a840280009e00161809600238000e00258008e0024480892012000418010000380),
    (0x1f0208e104988254412c202c2, 0x4132105a200b8801b00132305a180b8601af4160805818108c020f0132d05a000b8001acc160e058001082020c8160c058081080020c01580055a4150002400088000424000904c201480050000b0802a20060804c181482050080b0602a18060604c00148c050300b0002a000600024001389022001308003a0128003c00120804680060804420130600398128203c08120604678060604418130000380128c03c301200046600600044000109044240009) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock8 (b : Nat) : Array (Nat × Nat) :=
  certificateBlock8_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock9_0 : Array (Nat × Nat) := #[ (0x1f0208e104988254412c2, 0x10048401200030000400048c011e002f4003d00488011f002f0003c004b40118002cc0033004b00119002c80032004a8011c002c00030005a40100002240009005a00101002200008005980104002180006005800112002000000) ]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def certificateBlock9 (b : Nat) : Array (Nat × Nat) :=
  certificateBlock9_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def entryBlock : Nat → Nat → Array (Nat × Nat)
  | 0, b => certificateBlock0 b
  | 1, b => certificateBlock1 b
  | 2, b => certificateBlock2 b
  | 3, b => certificateBlock3 b
  | 4, b => certificateBlock4 b
  | 5, b => certificateBlock5 b
  | 6, b => certificateBlock6 b
  | 7, b => certificateBlock7 b
  | 8, b => certificateBlock8 b
  | 9, b => certificateBlock9 b
  | _, _ => #[]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def entry (k i : Nat) : Nat × Nat := ((entryBlock k (i / 16))[i % 16]?).getD (1,1)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def entryCount : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 => 29
  | 3 => 272
  | 4 => 1048
  | 5 => 1383
  | 6 => 532
  | 7 => 46
  | 8 => 3
  | 9 => 1
  | _ => 0

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def unpack (width : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | k+1, n => if n = 1 then [] else n % 2^width :: unpack width k (n >>> width)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def wires (r : ℕ × ℕ) : List V := (unpack 16 11 r.1).map (BitVec.ofNat 16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def links (r : ℕ × ℕ) : List ℕ := unpack 18 2000 r.2

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def pm (p : Fin 120) (i : Fin 16) : Fin 16 :=
  Fin.ofNat 16 ((permCode p.val >>> (5 * i.val)) % 32)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def sigma (p : Fin 120) (w : V) : V :=
  let packed := permCode p.val
  (BitVec.ofBoolListLE ((List.finRange 16).map fun i =>
    w.getLsbD (Fin.ofNat 16 ((packed >>> (5 * i.val)) % 32)).val)).setWidth 16

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sigma_bit (p : Fin 120) (w : V) (i : Fin 16) :
    (sigma p w).getLsbD i.val = w.getLsbD (pm p i).val := by
  unfold sigma
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp only [i.isLt, decide_true, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [i.isLt])]
  simp [List.getElem_finRange, pm]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem pm_onto : ∀ p : Fin 120, ∀ j : Fin 16, ∃ i : Fin 16, pm p i = j := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sigma_inj (p : Fin 120) : Function.Injective (sigma p) := by
  intro w v h
  apply BitVec.eq_of_getElem_eq
  intro i hi
  obtain ⟨j, hj⟩ := pm_onto p ⟨i,hi⟩
  have h' := congrArg (fun z : V => z.getLsbD j.val) h
  rw [sigma_bit, sigma_bit, hj] at h'
  simpa only [BitVec.getLsbD_eq_getElem hi] using h' 

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sigma_g : ∀ p, sigma p g = g := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sigma_const (p : Fin 120) : sigma p 0 = 0 ∧ sigma p (-1) = -1 := by
  constructor
  · apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [← BitVec.getLsbD_eq_getElem hi, sigma_bit p _ ⟨i,hi⟩]
    simp
  · change sigma p (BitVec.allOnes 16) = BitVec.allOnes 16
    apply BitVec.eq_of_getElem_eq
    intro i hi
    rw [← BitVec.getLsbD_eq_getElem hi, sigma_bit p _ ⟨i,hi⟩]
    simp only [BitVec.getLsbD_allOnes, BitVec.getElem_allOnes, decide_eq_true_eq]
    exact (pm p ⟨i,hi⟩).isLt

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sigma_mem (p : Fin 120) {a b z : V} (h : z ∈ dops a b) :
    sigma p z ∈ dops (sigma p a) (sigma p b) := by
  have h1 := Finset.mem_erase.mp h
  have h2 := Finset.mem_erase.mp h1.2
  apply Finset.mem_erase.mpr
  refine ⟨fun he => h1.1 (sigma_inj p (he.trans (sigma_const p).2.symm)), ?_⟩
  apply Finset.mem_erase.mpr
  refine ⟨fun he => h2.1 (sigma_inj p (he.trans (sigma_const p).1.symm)), ?_⟩
  simp only [List.mem_toFinset, ops, List.mem_cons, List.not_mem_nil, or_false] at h2 ⊢
  have compare (x y : V) (e : Fin 16 → Prop) (hxy : ∀ i : Fin 16, x.getLsbD i.val = y.getLsbD i.val) :
      x = y := by
    apply BitVec.eq_of_getElem_eq
    intro j hj
    simpa only [BitVec.getLsbD_eq_getElem hj] using hxy ⟨j,hj⟩
  rcases h2.2 with rfl | rfl | rfl | rfl
  · left
    apply compare (e := fun _ => True)
    intro i
    simp only [sigma_bit, BitVec.getLsbD_and]
  · right; left
    apply compare (e := fun _ => True)
    intro i
    simp only [sigma_bit, BitVec.getLsbD_or]
  · right; right; left
    apply compare (e := fun _ => True)
    intro i
    simp only [sigma_bit, BitVec.getLsbD_and, BitVec.getLsbD_not, i.isLt, (pm p i).isLt, decide_true, Bool.true_and]
  · right; right; right
    apply compare (e := fun _ => True)
    intro i
    simp only [sigma_bit, BitVec.getLsbD_and, BitVec.getLsbD_not, i.isLt, (pm p i).isLt, decide_true, Bool.true_and]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sigma_live (p : Fin 120) {k : ℕ} {s : Finset V} (h : live dops g k s) :
    live dops g k (s.image (sigma p)) := by
  induction k generalizing s with
  | zero => change s = {g} at h; simp [h, live, sigma_g]
  | succ k ih =>
    rcases h with h | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, ht⟩
    · exact Or.inl (ih h)
    · refine Or.inr ⟨_, Finset.mem_image_of_mem _ ha, _, Finset.mem_image_of_mem _ hb,
        fun eq => hab (sigma_inj p eq), _, sigma_mem p hz, ?_, r.image (sigma p), ?_, ?_⟩
      · intro hm
        obtain ⟨w, hw, eq⟩ := Finset.mem_image.mp hm
        exact hn (sigma_inj p eq ▸ hw)
      · simp [hs, Finset.image_insert]
      · simpa [Finset.image_insert] using ih ht



-- Four table lookups implement a permutation of the sixteen sample rows.
-- The proofs below verify each lookup against the bitwise definition.
namespace Nibble
def nibTable : Array Nat := #[
0xf000e000d000c000b000a00090008000700060005000400030002000100000000f000e000d000c000b000a00090008000700060005000400030002000100000000f000e000d000c000b000a00090008000700060005000400030002000100000000f000e000d000c000b000a0009000800070006000500040003000200010000,
0x8e008c008a00880086008400820080000e000c000a0008000600040002000000710070006100600051005000410040003100300021002000110010000100000000f000d000e000c000b0009000a0008000700050006000400030001000200000000f000e000d000c000b000a0009000800070006000500040003000200010000,
0xf000e000d000c0007000600050004000b000a0009000800030002000100000000d8009800d0009000c8008800c0008000580018005000100048000800400000002680260024802400228022002080200006800600048004000280020000800000017001600150014001300120011001000070006000500040003000200010000,
0x4980490048804800418041004080400009800900088008000180010000800000b400b000a400a00094009000840080003400300024002000140010000400000002680248026002400228020802200200006800480060004000280008002000000017001600150014001300120011001000070006000500040003000200010000,
0x8e008c008a0088000e000c000a00080086008400820080000600040002000000618041806100410060804080600040002180018021000100208000802000000010581050104810401018101010081000005800500048004000180010000800000027002600250024002300220021002000070006000500040003000200010000,
0x4980490048804800098009000880080041804100408040000180010000800000a6008600a4008400a2008200a00080002600060024000400220002002000000010581048105010401018100810101000005800480050004000180008001000000027002600250024002300220021002000070006000500040003000200010000,
0xf000e000b000a000d000c00090008000700060003000200050004000100000000f000e000d000c0007000600050004000b000a0009000800030002000100000000f000e000d000c0007000600050004000b000a0009000800030002000100000000f000e000d000c0007000600050004000b000a000900080003000200010000,
0x8e008c00860084008a008800820080000e000c00060004000a00080002000000710070006100600031003000210020005100500041004000110010000100000000f000d000e000c0007000500060004000b0009000a000800030001000200000000f000e000d000c0007000600050004000b000a000900080003000200010000,
0xf000e000b000a0007000600030002000d000c0009000800050004000100000000d4005400d0005000c4004400c0004000940014009000100084000400800000002a402a002840280022402200204020000a400a0008400800024002000040000001b001a001900180013001200110010000b000a000900080003000200010000,
0x2540250024402400214021002040200005400500044004000140010000400000d800d000c800c00098009000880080005800500048004000180010000800000002a4028402a00280022402040220020000a4008400a000800024000400200000001b001a001900180013001200110010000b000a000900080003000200010000,
0x8e008c00860084000e000c00060004008a008800820080000a0008000200000061402140610021006040204060002000414001404100010040400040400000001094109010841080101410101004100000940090008400800014001000040000002b002a002900280023002200210020000b000a000900080003000200010000,
0x2540250024402400054005000440040021402100204020000140010000400000ca008a00c8008800c2008200c00080004a000a004800080042000200400000001094108410901080101410041010100000940084009000800014000400100000002b002a002900280023002200210020000b000a000900080003000200010000,
0xf000e00070006000d000c00050004000b000a0003000200090008000100000000d8009800d00090005800180050001000c8008800c000800048000800400000002680260024802400068006000480040022802200208020000280020000800000017001600150014000700060005000400130012001100100003000200010000,
0x4980490041804100488048004080400009800900018001000880080000800000b400b000a400a00034003000240020009400900084008000140010000400000002680248026002400068004800600040022802080220020000280008002000000017001600150014000700060005000400130012001100100003000200010000,
0xf000e00070006000b000a00030002000d000c0005000400090008000100000000d4005400d00050009400140090001000c4004400c000400084000400800000002a402a00284028000a400a00084008002240220020402000024002000040000001b001a00190018000b000a0009000800130012001100100003000200010000,
0x2540250021402100244024002040200005400500014001000440040000400000d800d000c800c00058005000480040009800900088008000180010000800000002a4028402a0028000a4008400a0008002240204022002000024000400200000001b001a00190018000b000a0009000800130012001100100003000200010000,
0x4980490041804100098009000180010048804800408040000880080000800000a4402440a4002400a0402040a000200084400440840004008040004080000000120c120812041200100c100810041000020c020802040200000c0008000400000033003200310030002300220021002000130012001100100003000200010000,
0x2540250021402100054005000140010024402400204020000440040000400000c8804880c8004800c0804080c000400088800880880008008080008080000000120c120412081200100c100410081000020c020402080200000c0004000800000033003200310030002300220021002000130012001100100003000200010000,
0x8e008c000e000c008a0088000a00080086008400060004008200800002000000618041806100410021800180210001006080408060004000208000802000000010581050104810400058005000480040101810101008100000180010000800000027002600250024000700060005000400230022002100200003000200010000,
0x4980490009800900488048000880080041804100018001004080400000800000a6008600a40084002600060024000400a2008200a0008000220002002000000010581048105010400058004800500040101810081010100000180008001000000027002600250024000700060005000400230022002100200003000200010000,
0x8e008c000e000c0086008400060004008a0088000a000800820080000200000061402140610021004140014041000100604020406000200040400040400000001094109010841080009400900084008010141010100410000014001000040000002b002a00290028000b000a0009000800230022002100200003000200010000,
0x2540250005400500244024000440040021402100014001002040200000400000ca008a00c80088004a000a0048000800c2008200c000800042000200400000001094108410901080009400840090008010141004101010000014000400100000002b002a00290028000b000a0009000800230022002100200003000200010000,
0x4980490009800900418041000180010048804800088008004080400000800000a4402440a40024008440044084000400a0402040a00020008040004080000000120c120812041200020c020802040200100c100810041000000c0008000400000033003200310030001300120011001000230022002100200003000200010000,
0x2540250005400500214021000140010024402400044004002040200000400000c8804880c80048008880088088000800c0804080c00040008080008080000000120c120412081200020c020402080200100c100410081000000c0004000800000033003200310030001300120011001000230022002100200003000200010000,
0xf000d000e000c000b0009000a0008000700050006000400030001000200000000e800e000a800a000c800c0008800800068006000280020004800400008000000170016001500140013001200110010000700060005000400030002000100000000f000e000b000a000d000c0009000800070006000300020005000400010000,
0x8e008a008c00880086008200840080000e000a000c000800060002000400000070807000508050006080600040804000308030001080100020802000008000000170015001600140013001100120010000700050006000400030001000200000000f000e000b000a000d000c0009000800070006000300020005000400010000,
0xf000d000e000c0007000500060004000b0009000a000800030001000200000000b8009800a8008800b0009000a0008000380018002800080030001000200000004680460044804400428042004080400006800600048004000280020000800000017001600130012001500140011001000070006000300020005000400010000,
0x4980488049004800418040804100400009800880090008000180008001000000b200b00092009000a200a000820080003200300012001000220020000200000004680448046004400428040804200400006800480060004000280008002000000017001600130012001500140011001000070006000300020005000400010000,
0x8e008a008c0088000e000a000c00080086008200840080000600020004000000518041805080408051004100500040001180018010800080110001001000000020582050204820402018201020082000005800500048004000180010000800000027002600230022002500240021002000070006000300020005000400010000,
0x4980488049004800098008800900080041804080410040000180008001000000960086009200820094008400900080001600060012000200140004001000000020582048205020402018200820102000005800480050004000180008001000000027002600230022002500240021002000070006000300020005000400010000,
0xf000d000b0009000e000c000a0008000700050003000100060004000200000000e800e000a800a0006800600028002000c800c000880080004800400008000000170016001500140007000600050004001300120011001000030002000100000000f000e000b000a0007000600030002000d000c000900080005000400010000,
0x8e008a00860082008c008800840080000e000a00060002000c0008000400000070807000508050003080300010801000608060004080400020802000008000000170015001600140007000500060004001300110012001000030001000200000000f000e000b000a0007000600030002000d000c000900080005000400010000,
0xf000d000b00090007000500030001000e000c000a000800060004000200000000ac002c00a8002800a4002400a00020008c000c00880008008400040080000000522052005020500042204200402040001220120010201000022002000020000001d001c001900180015001400110010000d000c000900080005000400010000,
0x12c012801240120010c010801040100002c002800240020000c0008000400000e800e000c800c000a800a00088008000680060004800400028002000080000000522050205200500042204020420040001220102012001000022000200200000001d001c001900180015001400110010000d000c000900080005000400010000,
0x8e008a00860082000e000a00060002008c008800840080000c0008000400000050c010c050801080504010405000100040c000c04080008040400040400000002112211021022100201220102002200001120110010201000012001000020000002d002c002900280025002400210020000d000c000900080005000400010000,
0x12c012801240120002c002800240020010c010801040100000c0008000400000cc008c00c8008800c4008400c00080004c000c004800080044000400400000002112210221102100201220022010200001120102011001000012000200100000002d002c002900280025002400210020000d000c000900080005000400010000,
0xf000d00070005000e000c00060004000b000900030001000a0008000200000000b8009800a80088003800180028000800b0009000a000800030001000200000004680460044804400068006000480040042804200408040000280020000800000017001600130012000700060003000200150014001100100005000400010000,
0x4980488041804080490048004100400009800880018000800900080001000000b200b000920090003200300012001000a200a00082008000220020000200000004680448046004400068004800600040042804080420040000280008002000000017001600130012000700060003000200150014001100100005000400010000,
0xf000d00070005000b000900030001000e000c00060004000a0008000200000000ac002c00a80028008c000c0088000800a4002400a00020008400040080000000522052005020500012201200102010004220420040204000022002000020000001d001c00190018000d000c0009000800150014001100100005000400010000,
0x12c0128010c01080124012001040100002c0028000c000800240020000400000e800e000c800c0006800600048004000a800a0008800800028002000080000000522050205200500012201020120010004220402042004000022000200200000001d001c00190018000d000c0009000800150014001100100005000400010000,
0x49804880418040800980088001800080490048004100400009000800010000009240124092001200904010409000100082400240820002008040004080000000240a240824022400200a200820022000040a040804020400000a0008000200000035003400310030002500240021002000150014001100100005000400010000,
0x12c0128010c0108002c0028000c0008012401200104010000240020000400000c9004900c8004800c1004100c000400089000900880008008100010080000000240a240224082400200a200220082000040a040204080400000a0002000800000035003400310030002500240021002000150014001100100005000400010000,
0x8e008a000e000a008c0088000c00080086008200060002008400800004000000518041805080408011800180108000805100410050004000110001001000000020582050204820400058005000480040201820102008200000180010000800000027002600230022000700060003000200250024002100200005000400010000,
0x4980488009800880490048000900080041804080018000804100400001000000960086009200820016000600120002009400840090008000140004001000000020582048205020400058004800500040201820082010200000180008001000000027002600230022000700060003000200250024002100200005000400010000,
0x8e008a000e000a0086008200060002008c0088000c000800840080000400000050c010c05080108040c000c040800080504010405000100040400040400000002112211021022100011201100102010020122010200220000012001000020000002d002c00290028000d000c0009000800250024002100200005000400010000,
0x12c0128002c00280124012000240020010c0108000c000801040100000400000cc008c00c80088004c000c0048000800c4008400c000800044000400400000002112210221102100011201020110010020122002201020000012000200100000002d002c00290028000d000c0009000800250024002100200005000400010000,
0x49804880098008804180408001800080490048000900080041004000010000009240124092001200824002408200020090401040900010008040004080000000240a240824022400040a040804020400200a200820022000000a0008000200000035003400310030001500140011001000250024002100200005000400010000,
0x12c0128002c0028010c0108000c0008012401200024002001040100000400000c9004900c80048008900090088000800c1004100c00040008100010080000000240a240224082400040a040204080400200a200220082000000a0002000800000035003400310030001500140011001000250024002100200005000400010000,
0xf000b000e000a000d0009000c0008000700030006000200050001000400000000e400e00064006000c400c00044004000a400a0002400200084008000040000001b001a001900180013001200110010000b000a0009000800030002000100000000f000e00070006000d000c00050004000b000a000300020009000800010000,
0x8e0086008c0084008a008200880080000e0006000c0004000a00020008000000704070003040300060406000204020005040500010401000404040000040000001b0019001a00180013001100120010000b0009000a000800030001000200000000f000e00070006000d000c00050004000b000a000300020009000800010000,
0xf000b000e000a0007000300060002000d0009000c00080005000100040000000074005400640044007000500060004000340014002400040030001000200000008a408a008840880082408200804080000a400a0008400800024002000040000001b001a001300120019001800110010000b000a000300020009000800010000,
0x2540244025002400214020402100200005400440050004000140004001000000d200d00092009000c200c000820080005200500012001000420040000200000008a4088408a00880082408040820080000a4008400a000800024000400200000001b001a001300120019001800110010000b000a000300020009000800010000,
0x8e0086008c0084000e0006000c0004008a008200880080000a0002000800000031402140304020403100210030002000114001401040004011000100100000004094409040844080401440104004400000940090008400800014001000040000002b002a002300220029002800210020000b000a000300020009000800010000,
0x25402440250024000540044005000400214020402100200001400040010000009a008a009200820098008800900080001a000a001200020018000800100000004094408440904080401440044010400000940084009000800014000400100000002b002a002300220029002800210020000b000a000300020009000800010000,
0xf000b000d0009000e000a000c0008000700030005000100060002000400000000e400e00064006000a400a00024002000c400c0004400400084008000040000001b001a00190018000b000a00090008001300120011001000030002000100000000f000e00070006000b000a00030002000d000c000500040009000800010000,
0x8e0086008a0082008c008400880080000e0006000a0002000c00040008000000704070003040300050405000104010006040600020402000404040000040000001b0019001a0018000b0009000a0008001300110012001000030001000200000000f000e00070006000b000a00030002000d000c000500040009000800010000,
0xf000b000d00090007000300050001000e000a000c0008000600020004000000006c002c006400240068002800600020004c000c00440004004800080040000000922092009020900082208200802080001220120010201000022002000020000001d001c001500140019001800110010000d000c000500040009000800010000,
0x12c012401280120010c010401080100002c002400280020000c0004000800000e400e000a400a000c400c00084008000640060002400200044004000040000000922090209200900082208020820080001220102012001000022000200200000001d001c001500140019001800110010000d000c000500040009000800010000,
0x8e0086008a0082000e0006000a0002008c008400880080000c0004000800000030c010c030401040308010803000100020c000c02040004020800080200000004112411041024100401240104002400001120110010201000012001000020000002d002c002500240029002800210020000d000c000500040009000800010000,
0x12c012401280120002c002400280020010c010401080100000c0004000800000ac008c00a4008400a8008800a00080002c000c002400040028000800200000004112410241104100401240024010400001120102011001000012000200100000002d002c002500240029002800210020000d000c000500040009000800010000,
0xf000b00070003000e000a00060002000d000900050001000c000800040000000074005400640044003400140024000400700050006000400030001000200000008a408a00884088000a400a00084008008240820080408000024002000040000001b001a00130012000b000a0003000200190018001100100009000800010000,
0x2540244021402040250024002100200005400440014000400500040001000000d200d000920090005200500012001000c200c00082008000420040000200000008a4088408a0088000a4008400a0008008240804082008000024000400200000001b001a00130012000b000a0003000200190018001100100009000800010000,
0xf000b00070003000d000900050001000e000a00060002000c00080004000000006c002c00640024004c000c004400040068002800600020004800080040000000922092009020900012201200102010008220820080208000022002000020000001d001c00150014000d000c0005000400190018001100100009000800010000,
0x12c0124010c01040128012001080100002c0024000c000400280020000800000e400e000a400a0006400600024002000c400c0008400800044004000040000000922090209200900012201020120010008220802082008000022000200200000001d001c00150014000d000c0005000400190018001100100009000800010000,
0x2540244021402040054004400140004025002400210020000500040001000000928012809200120090801080900010008280028082000200808000808000000048064804480248004006400440024000080608040802080000060004000200000039003800310030002900280021002000190018001100100009000800010000,
0x12c0124010c0104002c0024000c0004012801200108010000280020000800000a5002500a4002400a1002100a00020008500050084000400810001008000000048064802480448004006400240044000080608020804080000060002000400000039003800310030002900280021002000190018001100100009000800010000,
0x8e0086000e0006008c0084000c0004008a0082000a000200880080000800000031402140304020401140014010400040310021003000200011000100100000004094409040844080009400900084008040144010400440000014001000040000002b002a00230022000b000a0003000200290028002100200009000800010000,
0x25402440054004402500240005000400214020400140004021002000010000009a008a00920082001a000a0012000200980088009000800018000800100000004094408440904080009400840090008040144004401040000014000400100000002b002a00230022000b000a0003000200290028002100200009000800010000,
0x8e0086000e0006008a0082000a0002008c0084000c000400880080000800000030c010c03040104020c000c020400040308010803000100020800080200000004112411041024100011201100102010040124010400240000012001000020000002d002c00250024000d000c0005000400290028002100200009000800010000,
0x12c0124002c00240128012000280020010c0104000c000401080100000800000ac008c00a40084002c000c0024000400a8008800a000800028000800200000004112410241104100011201020110010040124002401040000012000200100000002d002c00250024000d000c0005000400290028002100200009000800010000,
0x2540244005400440214020400140004025002400050004002100200001000000928012809200120082800280820002009080108090001000808000808000000048064804480248000806080408020800400640044002400000060004000200000039003800310030001900180011001000290028002100200009000800010000,
0x12c0124002c0024010c0104000c0004012801200028002001080100000800000a5002500a40024008500050084000400a1002100a0002000810001008000000048064802480448000806080208040800400640024004400000060002000400000039003800310030001900180011001000290028002100200009000800010000,
0xf0007000e0006000d0005000c0004000b0003000a0002000900010008000000009c0098001c00180094009000140010008c0088000c00080084008000040000006280620060806000428042004080400022802200208020000280020000800000017001600070006001500140005000400130012000300020011001000010000,
0x4980418049004100488040804800400009800180090001000880008008000000b040b00030403000a040a000204020009040900010401000804080000040000006280608062006000428040804200400022802080220020000280008002000000017001600070006001500140005000400130012000300020011001000010000,
0xf0007000e0006000b0003000a0002000d0005000c0004000900010008000000005c0054001c00140058005000180010004c0044000c0004004800400008000000a240a200a040a00082408200804080002240220020402000024002000040000001b001a000b000a001900180009000800130012000300020011001000010000,
0x2540214025002100244020402400200005400140050001000440004004000000d080d00050805000c080c00040804000908090001080100080808000008000000a240a040a200a00082408040820080002240204022002000024000400200000001b001a000b000a001900180009000800130012000300020011001000010000,
0x49804180490041000980018009000100488040804800400008800080080000003440244030402040340024003000200014400440104000401400040010000000820c820882048200800c800880048000020c020802040200000c0008000400000033003200230022003100300021002000130012000300020011001000010000,
0x25402140250021000540014005000100244020402400200004400040040000005880488050804080580048005000400018800880108000801800080010000000820c820482088200800c800480088000020c020402080200000c0004000800000033003200230022003100300021002000130012000300020011001000010000,
0xf0007000d0005000e0006000c0004000b000300090001000a00020008000000009c0098001c0018008c0088000c000800940090001400100084008000040000006280620060806000228022002080200042804200408040000280020000800000017001600070006001300120003000200150014000500040011001000010000,
0x4980418048804080490041004800400009800180088000800900010008000000b040b000304030009040900010401000a040a00020402000804080000040000006280608062006000228020802200200042804080420040000280008002000000017001600070006001300120003000200150014000500040011001000010000,
0xf0007000d0005000b000300090001000e0006000c0004000a00020008000000003c002c001c000c00380028001800080034002400140004003000200010000000c220c200c020c00082208200802080004220420040204000022002000020000001d001c000d000c001900180009000800150014000500040011001000010000,
0x12c010c012801080124010401200100002c000c0028000800240004002000000e100e00061006000c100c00041004000a100a0002100200081008000010000000c220c020c200c00082208020820080004220402042004000022000200200000001d001c000d000c001900180009000800150014000500040011001000010000,
0x49804180488040800980018008800080490041004800400009000100080000003240124030401040320012003000100022400240204000402200020020000000840a840884028400800a800880028000040a040804020400000a0008000200000035003400250024003100300021002000150014000500040011001000010000,
0x12c010c01280108002c000c002800080124010401200100002400040020000006900490061004100680048006000400029000900210001002800080020000000840a840284088400800a800280088000040a040204080400000a0002000800000035003400250024003100300021002000150014000500040011001000010000,
0xf0007000b0003000e0006000a0002000d000500090001000c00040008000000005c0054001c0014004c0044000c00040058005000180010004800400008000000a240a200a040a00022402200204020008240820080408000024002000040000001b001a000b000a001300120003000200190018000900080011001000010000,
0x2540214024402040250021002400200005400140044000400500010004000000d080d000508050009080900010801000c080c0004080400080808000008000000a240a040a200a00022402040220020008240804082008000024000400200000001b001a000b000a001300120003000200190018000900080011001000010000,
0xf0007000b0003000d000500090001000e0006000a0002000c00040008000000003c002c001c000c00340024001400040038002800180008003000200010000000c220c200c020c00042204200402040008220820080208000022002000020000001d001c000d000c001500140005000400190018000900080011001000010000,
0x12c010c012401040128010801200100002c000c0024000400280008002000000e100e00061006000a100a00021002000c100c0004100400081008000010000000c220c020c200c00042204020420040008220802082008000022000200200000001d001c000d000c001500140005000400190018000900080011001000010000,
0x2540214024402040054001400440004025002100240020000500010004000000528012805080108052001200500010004280028040800080420002004000000088068804880288008006800480028000080608040802080000060004000200000039003800290028003100300021002000190018000900080011001000010000,
0x12c010c01240104002c000c00240004012801080120010000280008002000000650025006100210064002400600020004500050041000100440004004000000088068802880488008006800280048000080608020804080000060002000400000039003800290028003100300021002000190018000900080011001000010000,
0x49804180098001804900410009000100488040800880008048004000080000003440244030402040144004401040004034002400300020001400040010000000820c820882048200020c020802040200800c800880048000000c0008000400000033003200230022001300120003000200310030002100200011001000010000,
0x25402140054001402500210005000100244020400440004024002000040000005880488050804080188008801080008058004800500040001800080010000000820c820482088200020c020402080200800c800480088000000c0004000800000033003200230022001300120003000200310030002100200011001000010000,
0x49804180098001804880408008800080490041000900010048004000080000003240124030401040224002402040004032001200300010002200020020000000840a840884028400040a040804020400800a800880028000000a0008000200000035003400250024001500140005000400310030002100200011001000010000,
0x12c010c002c000c01280108002800080124010400240004012001000020000006900490061004100290009002100010068004800600040002800080020000000840a840284088400040a040204080400800a800280088000000a0002000800000035003400250024001500140005000400310030002100200011001000010000,
0x2540214005400140244020400440004025002100050001002400200004000000528012805080108042800280408000805200120050001000420002004000000088068804880288000806080408020800800680048002800000060004000200000039003800290028001900180009000800310030002100200011001000010000,
0x12c010c002c000c0124010400240004012801080028000801200100002000000650025006100210045000500410001006400240060002000440004004000000088068802880488000806080208040800800680028004800000060002000400000039003800290028001900180009000800310030002100200011001000010000,
0x8e000e008c000c008a000a00880008008600060084000400820002008000000041c0418001c00180414041000140010040c0408000c00080404040000040000030183010300830002018201020082000101810101008100000180010000800000027002600070006002500240005000400230022000300020021002000010000,
0x4980098049000900488008804800080041800180410001004080008040000000864086000640060084408400044004008240820002400200804080000040000030183008301030002018200820102000101810081010100000180008001000000027002600070006002500240005000400230022000300020021002000010000,
0x8e000e008c000c0086000600840004008a000a0088000800820002008000000021c0214001c00140218021000180010020c0204000c0004020802000008000005014501050045000401440104004400010141010100410000014001000040000002b002a000b000a002900280009000800230022000300020021002000010000,
0x25400540250005002440044024000400214001402100010020400040200000008a808a000a800a008880880008800800828082000280020080808000008000005014500450105000401440044010400010141004101010000014000400100000002b002a000b000a002900280009000800230022000300020021002000010000,
0x49800980490009004180018041000100488008804800080040800080400000002640244006400440260024000600040022402040024000402200200002000000900c900890049000800c800880048000100c100810041000000c0008000400000033003200130012003100300011001000230022000300020021002000010000,
0x25400540250005002140014021000100244004402400040020400040200000004a8048800a8008804a0048000a00080042804080028000804200400002000000900c900490089000800c800480088000100c100410081000000c0004000800000033003200130012003100300011001000230022000300020021002000010000,
0x8e000e008a000a008c000c00880008008600060082000200840004008000000041c0418001c0018040c0408000c000804140410001400100404040000040000030183010300830001018101010081000201820102008200000180010000800000027002600070006002300220003000200250024000500040021002000010000,
0x4980098048800880490009004800080041800180408000804100010040000000864086000640060082408200024002008440840004400400804080000040000030183008301030001018100810101000201820082010200000180008001000000027002600070006002300220003000200250024000500040021002000010000,
0x8e000e008a000a0086000600820002008c000c0088000800840004008000000011c010c001c000c01180108001800080114010400140004011001000010000006012601060026000401240104002400020122010200220000012001000020000002d002c000d000c002900280009000800250024000500040021002000010000,
0x12c002c012800280124002401200020010c000c01080008010400040100000008d008c000d000c008900880009000800850084000500040081008000010000006012600260106000401240024010400020122002201020000012000200100000002d002c000d000c002900280009000800250024000500040021002000010000,
0x49800980488008804180018040800080490009004800080041000100400000001640124006400240160012000600020014401040044000401400100004000000a00aa008a002a000800a800880028000200a200820022000000a0008000200000035003400150014003100300011001000250024000500040021002000010000,
0x12c002c01280028010c000c010800080124002401200020010400040100000004d0049000d0009004c0048000c00080045004100050001004400400004000000a00aa002a008a000800a800280088000200a200220082000000a0002000800000035003400150014003100300011001000250024000500040021002000010000,
0x8e000e00860006008c000c00840004008a000a0082000200880008008000000021c0214001c0014020c0204000c00040218021000180010020802000008000005014501050045000101410101004100040144010400440000014001000040000002b002a000b000a002300220003000200290028000900080021002000010000,
0x25400540244004402500050024000400214001402040004021000100200000008a808a000a800a008280820002800200888088000880080080808000008000005014500450105000101410041010100040144004401040000014000400100000002b002a000b000a002300220003000200290028000900080021002000010000,
0x8e000e00860006008a000a00820002008c000c0084000400880008008000000011c010c001c000c01140104001400040118010800180008011001000010000006012601060026000201220102002200040124010400240000012001000020000002d002c000d000c002500240005000400290028000900080021002000010000,
0x12c002c012400240128002801200020010c000c01040004010800080100000008d008c000d000c008500840005000400890088000900080081008000010000006012600260106000201220022010200040124002401040000012000200100000002d002c000d000c002500240005000400290028000900080021002000010000,
0x25400540244004402140014020400040250005002400040021000100200000001a8012800a8002801a0012000a00020018801080088000801800100008000000c006c004c002c0008006800480028000400640044002400000060004000200000039003800190018003100300011001000290028000900080021002000010000,
0x12c002c01240024010c000c010400040128002801200020010800080100000002d0025000d0005002c0024000c00040029002100090001002800200008000000c006c002c004c0008006800280048000400640024004400000060002000400000039003800190018003100300011001000290028000900080021002000010000,
0x49800980418001804900090041000100488008804080008048000800400000002640244006400440224020400240004026002400060004002200200002000000900c900890049000100c100810041000800c800880048000000c0008000400000033003200130012002300220003000200310030001100100021002000010000,
0x25400540214001402500050021000100244004402040004024000400200000004a8048800a80088042804080028000804a0048000a0008004200400002000000900c900490089000100c100410081000800c800480088000000c0004000800000033003200130012002300220003000200310030001100100021002000010000,
0x49800980418001804880088040800080490009004100010048000800400000001640124006400240144010400440004016001200060002001400100004000000a00aa008a002a000200a200820022000800a800880028000000a0008000200000035003400150014002500240005000400310030001100100021002000010000,
0x12c002c010c000c01280028010800080124002401040004012000200100000004d0049000d00090045004100050001004c0048000c0008004400400004000000a00aa002a008a000200a200220082000800a800280088000000a0002000800000035003400150014002500240005000400310030001100100021002000010000,
0x25400540214001402440044020400040250005002100010024000400200000001a8012800a80028018801080088000801a0012000a0002001800100008000000c006c004c002c0004006400440024000800680048002800000060004000200000039003800190018002900280009000800310030001100100021002000010000,
0x12c002c010c000c01240024010400040128002801080008012000200100000002d0025000d00050029002100090001002c0024000c0004002800200008000000c006c002c004c0004006400240044000800680028004800000060002000400000039003800190018002900280009000800310030001100100021002000010000
]

def nib (w : V) (k : Fin 4) : BitVec 4 := (w >>> (4*k.val)).setWidth 4
def chunk (k : Fin 4) (b : BitVec 4) : V := b.setWidth 16 <<< (4*k.val)
def nibLookup (p : Fin 120) (k : Fin 4) (b : BitVec 4) : V :=
  BitVec.ofNat 16 (nibTable[p.val]! >>> (16*(16*k.val+b.toNat)))
def fastSigma (p : Fin 120) (w : V) : V :=
  nibLookup p 0 (nib w 0) ||| nibLookup p 1 (nib w 1) |||
  nibLookup p 2 (nib w 2) ||| nibLookup p 3 (nib w 3)


def table0 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 0 k b = sigma 0 (chunk k b) := by decide +kernel
def table1 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 1 k b = sigma 1 (chunk k b) := by decide +kernel
def table2 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 2 k b = sigma 2 (chunk k b) := by decide +kernel
def table3 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 3 k b = sigma 3 (chunk k b) := by decide +kernel
def table4 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 4 k b = sigma 4 (chunk k b) := by decide +kernel
def table5 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 5 k b = sigma 5 (chunk k b) := by decide +kernel
def table6 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 6 k b = sigma 6 (chunk k b) := by decide +kernel
def table7 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 7 k b = sigma 7 (chunk k b) := by decide +kernel
def table8 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 8 k b = sigma 8 (chunk k b) := by decide +kernel
def table9 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 9 k b = sigma 9 (chunk k b) := by decide +kernel

def table10 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 10 k b = sigma 10 (chunk k b) := by decide +kernel
def table11 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 11 k b = sigma 11 (chunk k b) := by decide +kernel
def table12 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 12 k b = sigma 12 (chunk k b) := by decide +kernel
def table13 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 13 k b = sigma 13 (chunk k b) := by decide +kernel
def table14 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 14 k b = sigma 14 (chunk k b) := by decide +kernel
def table15 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 15 k b = sigma 15 (chunk k b) := by decide +kernel
def table16 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 16 k b = sigma 16 (chunk k b) := by decide +kernel
def table17 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 17 k b = sigma 17 (chunk k b) := by decide +kernel
def table18 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 18 k b = sigma 18 (chunk k b) := by decide +kernel
def table19 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 19 k b = sigma 19 (chunk k b) := by decide +kernel

def table20 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 20 k b = sigma 20 (chunk k b) := by decide +kernel
def table21 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 21 k b = sigma 21 (chunk k b) := by decide +kernel
def table22 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 22 k b = sigma 22 (chunk k b) := by decide +kernel
def table23 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 23 k b = sigma 23 (chunk k b) := by decide +kernel
def table24 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 24 k b = sigma 24 (chunk k b) := by decide +kernel
def table25 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 25 k b = sigma 25 (chunk k b) := by decide +kernel
def table26 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 26 k b = sigma 26 (chunk k b) := by decide +kernel
def table27 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 27 k b = sigma 27 (chunk k b) := by decide +kernel
def table28 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 28 k b = sigma 28 (chunk k b) := by decide +kernel
def table29 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 29 k b = sigma 29 (chunk k b) := by decide +kernel

def table30 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 30 k b = sigma 30 (chunk k b) := by decide +kernel
def table31 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 31 k b = sigma 31 (chunk k b) := by decide +kernel
def table32 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 32 k b = sigma 32 (chunk k b) := by decide +kernel
def table33 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 33 k b = sigma 33 (chunk k b) := by decide +kernel
def table34 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 34 k b = sigma 34 (chunk k b) := by decide +kernel
def table35 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 35 k b = sigma 35 (chunk k b) := by decide +kernel
def table36 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 36 k b = sigma 36 (chunk k b) := by decide +kernel
def table37 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 37 k b = sigma 37 (chunk k b) := by decide +kernel
def table38 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 38 k b = sigma 38 (chunk k b) := by decide +kernel
def table39 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 39 k b = sigma 39 (chunk k b) := by decide +kernel

def table40 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 40 k b = sigma 40 (chunk k b) := by decide +kernel
def table41 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 41 k b = sigma 41 (chunk k b) := by decide +kernel
def table42 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 42 k b = sigma 42 (chunk k b) := by decide +kernel
def table43 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 43 k b = sigma 43 (chunk k b) := by decide +kernel
def table44 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 44 k b = sigma 44 (chunk k b) := by decide +kernel
def table45 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 45 k b = sigma 45 (chunk k b) := by decide +kernel
def table46 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 46 k b = sigma 46 (chunk k b) := by decide +kernel
def table47 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 47 k b = sigma 47 (chunk k b) := by decide +kernel
def table48 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 48 k b = sigma 48 (chunk k b) := by decide +kernel
def table49 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 49 k b = sigma 49 (chunk k b) := by decide +kernel

def table50 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 50 k b = sigma 50 (chunk k b) := by decide +kernel
def table51 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 51 k b = sigma 51 (chunk k b) := by decide +kernel
def table52 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 52 k b = sigma 52 (chunk k b) := by decide +kernel
def table53 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 53 k b = sigma 53 (chunk k b) := by decide +kernel
def table54 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 54 k b = sigma 54 (chunk k b) := by decide +kernel
def table55 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 55 k b = sigma 55 (chunk k b) := by decide +kernel
def table56 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 56 k b = sigma 56 (chunk k b) := by decide +kernel
def table57 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 57 k b = sigma 57 (chunk k b) := by decide +kernel
def table58 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 58 k b = sigma 58 (chunk k b) := by decide +kernel
def table59 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 59 k b = sigma 59 (chunk k b) := by decide +kernel

def table60 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 60 k b = sigma 60 (chunk k b) := by decide +kernel
def table61 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 61 k b = sigma 61 (chunk k b) := by decide +kernel
def table62 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 62 k b = sigma 62 (chunk k b) := by decide +kernel
def table63 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 63 k b = sigma 63 (chunk k b) := by decide +kernel
def table64 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 64 k b = sigma 64 (chunk k b) := by decide +kernel
def table65 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 65 k b = sigma 65 (chunk k b) := by decide +kernel
def table66 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 66 k b = sigma 66 (chunk k b) := by decide +kernel
def table67 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 67 k b = sigma 67 (chunk k b) := by decide +kernel
def table68 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 68 k b = sigma 68 (chunk k b) := by decide +kernel
def table69 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 69 k b = sigma 69 (chunk k b) := by decide +kernel

def table70 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 70 k b = sigma 70 (chunk k b) := by decide +kernel
def table71 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 71 k b = sigma 71 (chunk k b) := by decide +kernel
def table72 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 72 k b = sigma 72 (chunk k b) := by decide +kernel
def table73 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 73 k b = sigma 73 (chunk k b) := by decide +kernel
def table74 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 74 k b = sigma 74 (chunk k b) := by decide +kernel
def table75 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 75 k b = sigma 75 (chunk k b) := by decide +kernel
def table76 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 76 k b = sigma 76 (chunk k b) := by decide +kernel
def table77 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 77 k b = sigma 77 (chunk k b) := by decide +kernel
def table78 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 78 k b = sigma 78 (chunk k b) := by decide +kernel
def table79 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 79 k b = sigma 79 (chunk k b) := by decide +kernel

def table80 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 80 k b = sigma 80 (chunk k b) := by decide +kernel
def table81 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 81 k b = sigma 81 (chunk k b) := by decide +kernel
def table82 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 82 k b = sigma 82 (chunk k b) := by decide +kernel
def table83 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 83 k b = sigma 83 (chunk k b) := by decide +kernel
def table84 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 84 k b = sigma 84 (chunk k b) := by decide +kernel
def table85 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 85 k b = sigma 85 (chunk k b) := by decide +kernel
def table86 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 86 k b = sigma 86 (chunk k b) := by decide +kernel
def table87 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 87 k b = sigma 87 (chunk k b) := by decide +kernel
def table88 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 88 k b = sigma 88 (chunk k b) := by decide +kernel
def table89 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 89 k b = sigma 89 (chunk k b) := by decide +kernel

def table90 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 90 k b = sigma 90 (chunk k b) := by decide +kernel
def table91 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 91 k b = sigma 91 (chunk k b) := by decide +kernel
def table92 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 92 k b = sigma 92 (chunk k b) := by decide +kernel
def table93 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 93 k b = sigma 93 (chunk k b) := by decide +kernel
def table94 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 94 k b = sigma 94 (chunk k b) := by decide +kernel
def table95 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 95 k b = sigma 95 (chunk k b) := by decide +kernel
def table96 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 96 k b = sigma 96 (chunk k b) := by decide +kernel
def table97 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 97 k b = sigma 97 (chunk k b) := by decide +kernel
def table98 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 98 k b = sigma 98 (chunk k b) := by decide +kernel
def table99 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 99 k b = sigma 99 (chunk k b) := by decide +kernel

def table100 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 100 k b = sigma 100 (chunk k b) := by decide +kernel
def table101 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 101 k b = sigma 101 (chunk k b) := by decide +kernel
def table102 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 102 k b = sigma 102 (chunk k b) := by decide +kernel
def table103 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 103 k b = sigma 103 (chunk k b) := by decide +kernel
def table104 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 104 k b = sigma 104 (chunk k b) := by decide +kernel
def table105 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 105 k b = sigma 105 (chunk k b) := by decide +kernel
def table106 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 106 k b = sigma 106 (chunk k b) := by decide +kernel
def table107 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 107 k b = sigma 107 (chunk k b) := by decide +kernel
def table108 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 108 k b = sigma 108 (chunk k b) := by decide +kernel
def table109 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 109 k b = sigma 109 (chunk k b) := by decide +kernel

def table110 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 110 k b = sigma 110 (chunk k b) := by decide +kernel
def table111 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 111 k b = sigma 111 (chunk k b) := by decide +kernel
def table112 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 112 k b = sigma 112 (chunk k b) := by decide +kernel
def table113 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 113 k b = sigma 113 (chunk k b) := by decide +kernel
def table114 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 114 k b = sigma 114 (chunk k b) := by decide +kernel
def table115 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 115 k b = sigma 115 (chunk k b) := by decide +kernel
def table116 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 116 k b = sigma 116 (chunk k b) := by decide +kernel
def table117 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 117 k b = sigma 117 (chunk k b) := by decide +kernel
def table118 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 118 k b = sigma 118 (chunk k b) := by decide +kernel
def table119 : ∀ k : Fin 4, ∀ b : BitVec 4, nibLookup 119 k b = sigma 119 (chunk k b) := by decide +kernel

theorem lookup_ok (p : Fin 120) : ∀ k : Fin 4, ∀ b : BitVec 4,
    nibLookup p k b = sigma p (chunk k b) := by
  fin_cases p
  · exact table0
  · exact table1
  · exact table2
  · exact table3
  · exact table4
  · exact table5
  · exact table6
  · exact table7
  · exact table8
  · exact table9
  · exact table10
  · exact table11
  · exact table12
  · exact table13
  · exact table14
  · exact table15
  · exact table16
  · exact table17
  · exact table18
  · exact table19
  · exact table20
  · exact table21
  · exact table22
  · exact table23
  · exact table24
  · exact table25
  · exact table26
  · exact table27
  · exact table28
  · exact table29
  · exact table30
  · exact table31
  · exact table32
  · exact table33
  · exact table34
  · exact table35
  · exact table36
  · exact table37
  · exact table38
  · exact table39
  · exact table40
  · exact table41
  · exact table42
  · exact table43
  · exact table44
  · exact table45
  · exact table46
  · exact table47
  · exact table48
  · exact table49
  · exact table50
  · exact table51
  · exact table52
  · exact table53
  · exact table54
  · exact table55
  · exact table56
  · exact table57
  · exact table58
  · exact table59
  · exact table60
  · exact table61
  · exact table62
  · exact table63
  · exact table64
  · exact table65
  · exact table66
  · exact table67
  · exact table68
  · exact table69
  · exact table70
  · exact table71
  · exact table72
  · exact table73
  · exact table74
  · exact table75
  · exact table76
  · exact table77
  · exact table78
  · exact table79
  · exact table80
  · exact table81
  · exact table82
  · exact table83
  · exact table84
  · exact table85
  · exact table86
  · exact table87
  · exact table88
  · exact table89
  · exact table90
  · exact table91
  · exact table92
  · exact table93
  · exact table94
  · exact table95
  · exact table96
  · exact table97
  · exact table98
  · exact table99
  · exact table100
  · exact table101
  · exact table102
  · exact table103
  · exact table104
  · exact table105
  · exact table106
  · exact table107
  · exact table108
  · exact table109
  · exact table110
  · exact table111
  · exact table112
  · exact table113
  · exact table114
  · exact table115
  · exact table116
  · exact table117
  · exact table118
  · exact table119

theorem sigma_or (p : Fin 120) (a b : V) : sigma p (a ||| b) = sigma p a ||| sigma p b := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have h : (sigma p (a ||| b)).getLsbD i = (sigma p a ||| sigma p b).getLsbD i := by
    rw [BitVec.getLsbD_or, sigma_bit p (a ||| b) ⟨i,hi⟩,
      sigma_bit p a ⟨i,hi⟩, sigma_bit p b ⟨i,hi⟩, BitVec.getLsbD_or]
  simpa only [BitVec.getLsbD_eq_getElem hi] using h

set_option maxRecDepth 5000 in
set_option maxHeartbeats 1000000 in
theorem chunk_all (w : V) :
    chunk 0 (nib w 0) ||| chunk 1 (nib w 1) |||
    chunk 2 (nib w 2) ||| chunk 3 (nib w 3) = w := by
  have h1 : nib w 3 ++ nib w 2 ++ nib w 1 ++ nib w 0 = w := by
    simp only [nib, BitVec.setWidth_ushiftRight_eq_extractLsb]
    change w.extractLsb' 12 4 ++ w.extractLsb' 8 4 ++ w.extractLsb' 4 4 ++ w.extractLsb' 0 4 = w
    rw [BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 12 = 8 + 4),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 8 = 4 + 4),
      BitVec.extractLsb'_append_extractLsb'_eq_extractLsb' (by decide : 4 = 0 + 4)]
    simp
  have h2 := congrArg (BitVec.setWidth 16) h1
  rw [BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or] at h2
  simp only [BitVec.setWidth_eq] at h2
  calc
    _ = (nib w 3).setWidth 16 <<< 12 ||| (nib w 2).setWidth 16 <<< 8 |||
        (nib w 1).setWidth 16 <<< 4 ||| (nib w 0).setWidth 16 := by simp [chunk]; ac_rfl
    _ = w := by simpa using h2

theorem fastSigma_eq (p : Fin 120) (w : V) : fastSigma p w = sigma p w := by
  unfold fastSigma
  simp only [lookup_ok, ← sigma_or, chunk_all]

end Nibble

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def insertSorted (a : V) : List V → List V
  | [] => [a]
  | b :: bs => if a.toNat ≤ b.toNat then a :: b :: bs else b :: insertSorted a bs

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem insert_perm (a : V) (ws : List V) : (insertSorted a ws).Perm (a :: ws) := by
  induction ws with
  | nil => exact List.Perm.refl _
  | cons b bs ih =>
    simp only [insertSorted]
    split
    · exact List.Perm.refl _
    · exact (ih.cons b).trans (.swap _ _ _)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def sorted : List V → List V
  | [] => []
  | a :: ws => insertSorted a (sorted ws)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sorted_perm (ws : List V) : (sorted ws).Perm ws := by
  induction ws with
  | nil => exact List.Perm.refl _
  | cons a ws ih => exact (insert_perm a (sorted ws)).trans (ih.cons a)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def checkLink (prev : ℕ) (t : List V) (code : ℕ) : Bool :=
  (code / 128 < entryCount prev) &&
    (sorted (t.map (Nibble.fastSigma (Fin.ofNat 120 (code % 128)))) == wires (entry prev (code / 128)))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def checkLinks (prev : ℕ) : List (List V) → List ℕ → Bool
  | [], [] => true
  | t::ts, c::cs => checkLink prev t c && checkLinks prev ts cs
  | _, _ => false

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem link_of_mem {prev : ℕ} {ts : List (List V)} {cs : List ℕ}
    (hc : checkLinks prev ts cs = true) {t} (ht : t ∈ ts) :
    ∃ c, checkLink prev t c = true := by
  induction ts generalizing cs with
  | nil => simp at ht
  | cons u us ih =>
    cases cs with
    | nil => simp [checkLinks] at hc
    | cons c cs =>
      change checkLink prev u c && checkLinks prev us cs = true at hc
      rw [Bool.and_eq_true] at hc
      obtain ⟨h1, h2⟩ := hc
      rcases List.mem_cons.mp ht with rfl | ht
      · exact ⟨c,h1⟩
      · exact ih h2 ht

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem link_sound {k : ℕ} {t : List V} {c : ℕ}
    (h : checkLink k t c = true) (ht : live dops g k t.toFinset) :
    ∃ j < entryCount k, live dops g k (wires (entry k j)).toFinset := by
  simp only [checkLink, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨hi,he⟩ := h
  let p := Fin.ofNat 120 (c % 128)
  have hp : (wires (entry k (c / 128))).toFinset = t.toFinset.image (sigma p) := by
    rw [← he]
    ext w
    simp only [List.mem_toFinset, List.Perm.mem_iff (sorted_perm _),
      Finset.mem_image, List.mem_map, p, Nibble.fastSigma_eq]
  refine ⟨c / 128, hi, ?_⟩
  rw [hp]
  exact sigma_live p ht

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def checkEntry (k : ℕ) (r : ℕ × ℕ) : Bool :=
  let ws := wires r
  (ws != [g]) && (decide ws.Nodup) &&
    if k = 0 then true else checkLinks (k-1) (quickNext (k-1) ws) (links r)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem step_valid (k : ℕ)
    (checks : ∀ j < entryCount k, checkEntry k (entry k j) = true)
    (prev : k > 0 → ∀ j < entryCount (k-1), ¬ live dops g (k-1) (wires (entry (k-1) j)).toFinset) :
    ∀ j < entryCount k, ¬ live dops g k (wires (entry k j)).toFinset := by
  intro j hj run
  have H := checks j hj
  simp only [checkEntry, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq] at H
  obtain ⟨⟨notgoal, nd⟩, chk⟩ := H
  cases k with
  | zero => exact notgoal (singleton_small nd run)
  | succ k =>
    simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel] at chk
    rw [quickNext_eq] at chk
    rcases next_complete nd run with eq | ⟨t, ht, hl⟩
    · exact notgoal eq
    obtain ⟨c, hc⟩ := link_of_mem chk ht
    obtain ⟨u, hu, hlu⟩ := link_sound hc hl
    exact prev (by omega) u hu hlu

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def chunk (k offset count : ℕ) : Bool :=
  (List.range count).all fun i => checkEntry k (entry k (offset+i))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem chunk_sound {k offset count j : ℕ} (h : chunk k offset count = true)
    (ha : offset ≤ j) (hb : j < offset + count) :
    checkEntry k (entry k j) = true := by
  have hmem : j - offset ∈ List.range count := List.mem_range.mpr (by omega)
  have hc := List.all_eq_true.mp h _ hmem
  simpa only [Nat.add_sub_of_le ha] using hc


set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem raw_needed {k : ℕ} {S : Finset V} (sub : S ⊆ inp.toFinset)
    (h : live dops g k S) : S = inp.toFinset := by
  apply Finset.Subset.antisymm sub
  intro w hw
  let atIndex : Fin 5 → V := fun i => inp.getD i.val 0
  have index (v : V) (hv : v ∈ inp) : ∃ i, atIndex i = v := by
    obtain ⟨i, hi, he⟩ := List.getElem_of_mem hv
    refine ⟨⟨i, by simpa [inp] using hi⟩, ?_⟩
    exact (List.getD_eq_getElem ..).trans he
  have target : ∀ i : Fin 5, ∃ p : Fin 10, ∃ q : Fin 6,
      g.getLsbD (6+p.val) ≠ g.getLsbD q.val ∧
      ∀ j : Fin 5, (atIndex j).getLsbD (6+p.val) ≠ (atIndex j).getLsbD q.val →
        atIndex j = atIndex i := by decide +kernel
  obtain ⟨i, hi⟩ := index w (List.mem_toFinset.mp hw)
  obtain ⟨p,q,hg,uniq⟩ := target i
  obtain ⟨a,ha,hd⟩ := live_separates
      (fun t : V => t.getLsbD (6 + p.val) ≠ t.getLsbD q.val) hg
      (fun a b z hz hd => by
        have hmem := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).2
        simp only [ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hmem
        by_contra! fail
        obtain ⟨ha, hb⟩ := fail
        apply hd
        have hp : 6 + p.val < 16 := by omega
        have hq : q.val < 16 := by omega
        rcases hmem with rfl | rfl | rfl | rfl <;>
          simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hp, hq, decide_true, Bool.true_and, ha, hb]) h
  obtain ⟨j, hj⟩ := index a (List.mem_toFinset.mp (sub ha))
  have he := uniq j (by rwa [hj])
  rw [hi, hj] at he
  exact he ▸ ha


set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem chunk_glue {k offset a b : ℕ}
    (ha : chunk k offset a = true) (hb : chunk k (offset+a) b = true) :
    chunk k offset (a+b) = true := by
  apply List.all_eq_true.mpr
  intro j hj
  have hlt := List.mem_range.mp hj
  by_cases hja : j < a
  · exact List.all_eq_true.mp ha _ (List.mem_range.mpr hja)
  · have hmem : j-a ∈ List.range b := List.mem_range.mpr (by omega)
    have h := List.all_eq_true.mp hb _ hmem
    have he : offset+a+(j-a) = offset+j := by omega
    simpa only [he] using h
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done0 : chunk 0 0 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done1 : chunk 1 0 0 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c2_0 : chunk 2 0 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c2_16 : chunk 2 16 13 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done2 : chunk 2 0 29 = true := (@chunk_glue 2 0 16 13 c2_0 c2_16)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_0 : chunk 3 0 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_16 : chunk 3 16 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_32 : chunk 3 32 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_48 : chunk 3 48 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_64 : chunk 3 64 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_80 : chunk 3 80 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_96 : chunk 3 96 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_112 : chunk 3 112 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_128 : chunk 3 128 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_144 : chunk 3 144 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_160 : chunk 3 160 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_176 : chunk 3 176 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_192 : chunk 3 192 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_208 : chunk 3 208 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_224 : chunk 3 224 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_240 : chunk 3 240 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c3_256 : chunk 3 256 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done3 : chunk 3 0 272 = true := (@chunk_glue 3 0 128 144 (@chunk_glue 3 0 64 64 (@chunk_glue 3 0 32 32 (@chunk_glue 3 0 16 16 c3_0 c3_16) (@chunk_glue 3 32 16 16 c3_32 c3_48)) (@chunk_glue 3 64 32 32 (@chunk_glue 3 64 16 16 c3_64 c3_80) (@chunk_glue 3 96 16 16 c3_96 c3_112))) (@chunk_glue 3 128 64 80 (@chunk_glue 3 128 32 32 (@chunk_glue 3 128 16 16 c3_128 c3_144) (@chunk_glue 3 160 16 16 c3_160 c3_176)) (@chunk_glue 3 192 32 48 (@chunk_glue 3 192 16 16 c3_192 c3_208) (@chunk_glue 3 224 16 32 c3_224 (@chunk_glue 3 240 16 16 c3_240 c3_256)))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_0 : chunk 4 0 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_16 : chunk 4 16 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_32 : chunk 4 32 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_48 : chunk 4 48 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_64 : chunk 4 64 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_80 : chunk 4 80 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_96 : chunk 4 96 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_112 : chunk 4 112 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_128 : chunk 4 128 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_144 : chunk 4 144 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_160 : chunk 4 160 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_176 : chunk 4 176 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_192 : chunk 4 192 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_208 : chunk 4 208 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_224 : chunk 4 224 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_240 : chunk 4 240 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_256 : chunk 4 256 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_272 : chunk 4 272 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_288 : chunk 4 288 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_304 : chunk 4 304 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_320 : chunk 4 320 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_336 : chunk 4 336 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_352 : chunk 4 352 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_368 : chunk 4 368 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_384 : chunk 4 384 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_400 : chunk 4 400 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_416 : chunk 4 416 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_432 : chunk 4 432 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_448 : chunk 4 448 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_464 : chunk 4 464 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_480 : chunk 4 480 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_496 : chunk 4 496 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_512 : chunk 4 512 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_528 : chunk 4 528 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_544 : chunk 4 544 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_560 : chunk 4 560 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_576 : chunk 4 576 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_592 : chunk 4 592 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_608 : chunk 4 608 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_624 : chunk 4 624 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_640 : chunk 4 640 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_656 : chunk 4 656 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_672 : chunk 4 672 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_688 : chunk 4 688 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_704 : chunk 4 704 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_720 : chunk 4 720 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_736 : chunk 4 736 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_752 : chunk 4 752 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_768 : chunk 4 768 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_784 : chunk 4 784 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_800 : chunk 4 800 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_816 : chunk 4 816 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_832 : chunk 4 832 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_848 : chunk 4 848 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_864 : chunk 4 864 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_880 : chunk 4 880 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_896 : chunk 4 896 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_912 : chunk 4 912 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_928 : chunk 4 928 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_944 : chunk 4 944 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_960 : chunk 4 960 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_976 : chunk 4 976 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_992 : chunk 4 992 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_1008 : chunk 4 1008 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_1024 : chunk 4 1024 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c4_1040 : chunk 4 1040 8 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done4 : chunk 4 0 1048 = true := (@chunk_glue 4 0 528 520 (@chunk_glue 4 0 256 272 (@chunk_glue 4 0 128 128 (@chunk_glue 4 0 64 64 (@chunk_glue 4 0 32 32 (@chunk_glue 4 0 16 16 c4_0 c4_16) (@chunk_glue 4 32 16 16 c4_32 c4_48)) (@chunk_glue 4 64 32 32 (@chunk_glue 4 64 16 16 c4_64 c4_80) (@chunk_glue 4 96 16 16 c4_96 c4_112))) (@chunk_glue 4 128 64 64 (@chunk_glue 4 128 32 32 (@chunk_glue 4 128 16 16 c4_128 c4_144) (@chunk_glue 4 160 16 16 c4_160 c4_176)) (@chunk_glue 4 192 32 32 (@chunk_glue 4 192 16 16 c4_192 c4_208) (@chunk_glue 4 224 16 16 c4_224 c4_240)))) (@chunk_glue 4 256 128 144 (@chunk_glue 4 256 64 64 (@chunk_glue 4 256 32 32 (@chunk_glue 4 256 16 16 c4_256 c4_272) (@chunk_glue 4 288 16 16 c4_288 c4_304)) (@chunk_glue 4 320 32 32 (@chunk_glue 4 320 16 16 c4_320 c4_336) (@chunk_glue 4 352 16 16 c4_352 c4_368))) (@chunk_glue 4 384 64 80 (@chunk_glue 4 384 32 32 (@chunk_glue 4 384 16 16 c4_384 c4_400) (@chunk_glue 4 416 16 16 c4_416 c4_432)) (@chunk_glue 4 448 32 48 (@chunk_glue 4 448 16 16 c4_448 c4_464) (@chunk_glue 4 480 16 32 c4_480 (@chunk_glue 4 496 16 16 c4_496 c4_512)))))) (@chunk_glue 4 528 256 264 (@chunk_glue 4 528 128 128 (@chunk_glue 4 528 64 64 (@chunk_glue 4 528 32 32 (@chunk_glue 4 528 16 16 c4_528 c4_544) (@chunk_glue 4 560 16 16 c4_560 c4_576)) (@chunk_glue 4 592 32 32 (@chunk_glue 4 592 16 16 c4_592 c4_608) (@chunk_glue 4 624 16 16 c4_624 c4_640))) (@chunk_glue 4 656 64 64 (@chunk_glue 4 656 32 32 (@chunk_glue 4 656 16 16 c4_656 c4_672) (@chunk_glue 4 688 16 16 c4_688 c4_704)) (@chunk_glue 4 720 32 32 (@chunk_glue 4 720 16 16 c4_720 c4_736) (@chunk_glue 4 752 16 16 c4_752 c4_768)))) (@chunk_glue 4 784 128 136 (@chunk_glue 4 784 64 64 (@chunk_glue 4 784 32 32 (@chunk_glue 4 784 16 16 c4_784 c4_800) (@chunk_glue 4 816 16 16 c4_816 c4_832)) (@chunk_glue 4 848 32 32 (@chunk_glue 4 848 16 16 c4_848 c4_864) (@chunk_glue 4 880 16 16 c4_880 c4_896))) (@chunk_glue 4 912 64 72 (@chunk_glue 4 912 32 32 (@chunk_glue 4 912 16 16 c4_912 c4_928) (@chunk_glue 4 944 16 16 c4_944 c4_960)) (@chunk_glue 4 976 32 40 (@chunk_glue 4 976 16 16 c4_976 c4_992) (@chunk_glue 4 1008 16 24 c4_1008 (@chunk_glue 4 1024 16 8 c4_1024 c4_1040)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_0 : chunk 5 0 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_16 : chunk 5 16 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_32 : chunk 5 32 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_48 : chunk 5 48 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_64 : chunk 5 64 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_80 : chunk 5 80 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_96 : chunk 5 96 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_112 : chunk 5 112 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_128 : chunk 5 128 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_144 : chunk 5 144 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_160 : chunk 5 160 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_176 : chunk 5 176 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_192 : chunk 5 192 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_208 : chunk 5 208 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_224 : chunk 5 224 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_240 : chunk 5 240 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_256 : chunk 5 256 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_272 : chunk 5 272 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_288 : chunk 5 288 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_304 : chunk 5 304 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_320 : chunk 5 320 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_336 : chunk 5 336 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_352 : chunk 5 352 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_368 : chunk 5 368 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_384 : chunk 5 384 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_400 : chunk 5 400 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_416 : chunk 5 416 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_432 : chunk 5 432 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_448 : chunk 5 448 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_464 : chunk 5 464 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_480 : chunk 5 480 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_496 : chunk 5 496 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_512 : chunk 5 512 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_528 : chunk 5 528 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_544 : chunk 5 544 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_560 : chunk 5 560 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_576 : chunk 5 576 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_592 : chunk 5 592 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_608 : chunk 5 608 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_624 : chunk 5 624 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_640 : chunk 5 640 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_656 : chunk 5 656 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_672 : chunk 5 672 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_688 : chunk 5 688 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_704 : chunk 5 704 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_720 : chunk 5 720 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_736 : chunk 5 736 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_752 : chunk 5 752 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_768 : chunk 5 768 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_784 : chunk 5 784 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_800 : chunk 5 800 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_816 : chunk 5 816 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_832 : chunk 5 832 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_848 : chunk 5 848 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_864 : chunk 5 864 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_880 : chunk 5 880 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_896 : chunk 5 896 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_912 : chunk 5 912 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_928 : chunk 5 928 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_944 : chunk 5 944 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_960 : chunk 5 960 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_976 : chunk 5 976 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_992 : chunk 5 992 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1008 : chunk 5 1008 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1024 : chunk 5 1024 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1040 : chunk 5 1040 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1056 : chunk 5 1056 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1072 : chunk 5 1072 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1088 : chunk 5 1088 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1104 : chunk 5 1104 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1120 : chunk 5 1120 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1136 : chunk 5 1136 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1152 : chunk 5 1152 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1168 : chunk 5 1168 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1184 : chunk 5 1184 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1200 : chunk 5 1200 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1216 : chunk 5 1216 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1232 : chunk 5 1232 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1248 : chunk 5 1248 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1264 : chunk 5 1264 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1280 : chunk 5 1280 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1296 : chunk 5 1296 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1312 : chunk 5 1312 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1328 : chunk 5 1328 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1344 : chunk 5 1344 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1360 : chunk 5 1360 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c5_1376 : chunk 5 1376 7 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done5 : chunk 5 0 1383 = true := (@chunk_glue 5 0 688 695 (@chunk_glue 5 0 336 352 (@chunk_glue 5 0 160 176 (@chunk_glue 5 0 80 80 (@chunk_glue 5 0 32 48 (@chunk_glue 5 0 16 16 c5_0 c5_16) (@chunk_glue 5 32 16 32 c5_32 (@chunk_glue 5 48 16 16 c5_48 c5_64))) (@chunk_glue 5 80 32 48 (@chunk_glue 5 80 16 16 c5_80 c5_96) (@chunk_glue 5 112 16 32 c5_112 (@chunk_glue 5 128 16 16 c5_128 c5_144)))) (@chunk_glue 5 160 80 96 (@chunk_glue 5 160 32 48 (@chunk_glue 5 160 16 16 c5_160 c5_176) (@chunk_glue 5 192 16 32 c5_192 (@chunk_glue 5 208 16 16 c5_208 c5_224))) (@chunk_glue 5 240 48 48 (@chunk_glue 5 240 16 32 c5_240 (@chunk_glue 5 256 16 16 c5_256 c5_272)) (@chunk_glue 5 288 16 32 c5_288 (@chunk_glue 5 304 16 16 c5_304 c5_320))))) (@chunk_glue 5 336 176 176 (@chunk_glue 5 336 80 96 (@chunk_glue 5 336 32 48 (@chunk_glue 5 336 16 16 c5_336 c5_352) (@chunk_glue 5 368 16 32 c5_368 (@chunk_glue 5 384 16 16 c5_384 c5_400))) (@chunk_glue 5 416 48 48 (@chunk_glue 5 416 16 32 c5_416 (@chunk_glue 5 432 16 16 c5_432 c5_448)) (@chunk_glue 5 464 16 32 c5_464 (@chunk_glue 5 480 16 16 c5_480 c5_496)))) (@chunk_glue 5 512 80 96 (@chunk_glue 5 512 32 48 (@chunk_glue 5 512 16 16 c5_512 c5_528) (@chunk_glue 5 544 16 32 c5_544 (@chunk_glue 5 560 16 16 c5_560 c5_576))) (@chunk_glue 5 592 48 48 (@chunk_glue 5 592 16 32 c5_592 (@chunk_glue 5 608 16 16 c5_608 c5_624)) (@chunk_glue 5 640 16 32 c5_640 (@chunk_glue 5 656 16 16 c5_656 c5_672)))))) (@chunk_glue 5 688 352 343 (@chunk_glue 5 688 176 176 (@chunk_glue 5 688 80 96 (@chunk_glue 5 688 32 48 (@chunk_glue 5 688 16 16 c5_688 c5_704) (@chunk_glue 5 720 16 32 c5_720 (@chunk_glue 5 736 16 16 c5_736 c5_752))) (@chunk_glue 5 768 48 48 (@chunk_glue 5 768 16 32 c5_768 (@chunk_glue 5 784 16 16 c5_784 c5_800)) (@chunk_glue 5 816 16 32 c5_816 (@chunk_glue 5 832 16 16 c5_832 c5_848)))) (@chunk_glue 5 864 80 96 (@chunk_glue 5 864 32 48 (@chunk_glue 5 864 16 16 c5_864 c5_880) (@chunk_glue 5 896 16 32 c5_896 (@chunk_glue 5 912 16 16 c5_912 c5_928))) (@chunk_glue 5 944 48 48 (@chunk_glue 5 944 16 32 c5_944 (@chunk_glue 5 960 16 16 c5_960 c5_976)) (@chunk_glue 5 992 16 32 c5_992 (@chunk_glue 5 1008 16 16 c5_1008 c5_1024))))) (@chunk_glue 5 1040 176 167 (@chunk_glue 5 1040 80 96 (@chunk_glue 5 1040 32 48 (@chunk_glue 5 1040 16 16 c5_1040 c5_1056) (@chunk_glue 5 1072 16 32 c5_1072 (@chunk_glue 5 1088 16 16 c5_1088 c5_1104))) (@chunk_glue 5 1120 48 48 (@chunk_glue 5 1120 16 32 c5_1120 (@chunk_glue 5 1136 16 16 c5_1136 c5_1152)) (@chunk_glue 5 1168 16 32 c5_1168 (@chunk_glue 5 1184 16 16 c5_1184 c5_1200)))) (@chunk_glue 5 1216 80 87 (@chunk_glue 5 1216 32 48 (@chunk_glue 5 1216 16 16 c5_1216 c5_1232) (@chunk_glue 5 1248 16 32 c5_1248 (@chunk_glue 5 1264 16 16 c5_1264 c5_1280))) (@chunk_glue 5 1296 48 39 (@chunk_glue 5 1296 16 32 c5_1296 (@chunk_glue 5 1312 16 16 c5_1312 c5_1328)) (@chunk_glue 5 1344 16 23 c5_1344 (@chunk_glue 5 1360 16 7 c5_1360 c5_1376)))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_0 : chunk 6 0 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_16 : chunk 6 16 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_32 : chunk 6 32 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_48 : chunk 6 48 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_64 : chunk 6 64 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_80 : chunk 6 80 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_96 : chunk 6 96 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_112 : chunk 6 112 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_128 : chunk 6 128 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_144 : chunk 6 144 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_160 : chunk 6 160 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_176 : chunk 6 176 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_192 : chunk 6 192 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_208 : chunk 6 208 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_224 : chunk 6 224 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_240 : chunk 6 240 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_256 : chunk 6 256 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_272 : chunk 6 272 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_288 : chunk 6 288 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_304 : chunk 6 304 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_320 : chunk 6 320 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_336 : chunk 6 336 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_352 : chunk 6 352 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_368 : chunk 6 368 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_384 : chunk 6 384 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_400 : chunk 6 400 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_416 : chunk 6 416 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_432 : chunk 6 432 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_448 : chunk 6 448 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_464 : chunk 6 464 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_480 : chunk 6 480 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_496 : chunk 6 496 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_512 : chunk 6 512 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c6_528 : chunk 6 528 4 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done6 : chunk 6 0 532 = true := (@chunk_glue 6 0 272 260 (@chunk_glue 6 0 128 144 (@chunk_glue 6 0 64 64 (@chunk_glue 6 0 32 32 (@chunk_glue 6 0 16 16 c6_0 c6_16) (@chunk_glue 6 32 16 16 c6_32 c6_48)) (@chunk_glue 6 64 32 32 (@chunk_glue 6 64 16 16 c6_64 c6_80) (@chunk_glue 6 96 16 16 c6_96 c6_112))) (@chunk_glue 6 128 64 80 (@chunk_glue 6 128 32 32 (@chunk_glue 6 128 16 16 c6_128 c6_144) (@chunk_glue 6 160 16 16 c6_160 c6_176)) (@chunk_glue 6 192 32 48 (@chunk_glue 6 192 16 16 c6_192 c6_208) (@chunk_glue 6 224 16 32 c6_224 (@chunk_glue 6 240 16 16 c6_240 c6_256))))) (@chunk_glue 6 272 128 132 (@chunk_glue 6 272 64 64 (@chunk_glue 6 272 32 32 (@chunk_glue 6 272 16 16 c6_272 c6_288) (@chunk_glue 6 304 16 16 c6_304 c6_320)) (@chunk_glue 6 336 32 32 (@chunk_glue 6 336 16 16 c6_336 c6_352) (@chunk_glue 6 368 16 16 c6_368 c6_384))) (@chunk_glue 6 400 64 68 (@chunk_glue 6 400 32 32 (@chunk_glue 6 400 16 16 c6_400 c6_416) (@chunk_glue 6 432 16 16 c6_432 c6_448)) (@chunk_glue 6 464 32 36 (@chunk_glue 6 464 16 16 c6_464 c6_480) (@chunk_glue 6 496 16 20 c6_496 (@chunk_glue 6 512 16 4 c6_512 c6_528))))))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c7_0 : chunk 7 0 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c7_16 : chunk 7 16 16 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c7_32 : chunk 7 32 14 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done7 : chunk 7 0 46 = true := (@chunk_glue 7 0 16 30 c7_0 (@chunk_glue 7 16 16 14 c7_16 c7_32))
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c8_0 : chunk 8 0 3 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done8 : chunk 8 0 3 = true := c8_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def c9_0 : chunk 9 0 1 = true := by decide +kernel
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
def done9 : chunk 9 0 1 = true := c9_0
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem checks (k : ℕ) (hk : k ≤ 9) :
    ∀ j < entryCount k, checkEntry k (entry k j) = true := by
  intro j hj
  interval_cases k
  · exact @chunk_sound 0 0 0 j done0 (Nat.zero_le j) hj
  · exact @chunk_sound 1 0 0 j done1 (Nat.zero_le j) hj
  · exact @chunk_sound 2 0 29 j done2 (Nat.zero_le j) hj
  · exact @chunk_sound 3 0 272 j done3 (Nat.zero_le j) hj
  · exact @chunk_sound 4 0 1048 j done4 (Nat.zero_le j) hj
  · exact @chunk_sound 5 0 1383 j done5 (Nat.zero_le j) hj
  · exact @chunk_sound 6 0 532 j done6 (Nat.zero_le j) hj
  · exact @chunk_sound 7 0 46 j done7 (Nat.zero_le j) hj
  · exact @chunk_sound 8 0 3 j done8 (Nat.zero_le j) hj
  · exact @chunk_sound 9 0 1 j done9 (Nat.zero_le j) hj

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rejected (k : ℕ) (hk : k ≤ 9) :
    ∀ j < entryCount k, ¬ live dops g k (wires (entry k j)).toFinset := by
  induction k with
  | zero => exact step_valid 0 (checks _ hk) (fun h => False.elim (by omega))
  | succ k ih =>
    exact step_valid (k+1) (checks _ hk) (fun _ => by simpa using ih (by omega))

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem base : ¬ build dops g 9 inp.toFinset := by
  intro h
  obtain ⟨s,hs,run⟩ := compress h
  rw [raw_needed hs run] at run
  have eq : wires (entry 9 0) = inp := by decide +kernel
  exact rejected 9 (by decide) 0 (by decide) (by simpa only [eq] using run)

end
end PEqualNP.Outside.L_meta_10610.Cert

namespace PEqualNP.Outside.L_meta_10610.Signed
open PEqualNP.Outside.L_meta_10610
def sampleRow (j : Fin 16) : Fin 32 := ![0, 1, 2, 3, 4, 5, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25] j
def sample (w : W) : Cert.V :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 16 => w[(sampleRow k).val]))).cast List.length_ofFn

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sample_bit (w : W) (j : ℕ) (hj : j < 16) :
    (sample w)[j] = w[(sampleRow ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [sample, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sample_ops (a b z : W) (hz : z ∈ basicOps a b) :
    sample z ∈ Cert.ops (sample a) (sample b) := by
  have hand (u v : W) : sample (u &&& v) = (sample u &&& sample v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [sample_bit, BitVec.getElem_and]
  have hor (u v : W) : sample (u ||| v) = (sample u ||| sample v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [sample_bit, BitVec.getElem_or]
  have hnot (u : W) : sample (~~~u) = ~~~sample u :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [sample_bit, BitVec.getElem_not]
  simp only [basicOps, ops, Cert.ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl|rfl|rfl|rfl <;> simp [hand, hor, hnot]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem sample_lower (cert : ¬ build Cert.dops Cert.g 9 Cert.inp.toFinset) :
    ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t 9 cliqueInputs.toFinset → False := by
  intro t ht run
  have transport {k av} (h : build basicOps t k av) (avail : Finset Cert.V)
      (inv : ∀ a ∈ av, (sample a)[0] = false ∧ (sample a = 0 ∨ sample a ∈ avail)) :
          (sample t)[0] = false ∧ (sample t = 0 ∨ build Cert.dops (sample t) k avail) := by
    induction k generalizing av avail with
    | zero => exact inv t h
    | succ k ih =>
      rcases h with skip|⟨a,ha,b,hb,hab,z,hz,tail⟩
      · obtain ⟨q,r⟩ := ih skip avail inv
        exact ⟨q,r.imp_right Or.inl⟩
      obtain ⟨fa,sa⟩ := inv a ha
      obtain ⟨fb,sb⟩ := inv b hb
      have hz' := sample_ops a b z hz
      have opts := hz'
      simp only [Cert.ops, List.mem_cons, List.not_mem_nil, or_false] at opts
      have fz : (sample z)[0] = false := by
        rcases opts with e|e|e|e <;> simp [e,fa,fb]
      by_cases keep : sample z = 0 ∨ sample z ∈ avail
      · obtain ⟨q,r⟩ := ih tail avail (by
          intro w hw
          rcases Finset.mem_insert.mp hw with rfl|hw
          · exact ⟨fz,keep⟩
          · exact inv w hw)
        exact ⟨q,r.imp_right Or.inl⟩
      have fresh : sample z ≠ 0 ∧ sample z ∉ avail := not_or.mp keep
      have extra : sample z ≠ -1 := fun h => by simpa [h] using fz
      have useful : sample a ∈ avail ∧ sample b ∈ avail ∧ sample a ≠ sample b := by
        rcases sa with sa|sa
        · rcases opts with e|e|e|e <;> simp [sa] at e <;> grind
        rcases sb with sb|sb
        · rcases opts with e|e|e|e <;> simp [sb] at e <;> grind
        refine ⟨sa,sb,?_⟩
        intro eq
        rcases opts with e|e|e|e <;> simp [eq] at e <;> grind
      obtain ⟨q,r⟩ := ih tail (insert (sample z) avail) (by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl|hw
        · exact ⟨fz,Or.inr (Finset.mem_insert_self ..)⟩
        obtain ⟨d,e⟩ := inv w hw
        exact ⟨d,e.imp_right (Finset.mem_insert_of_mem ·)⟩)
      refine ⟨q,r.imp_right (fun hr => Or.inr ⟨_,useful.1,_,useful.2.1,useful.2.2,_,?_,hr⟩)⟩
      exact Finset.mem_erase.mpr ⟨extra,Finset.mem_erase.mpr ⟨fresh.1,List.mem_toFinset.mpr hz'⟩⟩
  have init : ∀ w ∈ cliqueInputs, (sample w)[0] = false ∧ sample w ∈ Cert.inp := by
    intro w hw
    simp only [cliqueInputs,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  obtain ⟨f,hr⟩ := transport run Cert.inp.toFinset (fun w hw => by
    have hi := init w (List.mem_toFinset.mp hw)
    exact ⟨hi.1,Or.inr (List.mem_toFinset.mpr hi.2)⟩)
  rcases ht with rfl|rfl
  · have e : sample goal = Cert.g := by decide +kernel
    rw [e] at hr
    exact hr.elim (by decide +kernel) cert
  · exact (by decide +kernel : ¬ (sample (~~~goal))[0] = false) f
end PEqualNP.Outside.L_meta_10610.Signed


namespace PEqualNP.Outside.L_meta_10610.Signed

-- Each added vertex has a pair of rows distinguished only by its input.
-- Keeping that input live forces one binary gate to disappear under restriction.
def liftBound (k : Nat) (ws : List W) := ∀ t, (t = goal ∨ t = ~~~goal) → build basicOps t k ws.toFinset → False
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem stepLift {k : Nat} {old new : List W} {p : W} {r : Fin 16} (proj : W → W)
    (hom : ∀ a b z, z ∈ basicOps a b → proj z ∈ basicOps (proj a) (proj b))
    (sign : proj goal = goal ∧ proj (~~~goal) = ~~~goal)
    (alone : ∀ w ∈ new, changes w r = true → w = p)
    (gone : proj p = 0)
    (incl : ∀ w ∈ new, proj w = 0 ∨ proj w ∈ old)
    (base : liftBound k old) : liftBound (k+1) new := by
  intro t ht h
  obtain ⟨u, sub, run⟩ := compress h
  have d : differs r t := ht.elim (fun e => e ▸ (goal_changes r).1) (fun e => e ▸ (goal_changes r).2)
  obtain ⟨w,hw,hd⟩ := live_separates (differs r) d (ops_differs r) run
  have mem (a : W) (ha : a ∈ u) := List.mem_toFinset.mp (sub ha)
  have e := alone w (mem w hw) (by simpa [changes, differs] using hd)
  have pt : proj t = t := ht.elim (fun e => e ▸ sign.1) (fun e => e ▸ sign.2)
  have nt : t ≠ 0 ∧ t ≠ ~~~0 := by rcases ht with rfl|rfl <;> decide +kernel
  have ne : p ≠ t := by intro h; exact nt.1 (pt ▸ (h ▸ gone))
  have sb := live_transport_save hom run (e ▸ hw) ne gone (av := old.toFinset) (by
    intro a ha
    rcases incl a (mem a ha) with h|h
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨_, List.mem_toFinset.mpr h, Or.inl rfl⟩))
  rw [pt] at sb
  change SignedBuild k old.toFinset t at sb
  rcases sb with h|h|h|h
  · exact nt.1 h
  · exact nt.2 h
  · exact base _ ht h
  · apply base _ _ h
    rcases ht with rfl|rfl
    · exact Or.inr rfl
    · exact Or.inl BitVec.not_not

def rowProj (i : Fin 32 → Fin 32) (w : W) : W :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 32 => w[(i k).val]))).cast List.length_ofFn

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowProj_bit (i : Fin 32 → Fin 32) (w : W) (j : ℕ) (hj : j < 32) :
    (rowProj i w)[j] = w[(i ⟨j, hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowProj, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

-- Restriction reads rows, so it commutes with the bitwise gate operations.
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowProj_not (i : Fin 32 → Fin 32) (u : W) : rowProj i (~~~u) = ~~~rowProj i u :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowProj_bit, BitVec.getElem_not]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowProj_ops (i : Fin 32 → Fin 32) (a b z : W) (hz : z ∈ basicOps a b) :
    rowProj i z ∈ basicOps (rowProj i a) (rowProj i b) := by
  have hand (u v : W) : rowProj i (u &&& v) = (rowProj i u &&& rowProj i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [rowProj_bit, BitVec.getElem_and]
  have hor (u v : W) : rowProj i (u ||| v) = (rowProj i u ||| rowProj i v) :=
    BitVec.eq_of_getElem_eq fun j hj => by simp only [rowProj_bit, BitVec.getElem_or]
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz ⊢
  rcases hz with rfl | rfl | rfl | rfl <;> simp [hand, hor, rowProj_not]


def vars6 : List W := [0x2c4b2082, 0x54954104, 0x99068208, 0xe2180410, 0x3e00820, 0x200000]
def proj6 := rowProj (fun i => if i = 21 then 31 else i)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem lb6 (k : Nat) (old : liftBound k cliqueInputs) : liftBound (k+1) vars6 := by
  apply stepLift (p := 0x200000) (r := 5) proj6 _ _ _ _ _ old
  · exact rowProj_ops _
  · decide +kernel
  · intro w hw
    simp only [vars6, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · decide +kernel
  · intro w hw
    simp only [vars6, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

def vars7 : List W := [0x244b2082, 0x54954104, 0x91068208, 0xe2180410, 0xbe00820, 0x200000, 0x8000000]
def proj7 := rowProj (fun i => if i = 27 then 17 else i)
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem lb7 (k : Nat) (old : liftBound k vars6) : liftBound (k+1) vars7 := by
  apply stepLift (p := 0x8000000) (r := 11) proj7 _ _ _ _ _ old
  · exact rowProj_ops _
  · decide +kernel
  · intro w hw
    simp only [vars7, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  · decide +kernel
  · intro w hw
    simp only [vars7, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

end PEqualNP.Outside.L_meta_10610.Signed

namespace PEqualNP.Outside.L_meta_10610.Witness
open PEqualNP.CircuitLowerBounds

def gates : List Gate := [
  ⟨.or,[1,2]⟩, ⟨.or,[0,7]⟩, ⟨.or,[8,4]⟩, ⟨.or,[3,5]⟩, ⟨.or,[1,6]⟩, ⟨.or,[5,6]⟩,
  ⟨.and,[0,2]⟩, ⟨.and,[8,4]⟩, ⟨.and,[9,12]⟩, ⟨.and,[10,11]⟩,
  ⟨.or,[13,14]⟩, ⟨.or,[15,16]⟩, ⟨.or,[17,18]⟩]

def edge (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem correct : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates,19⟩ (List.ofFn x) = edge x := by
  decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem basis : (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates.length = 13 := by simp [gates]
end PEqualNP.Outside.L_meta_10610.Witness

namespace PEqualNP.Outside.L_meta_10610.Signed
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_10610.Witness
def orig : List W := [0x244b2082, 0x200000, 0x54954104, 0x8000000, 0x91068208, 0xe2180410, 0xbe00820]

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem samevars : orig.toFinset = vars7.toFinset := by decide +kernel
def row (k : Fin 32) (i : Fin 7) : Bool := (orig.getD i.val 0)[k.val]
set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem rowSpec : ∀ k, edge (row k) = goal[k.val] := by decide +kernel

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem binaryLower (base : liftBound 9 cliqueInputs) (gs : List Gate) (o : Nat)
    (hg : ∀ g ∈ gs, legal g) (he : ∀ x, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = edge x) :
    12 ≤ binaryCost gs := by
  have init : ∀ u ∈ orig, holds orig.toFinset u := fun u hu => Or.inr (Or.inr ⟨u,List.mem_toFinset.mpr hu,Or.inl rfl⟩)
  have hr (k : Fin 32) : List.ofFn (row k) = orig.map (fun w => w[k.val]) := by
    apply List.ext_getElem (by rfl)
    intro i hi hj
    have hlt : i < orig.length := by simpa using hj
    simp only [row, List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hlt, Option.getD_some]
  obtain ⟨t,ht,run⟩ := compile gs o hg orig orig.toFinset init (by
    intro k
    change Circuit.eval ⟨gs,o⟩ (orig.map (fun w => w[k.val])) = goal[k.val]
    rw [← hr, he, rowSpec])
  by_contra! low
  have small : binaryCost gs ≤ 11 := by omega
  rw [samevars] at run
  have extend {a b : Nat} (h : a ≤ b) (r : build basicOps t a vars7.toFinset) : build basicOps t b vars7.toFinset := by
    induction h with
    | refl => exact r
    | step _ ih => exact Or.inl ih
  exact (lb7 _ (lb6 _ base)) _ ht (extend small run)

set_option maxRecDepth 40000 in
set_option maxHeartbeats 0 in
theorem conditional (base : liftBound 9 cliqueInputs) : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) := by
  intro gs o legalGs _ correct
  by_cases pres : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hg,hn⟩ := pres
    have cut : binaryCost gs < gs.length := List.length_filter_lt_length_iff_exists.mpr ⟨g,hg,by simp [isBinary,hn]⟩
    have cost := binaryLower base gs o legalGs correct
    exact ⟨gates,19,basis.1,by rw [basis.2]; omega, PEqualNP.Outside.L_meta_10610.Witness.correct⟩
  · exact ⟨gs,o,(fun g hg => ⟨(legalGs g hg).1.imp_right (·.resolve_right fun h => pres ⟨g,hg,h⟩), (legalGs g hg).2⟩), Nat.le_refl _, correct⟩
end PEqualNP.Outside.L_meta_10610.Signed

theorem PEqualNP.Outside.L_meta_10610 : (∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 7 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 4, 5, 0, 6, 1, 6, 2, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)) :=
  PEqualNP.Outside.L_meta_10610.Signed.conditional (PEqualNP.Outside.L_meta_10610.Signed.sample_lower PEqualNP.Outside.L_meta_10610.Cert.base)
