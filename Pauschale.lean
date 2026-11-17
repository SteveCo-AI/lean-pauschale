-- This module serves as the root of the `Pauschale` library.
-- Import modules here that should be built as part of the library.
import Pauschale.Basic

/-!
# Pauschalisierung als unabdingbares Urteil über Mengen

Formalisierung der Debatte um Pauschalurteile — als ehrliches Lean-4-Modell.

**Ricks Thesen** (Systementwickler, SlotDB):
1. „Wenn etwas absolut richtig ist, dann bedarf es keiner Zwangs-Korrektur."
2. „Pauschalisierung ist das einzig Machbare bei Urteilen über Mengen."

**Der Einwand der Gegenseite**: „Pauschalaussagen gelten nicht."

**Ehrlichkeitsvertrag dieses Modells** (bindend):
- Kein Ergebnis wird behauptet, das nicht bewiesen ist. Nicht Beweisbares wird
  abgeschwächt, und die Schwächung wird als Kommentar dokumentiert.
- `sorry` ist verboten; der Build muss grün sein.
- Grenzen werden mit Prädikaten benannt, nicht als Mauer: Die Aussagen gelten
  *unter* den Prädikaten (endliches Ensemble, entscheidbares Urteil,
  keine Klassenzugehörigkeit) — die Prädikate stehen in den Typen.
- Der Preis der Pauschalisierung (Informationsverlust über das Individuum)
  wird als bewiesenes Typ-Statement sichtbar gemacht, nicht wegerklärt.
- `#print axioms` am Dateiende weist für jedes Theorem die Axiom-Nutzung aus.
  Das Modell deklariert **keine eigenen Axiome**. Der Claim des Modells ist
  exakt so stark wie seine Beweise — nicht stärker.

**Aufbau**:
- *Rahmen*: Prädikate und Grundbegriffe (Umbenennung, Klassenfrei, Konstant,
  Endlich, Dressur/Bildung).
- *Ebene 1*: `pauschal_eindeutig` — wer nicht klassifiziert, kann nur pauschal
  urteilen; und: für endliche Ensembles mit entscheidbarem Urteil ist das
  Pauschal-Urteil machbar (entscheidbar).
- *Ebene 2*: `keine_lizenz_fuer_einzelurteil` — das Ensemble-Urteil liziert
  kein Einzelurteil, außer es ist das absolut-richtige (∀-)Urteil.
- *Ebene 3*: Dressur (Basis) und Bildung (Basis + Instanz-Korrektur): die
  Korrektur spezialisiert die Basis, sie ersetzt sie nicht — und sie kostet:
  Wer korrigiert, klassifiziert.
- *Bilanz*: `#eval` (Prüfen statt glauben) und `#print axioms` (Axiom-Nutzung).
-/

/-! ## Rahmen: Prädikate in Typen -/

/-- Eine Umbenennung ist eine Bijektion des Ensembles auf sich.
Ein Urteil, das „keine Klasse referenziert", darf von ihr nicht abhängen. -/
structure Umbenennung (α : Type) where
  vor : α → α
  zurueck : α → α
  hin : ∀ x : α, zurueck (vor x) = x
  her : ∀ x : α, vor (zurueck x) = x

/-- Die Vertauschung zweier Elemente: der Test, ob ein Urteil
Klassen bildet. -/
def tausch [DecidableEq α] (a b x : α) : α :=
  if x = a then b else if x = b then a else x

theorem tausch_links [DecidableEq α] (a b : α) : tausch a b a = b :=
  ite_eq_left rfl

theorem tausch_rechts [DecidableEq α] (a b : α) : tausch a b b = a := by
  by_cases hba : b = a
  · rw [hba]
    exact ite_eq_left rfl
  · exact (ite_eq_right hba).trans (ite_eq_left rfl)

theorem tausch_invol [DecidableEq α] (a b x : α) :
    tausch a b (tausch a b x) = x := by
  by_cases hxa : x = a
  · rw [hxa, tausch_links a b, tausch_rechts a b]
  · by_cases hxb : x = b
    · rw [hxb, tausch_rechts a b, tausch_links a b]
    · have hx : tausch a b x = x := (ite_eq_right hxa).trans (ite_eq_right hxb)
      rw [hx, hx]

/-- Die Vertauschung als Umbenennung (sie ist ihre eigene Umkehrung). -/
def vertausche [DecidableEq α] (a b : α) : Umbenennung α where
  vor x := tausch a b x
  zurueck x := tausch a b x
  hin x := tausch_invol a b x
  her x := tausch_invol a b x

/-- **Klassenfrei**: ein Urteil über α, das unter jeder Umbenennung invariant
ist. Es referenziert nirgends die Zugehörigkeit einzelner Elemente zu einer
Teilmenge — wäre das Urteil an einer Klasse festgemacht, gäbe es eine
Umbenennung, an der es bricht. -/
def Klassenfrei {α : Type} (u : α → Prop) : Prop :=
  ∀ (ρ : Umbenennung α) (x : α), u (ρ.vor x) = u x

/-- **Konstant**: das Urteil unterscheidet keine Elemente — die pauschale Form.
Die Urteilswerte sind als Gleichheit von Propositionen pointweise gleich. -/
def Konstant {α : Type} (u : α → Prop) : Prop :=
  ∀ a b : α, u a = u b

/-- Doppelte Erfassung ausgeschlossen (eigenes Prädikat, keine
Bibliotheksabhängigkeit): die Erfassung zählt Elemente, nicht Nennungen. -/
inductive OhneDoppel {α : Type} : List α → Prop where
  | nil : OhneDoppel []
  | kons {a : α} {l : List α} (h : ∀ x : α, x ∈ l → a ≠ x) (t : OhneDoppel l) :
      OhneDoppel (a :: l)

/-- **Endlich**: das Prädikat „endliches Ensemble" — gegeben durch eine
Erfassung (Volkszählung), die jedes Element erreicht und keines doppelt
zählt. -/
structure Endlich (α : Type) where
  erfassung : List α
  erfasst : ∀ x : α, x ∈ erfassung
  ohne_doppel : OhneDoppel erfassung

/-- Listen-Helfer: Wer in `b :: l` liegt, ist `b` oder liegt in `l` — als
Widerspruchs-Schema, konstruktiv und axiom-frei. (Die Core-Lemmas um
`List.all_eq_true` ziehen `propext` und `Quot.sound`; dieses Modell
vermeidet sie bewusst — die Prädikate genügen.) -/
private theorem mem_head_tail {α : Type} {x b : α} {l : List α}
    (h : x ∈ b :: l) (hne : ¬(x = b)) (hrest : x ∈ l → False) : False := by
  cases h with
  | head _ => exact hne rfl
  | tail _ h' => exact hrest h'

/-! ## Ebene 1: Das Ensemble-Urteil

Die ursprüngliche Aufgaben-Formulierung lautete: „Es existiert keine
entscheidbare Funktion `decide : (α : Type) → α → Prop → Bool`, die für alle
Elemente eines endlichen Ensembles ohne Klassenbildung ein
Unterscheidungs-Urteil fällen kann, ohne die Klassenzugehörigkeit zu
referenzieren."

**Ehrliche Abschwächung — die wörtliche Aussage ist nicht beweisbar:**

1. *Klassisch falsch*: `Classical.propDecidable` (gestützt auf das
   Axiom `Classical.choice`) liefert sehr wohl einen Entscheider für jede
   Proposition — nur eben nicht berechenbar, ohne jede Berechnungsregel:
   eine Papierlizenz. „Es existiert keiner" gilt also nur konstruktiv.
2. *Konstruktiv nicht formalisierbar*: „es gibt keinen Algorithmus, der …"
   ist eine meta-mathematische Aussage über Berechenbarkeit; sie zu beweisen
   würde eine Formalisierung von Berechenbarkeit erfordern — hier nicht
   Gegenstand.
3. *Stärker und beweisbar*: `pauschal_eindeutig` unten quantifiziert über
   JEDE Urteilsfunktion `u : α → Prop` — egal ob berechenbar, klassisch oder
   noch so mächtig: jede klassenfreie Funktion ist konstant, und die
   Kontraposition (`unterscheidung_braucht_klassenbildung`) sagt: wer
   unterscheidet, referenziert Klassenzugehörigkeit. Das deckt jeden
   erdenklichen Entscheider ab, statt seine Existenz zu leugnen.

Damit gilt Ricks „das einzig Machbare" genau unter den Prädikaten, und nur
unter ihnen (`klassenfrei_gilt_genau_wenn_pauschal`, `ueberAlle_entscheidbar`,
`ueberExistenz_entscheidbar`): endliches Ensemble, entscheidbares Urteil,
keine individuelle Verteilung. Die Prädikate stehen in den Typen — nicht
im Wortlaut. -/

/-- **Ebene 1, Kern**: Jedes klassenfreie Urteil ist konstant — die
Pauschale ist die einzige klassenfreie Urteilsform. -/
theorem pauschal_eindeutig {α : Type} [DecidableEq α] {u : α → Prop}
    (h : Klassenfrei u) : Konstant u := by
  intro a b
  have h1 : u ((vertausche a b).vor a) = u a := h (vertausche a b) a
  have h2 : (vertausche a b).vor a = b := tausch_links a b
  rw [h2] at h1
  exact h1.symm

/-- Konstante Urteile sind klassenfrei — die Umkehrung. -/
theorem konstant_ist_klassenfrei {α : Type} {u : α → Prop}
    (h : Konstant u) : Klassenfrei u :=
  fun ρ x => h (ρ.vor x) x

/-- „Das einzig Machbare" — ehrlich: unter dem Prädikat der Klassenfreiheit
ist die Pauschale nicht nur machbar, sondern die *genaue* Urteilsform. -/
theorem klassenfrei_gilt_genau_wenn_pauschal {α : Type} [DecidableEq α]
    {u : α → Prop} : Klassenfrei u ↔ Konstant u :=
  ⟨pauschal_eindeutig, konstant_ist_klassenfrei⟩

/-- **Kontraposition**: Ein Urteil, das zwei Elemente unterscheidet,
referenziert Klassenzugehörigkeit — Unterscheidung *ist* Klassenbildung. -/
theorem unterscheidung_braucht_klassenbildung {α : Type} [DecidableEq α]
    {u : α → Prop} {a b : α} (h : u a ≠ u b) : ¬ Klassenfrei u := by
  intro hk
  have h1 : u ((vertausche a b).vor a) = u a := hk (vertausche a b) a
  have h2 : (vertausche a b).vor a = b := tausch_links a b
  rw [h2] at h1
  exact h h1.symm

/-- **Machbarkeit 1**: Über ein endliches Ensemble ist das Über-alle-Urteil
entscheidbar — konstruktiv, Element für Element, ohne klassische Axiome.
Das ist der „Machbar"-Kern der Pauschalisierung. (Ein `def`, kein `theorem`:
der Wert IST die Entscheidung.) -/
private def alleInListe {α : Type} {u : α → Prop} (inst : ∀ x : α, Decidable (u x)) :
    (l : List α) → Decidable (∀ x : α, x ∈ l → u x)
  | [] => isTrue (fun x hx => nomatch hx)
  | a :: l =>
      match alleInListe inst l with
      | isTrue h =>
          match inst a with
          | isTrue ha => isTrue (fun x hx => by
              cases hx with
              | head _ => exact ha
              | tail _ hxl => exact h x hxl)
          | isFalse ha => isFalse (fun k => ha (k a (List.Mem.head l)))
      | isFalse h => isFalse (fun k => h (fun x hx => k x (List.Mem.tail a hx)))

def ueberAlle_entscheidbar {α : Type} (E : Endlich α) {u : α → Prop}
    (inst : ∀ x : α, Decidable (u x)) : Decidable (∀ x : α, u x) :=
  match alleInListe inst E.erfassung with
  | isTrue h => isTrue (fun x => h x (E.erfasst x))
  | isFalse h => isFalse (fun k => h (fun x _hx => k x))

/-- **Machbarkeit 2**: Dasselbe für das Mindestens-ein-Urteil. -/
private def mindestensEinsInListe {α : Type} {u : α → Prop}
    (inst : ∀ x : α, Decidable (u x)) :
    (l : List α) → Decidable (∃ x : α, x ∈ l ∧ u x)
  | [] => isFalse (fun hex => Exists.elim hex (fun x hx => nomatch hx.1))
  | a :: l =>
      match inst a with
      | isTrue ha => isTrue ⟨a, List.Mem.head l, ha⟩
      | isFalse ha =>
          match mindestensEinsInListe inst l with
          | isTrue h => isTrue (Exists.elim h (fun x hx => ⟨x, List.Mem.tail a hx.1, hx.2⟩))
          | isFalse h => isFalse (fun hex => by
              obtain ⟨x, hx1, hx2⟩ := hex
              cases hx1 with
              | head _ => exact ha hx2
              | tail _ hxl => exact h ⟨x, hxl, hx2⟩)

def ueberExistenz_entscheidbar {α : Type} (E : Endlich α) {u : α → Prop}
    (inst : ∀ x : α, Decidable (u x)) : Decidable (∃ x : α, u x) :=
  match mindestensEinsInListe inst E.erfassung with
  | isTrue h => isTrue (Exists.elim h (fun x hx => ⟨x, hx.2⟩))
  | isFalse h => isFalse (fun hex => h (Exists.elim hex (fun x hx => ⟨x, E.erfasst x, hx⟩)))

/-- **Der Preis, als Typ-Statement**: Ein klassenfreies Urteil unterscheidet
zwei Elemente nicht — selbst wenn sie verschieden sind. Der
Informationsverlust über das Individuum ist real und hier bewiesen, nicht
wegdiskutiert. -/
theorem informationsverlust {α : Type} [DecidableEq α] {u : α → Prop}
    (h : Klassenfrei u) (a b : α) (hne : a ≠ b) : u a = u b ∧ a ≠ b :=
  ⟨pauschal_eindeutig h a b, hne⟩

/-! ## Ebene 2: Keine Lizenz für Einzelurteile

Das Ensemble-Urteil liziert ein Einzelurteil genau dann, wenn es das
absolut-richtige (∀-)Urteil ist. Alles Schwächere — Existenz, Durchschnitt,
Mehrheit — liziert nichts. Damit hat der Einwand „Pauschalaussagen gelten
nicht" einen wahren Kern (keine Instanz-Lizenz), ist als Totalität aber
widerlegt (es gibt gültige Pauschalen) — beides beweisbar. -/

/-- Die EINZE legitimierte Lizenz: nur das absolut-richtige Urteil (für alle
Elemente bewiesen) gilt für ein konkretes Element. -/
theorem pauschale_liziert_wenn_absolut {α : Type} {u : α → Prop} {a : α}
    (h : ∀ x : α, u x) : u a := h a

/-- Der Universal-Einwand „Pauschalaussagen gelten nicht" ist als Totalität
widerlegt: Es gibt eine gültige Pauschale (für jedes α, auch für leere). -/
theorem es_gibt_gueltige_pauschalen {α : Type} :
    ∃ u : α → Prop, ∀ x : α, u x :=
  ⟨fun _ => True, fun _ => True.intro⟩

/-- **Ebene 2, Kern**: Aus „irgendein Element erfüllt u" folgt NICHT „dieses
Element erfüllt u". Beweis durch Zeugen: über Bool erfüllt `true` das
Urteil `= true`, `false` aber nicht. -/
theorem keine_lizenz_fuer_einzelurteil :
    ¬ (∀ (α : Type) (u : α → Prop), (∃ x : α, u x) → ∀ (a : α), u a) := by
  intro h
  have h' : false = true := h Bool (fun x => x = true) ⟨true, rfl⟩ false
  exact Bool.noConfusion h'

/-- **Durchschnitts-Variante**: „Mehrheit" — mehr als die Hälfte der Erfassung
erfüllt u. Auch das liziert kein Einzelurteil. -/
def Mehrheit {α : Type} (E : Endlich α) (u : α → Prop)
    (inst : ∀ x : α, Decidable (u x)) : Prop :=
  2 * List.countP (fun x => @decide (u x) (inst x)) E.erfassung
    > E.erfassung.length

/-- Zeugensystem: drei Elemente, zwei erfüllen das Urteil. Die Feldbeweise
sind ausdrückliche Konstruktor-Zeugen (kein `simp`): `simp` zieht `propext`,
und die Axiom-Bilanz des Modells soll sauber bleiben. -/
inductive Trio where
  | eins : Trio
  | zwei : Trio
  | drei : Trio

def trioUrteil : Trio → Prop
  | Trio.eins => True
  | Trio.zwei => True
  | Trio.drei => False

def trioInst : (x : Trio) → Decidable (trioUrteil x)
  | Trio.eins => isTrue True.intro
  | Trio.zwei => isTrue True.intro
  | Trio.drei => isFalse (fun h => h)

def trioEndlich : Endlich Trio where
  erfassung := [Trio.eins, Trio.zwei, Trio.drei]
  erfasst := fun x => by
    cases x with
    | eins => exact List.Mem.head _
    | zwei => exact List.Mem.tail _ (List.Mem.head _)
    | drei => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
  ohne_doppel := OhneDoppel.kons (fun x hx => by
      cases x with
      | eins => exact (mem_head_tail hx (fun h => nomatch h) (fun h' =>
          mem_head_tail h' (fun h => nomatch h) (fun h'' => nomatch h''))).elim
      | zwei => exact fun h => nomatch h
      | drei => exact fun h => nomatch h)
    (OhneDoppel.kons (fun x hx => by
      cases x with
      | eins => exact (mem_head_tail hx (fun h => nomatch h) (fun h' => nomatch h')).elim
      | zwei => exact (mem_head_tail hx (fun h => nomatch h) (fun h' => nomatch h')).elim
      | drei => exact fun h => nomatch h)
    (OhneDoppel.kons (fun x hx => nomatch hx) OhneDoppel.nil))

/-- **Ebene 2, Durchschnitt**: Eine 2-von-3-Mehrheit gilt — und `drei`
erfüllt das Urteil dennoch nicht. Mehrheit ist kein Einzelurteil. -/
theorem mehrheit_impliziert_nicht_instanz :
    ¬ (∀ (α : Type) (E : Endlich α) (u : α → Prop) (inst : ∀ x : α, Decidable (u x)),
        Mehrheit E u inst → ∀ (a : α), u a) := by
  intro h
  have hmehr : Mehrheit trioEndlich trioUrteil trioInst := by
    show 2 * List.countP
        (fun x => @decide (trioUrteil x) (trioInst x)) [Trio.eins, Trio.zwei, Trio.drei] > 3
    decide
  have h' : trioUrteil Trio.drei :=
    h Trio trioEndlich trioUrteil trioInst hmehr Trio.drei
  exact h'

/-! ## Ebene 3: Korrektur — Dressur als Basis, Bildung als Überschreibung

Strukturvererbung analog OO: Die Basis (`Dressur`) ist die ererbte
Standard-Pauschale. `Bildung` erweitert sie um das Korrekturfeld
(`ausnahme`) — Bildung hat Dressur als Basis und überschreibt sie
fallweise. Die Instanz-Korrektur respektiert Ebene 2: Weil die Pauschale
über das Individuum nichts sagt, entscheidet hier die Instanz selbst. -/

/-- **Dressur**: die ererbte Standard-Pauschale — ein Urteil über das
Ensemble, das kein Individuum kennt. -/
structure Dressur (α : Type) where
  urteil : α → Prop

/-- **Bildung**: Dressur als Basis, plus Instanz-Korrektur (Überschreibung).
Das Korrekturfeld ist elementindiziert — es entscheidet einzelne Fälle. -/
structure Bildung (α : Type) extends Dressur α where
  ausnahme : α → Prop

/-- Das effektive Urteil nach Korrektur: die Basis, ausgenommen wo die
Instanz widerspricht. -/
def Bildung.effektiv {α : Type} (k : Bildung α) (a : α) : Prop :=
  k.urteil a ∧ ¬ k.ausnahme a

/-- Korrektur ersetzt die Basis nicht — sie spezialisiert sie: Das
effektive Urteil bleibt ein Urteil der Basis. -/
theorem korrektur_spezialisiert_nicht_ersetzt {α : Type} {k : Bildung α}
    {a : α} (h : k.effektiv a) : k.urteil a := h.1

/-- Jede Dressur trägt eine Bildung: die leere Korrektur (keine Ausnahme)
liefert die Basis unverändert zurück. Bildung hat Dressur als Basis —
ohne Basis gäbe es nichts zu überschreiben. -/
theorem jede_dressur_hat_bildung {α : Type} (p : Dressur α) :
    ∃ k : Bildung α, k.toDressur = p ∧ ∀ a : α, (k.effektiv a ↔ p.urteil a) := by
  refine ⟨⟨p, fun _ => False⟩, rfl, fun a => ⟨fun h => h.1, fun h => ⟨h, fun f => f⟩⟩⟩

/-- **Ricks Satz, operatorisch**: Was absolut richtig ist, bedarf keiner
Zwangs-Korrektur — schärfer: eine erzwungene Ausnahme am absolut Richtigen
kann nur Fehler erzeugen. Die Konklusion führt beides vor: die Basis hatte
bei `a` recht, UND das korrigierte Urteil leugnet es — die Zwangs-Korrektur
hat eine wahre Aussage in eine falsche verwandelt. -/
theorem zwang_am_absoluten_erzeugt_fehler {α : Type} {k : Bildung α} {a : α}
    (h : ∀ x : α, k.urteil x) (ha : k.ausnahme a) :
    k.urteil a ∧ ¬ k.effektiv a :=
  ⟨h a, fun heff => heff.2 ha⟩

/-- Die radikale Gegenseite, operatorisch: „Pauschalaussagen gelten nicht"
— als überall erzwungene Korrektur umgesetzt — schafft die Basis komplett ab.
Eine totale Ausnahme ist keine Korrektur mehr, sondern Abschaffung. -/
theorem totale_ausnahme_schafft_basis_ab {α : Type} {k : Bildung α}
    (h : ∀ x : α, k.ausnahme x) (a : α) : ¬ k.effektiv a :=
  fun heff => heff.2 (h a)

/-- Ebene 2 in Ebene 3: Dieselbe Basis, entgegengesetzte Instanz-Ergebnisse.
Die Pauschale allein bestimmt die Instanz nicht — erst die Instanz-Entscheidung
(im Korrekturfeld) tut es. Genau deshalb ist die Korrektur DATA, kein Theorem:
Sie kann aus dem Ensemble-Urteil nicht abgeleitet werden. -/
theorem pauschale_bestimmt_nicht_die_instanz {α : Type} {u : α → Prop} {a : α}
    (hu : u a) :
    ∃ k₁ k₂ : Bildung α, k₁.toDressur = k₂.toDressur ∧ k₁.effektiv a ∧ ¬ k₂.effektiv a :=
  ⟨⟨⟨u⟩, fun _ => False⟩, ⟨⟨u⟩, fun _ => True⟩, rfl,
    ⟨hu, fun f => f⟩, fun heff => heff.2 True.intro⟩

/-- **Die Kosten der Korrektur**: Die Basis gewährt `b`, die Ausnahme trifft
`a`, verschont `b` — schon ist das effektive Urteil nicht mehr klassenfrei.
Wer korrigiert, klassifiziert: Die Instanz-Korrektur ist selbst eine
Klassenbildung und kostet die Pauschalität aus Ebene 1. Der Preis wird
hier bewiesen, nicht bestritten. -/
theorem korrektur_bricht_pauschalitaet {α : Type} [DecidableEq α]
    {k : Bildung α} {a b : α} (hb : k.urteil b) (ha : k.ausnahme a)
    (hnb : ¬ k.ausnahme b) :
    ¬ Klassenfrei (fun x => k.effektiv x) := by
  intro hk
  have heffb : k.effektiv b := ⟨hb, hnb⟩
  have hh : k.effektiv a = k.effektiv b := pauschal_eindeutig hk a b
  have heffa : k.effektiv a := by rw [hh]; exact heffb
  exact heffa.2 ha

/-! ## Bilanz: Prüfen statt glauben

Das Ensemble-Urteil über den Zeugen `Trio` wird hier tatsächlich berechnet
(drei Elemente, zwei erfüllen das Urteil):
- „Alle drei erfüllen es" — entscheidbar, Ergebnis: falsch.
- „Mindestens eines erfüllt es" — entscheidbar, Ergebnis: wahr.
Machbar ist das Pauschal-Urteil also wirklich — das ist keine Redewendung. -/

#eval @decide (∀ x : Trio, trioUrteil x) (ueberAlle_entscheidbar trioEndlich trioInst)
#eval @decide (∃ x : Trio, trioUrteil x) (ueberExistenz_entscheidbar trioEndlich trioInst)

/-! ### Axiom-Bilanz jedes Theorems (Philosophie im Verhalten)

`#print axioms` für jedes Theorem dieses Modells. Das Modell deklariert
KEINE eigenen Axiome — und vermeidet darüber hinaus die Kernlogik-Axiome
von Lean (`propext`, `Quot.sound`, `Classical.choice`): Sogar die
Machbarkeits-Beweise und die Zeugen kommen mit reiner konstruktiver Logik
aus. Die erwartete Ausgabe ist für ALLE Einträge „does not depend on any
axioms"; falls ein Beweis dennoch eines zieht, steht es hier schwarz auf
weiß und wird im Begleittext benannt. -/

#print axioms tausch_links
#print axioms tausch_rechts
#print axioms tausch_invol
#print axioms pauschal_eindeutig
#print axioms konstant_ist_klassenfrei
#print axioms klassenfrei_gilt_genau_wenn_pauschal
#print axioms unterscheidung_braucht_klassenbildung
#print axioms ueberAlle_entscheidbar
#print axioms ueberExistenz_entscheidbar
#print axioms informationsverlust
#print axioms pauschale_liziert_wenn_absolut
#print axioms es_gibt_gueltige_pauschalen
#print axioms keine_lizenz_fuer_einzelurteil
#print axioms mehrheit_impliziert_nicht_instanz
#print axioms korrektur_spezialisiert_nicht_ersetzt
#print axioms jede_dressur_hat_bildung
#print axioms zwang_am_absoluten_erzeugt_fehler
#print axioms totale_ausnahme_schafft_basis_ab
#print axioms pauschale_bestimmt_nicht_die_instanz
#print axioms korrektur_bricht_pauschalitaet
