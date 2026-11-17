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

**Terminologie, fixiert (Review-Punkt 2)**: Das Wort „Pauschale" schwankte in
früheren Kommentaren dieses Modells zwischen zwei Bedeutungen — ab jetzt
benennt das Modell nur noch die beiden Präzisionsbegriffe:
- **Konstant-Urteil** (formalisiert in `Konstant`/`Klassenfrei`, Ebene 1):
  `u a = u b` für alle `a b` — ein Urteil, das kein Individuum vom anderen
  unterscheidet.
- **Mengenurteil** (Ebene 2): die ∀-, ∃- und Mehrheit-Formen — ein Urteil
  ÜBER die ganze Menge, das sehr wohl zwischen Individuen trennt
  (`mehrheit_impliziert_nicht_instanz` beweist: Ein Mengenurteil ist kein
  Konstant-Urteil).
Das Wort „Pauschale" steht im Folgenden nur noch in wörtlichen Zitaten der
Debatte (Ricks Thesen, der Einwand der Gegenseite) und in Theorem-Namen, die
Vertragsbestand und unveränderlich sind; der Kommentar an jeder solchen
Stelle sagt, welcher Präzisionsbegriff gemeint ist.

**Ehrlichkeitsvertrag dieses Modells** (bindend):
- Kein Ergebnis wird behauptet, das nicht bewiesen ist. Nicht Beweisbares wird
  abgeschwächt, und die Schwächung wird als Kommentar dokumentiert.
- `sorry` ist verboten; der Build muss grün sein.
- Grenzen werden mit Prädikaten benannt, nicht als Mauer: Die Aussagen gelten
  *unter* den Prädikaten (endliches Ensemble, entscheidbares Urteil,
  keine Klassenzugehörigkeit) — die Prädikate stehen in den Typen.
- Der Preis des Konstant-Urteils (Informationsverlust über das Individuum)
  wird als bewiesenes Typ-Statement sichtbar gemacht, nicht wegerklärt.
- `#print axioms` am Dateiende weist für jedes Theorem die Axiom-Nutzung aus.
  Das Modell deklariert **keine eigenen Axiome**. Der Claim des Modells ist
  exakt so stark wie seine Beweise — nicht stärker.

**Aufbau**:
- *Rahmen*: Prädikate und Grundbegriffe (Umbenennung, Klassenfrei, Konstant,
  Endlich, Dressur/Bildung).
- *Ebene 1*: `pauschal_eindeutig` — wer nicht klassifiziert, kann nur konstant
  urteilen; und: für endliche Ensembles mit entscheidbarem Urteil sind die
  Mengenurteile (∀, ∃) machbar (entscheidbar).
- *Ebene 2*: `keine_lizenz_fuer_einzelurteil` — das Mengenurteil liziert
  kein Einzelurteil, außer es ist das absolut-richtige (∀-)Urteil.
- *Ebene 3*: Dressur (Basis, als Typ erzwungen: ein Konstant-Urteil) und
  Bildung (Basis + Instanz-Korrektur): die Korrektur spezialisiert die Basis,
  sie ersetzt sie nicht — und sie kostet: Wer korrigiert, klassifiziert.
- *Ebene 4*: die Merkmals-Achse (Review-Punkt 1) — `Objekt` = Kennung +
  Merkmal. Namens-Unabhängigkeit ist nicht Konstanz
  (`namens_unabhaengig_nicht_identisch_mit_konstant`), Merkmals-Klassen
  entstehen ohne Gruppen-Nennung (`merkmalsklassen_sind_klassenbildung`),
  und der Kernsatz aus Ebene 1 bleibt gültig, auf der anderen Achse
  (`pauschal_eindeutig_gilt_weiterhin`).
- *Bilanz*: `#eval` (Prüfen statt glauben) und `#print axioms` (Axiom-Nutzung).
-/

/-! ## Rahmen: Prädikate in Typen -/

/-- Eine Umbenennung ist eine Bijektion des Ensembles auf sich.
Ein Urteil, das „keine Klasse referenziert", darf von ihr nicht abhängen.
(Ebene 4 verfeinert das: Wessen Achse umbenannt wird — die Elemente als
Ganze oder nur ihre Namen — entscheidet, was „nicht abhängen" heißt.) -/
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
ist. Lesart auf nackten Elementen (ohne Merkmals-Achse, Ebenen 1–3): Es
referenziert nirgends die Zugehörigkeit einzelner Elemente zu einer
Teilmenge — wäre das Urteil an einer vorbestehenden Klasse festgemacht, gäbe
es eine Umbenennung, an der es bricht. (Ebene 4 trennt diese Lesart auf:
Sobald Elemente ein Merkmal tragen, gibt es unterscheidende Urteile, die
dennoch jeden Namen ignorieren — ihre Klassen entstehen am Merkmal.) -/
def Klassenfrei {α : Type} (u : α → Prop) : Prop :=
  ∀ (ρ : Umbenennung α) (x : α), u (ρ.vor x) = u x

/-- **Konstant**: das Konstant-Urteil — es unterscheidet keine Elemente.
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
   Kontraposition (`unterscheidung_braucht_klassenbildung`) sagt: Wer auf
   nackten Elementen unterscheidet, ist nicht klassenfrei. (Die frühere
   Lesart „wer unterscheidet, referenziert Klassenzugehörigkeit" war zu
   breit — Ebene 4 zeigt unterscheidende Urteile, die keine vorbestehende
   Gruppe referenzieren: Ihre Klassen entstehen am Merkmal.) Das deckt
   jeden erdenklichen Entscheider ab, statt seine Existenz zu leugnen.

Damit gilt Ricks „das einzig Machbare" genau unter den Prädikaten, und nur
unter ihnen (`klassenfrei_gilt_genau_wenn_pauschal`, `ueberAlle_entscheidbar`,
`ueberExistenz_entscheidbar`): endliches Ensemble, entscheidbares Urteil,
keine individuelle Verteilung. Die Prädikate stehen in den Typen — nicht
im Wortlaut. -/

/-- **Ebene 1, Kern**: Jedes klassenfreie Urteil ist ein Konstant-Urteil —
das Konstant-Urteil ist die einzige klassenfreie Urteilsform. (Der
Theorem-Name ist historisch und Vertragsbestand; seine „Pauschale" ist
hier das Konstant-Urteil.) -/
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
ist das Konstant-Urteil nicht nur machbar, sondern die *genaue*
Urteilsform. (Der Theorem-Name ist historisch und Vertragsbestand; seine
„Pauschale" ist hier das Konstant-Urteil.) -/
theorem klassenfrei_gilt_genau_wenn_pauschal {α : Type} [DecidableEq α]
    {u : α → Prop} : Klassenfrei u ↔ Konstant u :=
  ⟨pauschal_eindeutig, konstant_ist_klassenfrei⟩

/-- **Kontraposition**: Ein Urteil, das zwei Elemente unterscheidet, ist
nicht klassenfrei. Auf nackten Elementen ist jede Unterscheidung damit
zwangsläufig Klassenbildung. (Ob sie dabei eine *vorbestehende* Gruppe
referenzieren muss, entscheidet erst Ebene 4: nein — die Alarmregel bildet
ihre Klassen am Merkmal, ohne je einen Gruppennamen zu lesen.) -/
theorem unterscheidung_braucht_klassenbildung {α : Type} [DecidableEq α]
    {u : α → Prop} {a b : α} (h : u a ≠ u b) : ¬ Klassenfrei u := by
  intro hk
  have h1 : u ((vertausche a b).vor a) = u a := hk (vertausche a b) a
  have h2 : (vertausche a b).vor a = b := tausch_links a b
  rw [h2] at h1
  exact h h1.symm

/-- **Machbarkeit 1**: Über ein endliches Ensemble ist das Über-alle-Urteil
entscheidbar — konstruktiv, Element für Element, ohne klassische Axiome.
Das ist der „Machbar"-Kern der Mengenurteile. (Ein `def`, kein `theorem`:
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
widerlegt (es gibt gültige Mengenurteile — etwa das ∀-Urteil) — beides
beweisbar. -/

/-- Die EINZIG legitimierte Lizenz: nur das absolut-richtige Mengenurteil
(∀-Form, für alle Elemente bewiesen) gilt für ein konkretes Element. (Der
Theorem-Name ist historisch und Vertragsbestand; seine „Pauschale" ist hier
das Mengenurteil.) -/
theorem pauschale_liziert_wenn_absolut {α : Type} {u : α → Prop} {a : α}
    (h : ∀ x : α, u x) : u a := h a

/-- Der Universal-Einwand „Pauschalaussagen gelten nicht" ist als Totalität
widerlegt: Es gibt ein gültiges Mengenurteil (∀-Form, für jedes α, auch für
leere). (Der Theorem-Name ist historisch und Vertragsbestand; seine
„Pauschalen" sind hier Mengenurteile.) -/
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

Strukturvererbung analog OO: Die Basis (`Dressur`) ist das ererbte
Konstant-Urteil — seit dem Review-Typfix (Punkt 3) erzwingt der Typ es auch.
`Bildung` erweitert sie um das Korrekturfeld (`ausnahme`) — Bildung hat
Dressur als Basis und überschreibt sie fallweise. Die Instanz-Korrektur
respektiert Ebene 2: Weil das Konstant-Urteil über das Individuum nichts
sagt, entscheidet hier die Instanz selbst. -/

/-- **Dressur**: die ererbte Basis — ein Konstant-Urteil über das Ensemble.
Der Typ erzwingt jetzt, was der Kommentar früher nur versprach: Das Feld
`urteil_konstant` hält den Beweis, dass die Urteilsfunktion kein Individuum
vom anderen unterscheidet — „Dressur kennt kein Individuum" ist damit ein
Typ-Statement. (Wahl dokumentiert, Review-Punkt 3: Statt den Kommentar
zurückzunehmen, steht das Prädikat im Typ — so verlangt es der
Ehrlichkeitsvertrag dieses Modells: Zusagen und Grenzen stehen in den
Typen, nicht im Wortlaut.) -/
structure Dressur (α : Type) where
  urteil : α → Prop
  urteil_konstant : Konstant urteil

/-- Die Typ-Fixierung zahlt sich aus: Das Urteil jeder Dressur ist
klassenfrei — die ererbte Basis übersteht jede Umbenennung aus Ebene 1. -/
theorem dressur_urteil_ist_klassenfrei {α : Type} (p : Dressur α) :
    Klassenfrei p.urteil :=
  konstant_ist_klassenfrei p.urteil_konstant

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
Das Konstant-Urteil der Basis allein bestimmt die Instanz nicht — erst die
Instanz-Entscheidung (im Korrekturfeld) tut es. Genau deshalb ist die
Korrektur DATA, kein Theorem: Sie kann aus dem Basis-Urteil nicht abgeleitet
werden. Zeuge: Die Basis ist das Konstant-Urteil auf den Wert `u a` (der Typ
verlangt Konstanz); beide Korrekturen derselben Basis trennen die Instanz.
(Der Theorem-Name ist historisch und Vertragsbestand; seine „Pauschale" ist
hier das Basis-Urteil.) -/
theorem pauschale_bestimmt_nicht_die_instanz {α : Type} {u : α → Prop} {a : α}
    (hu : u a) :
    ∃ k₁ k₂ : Bildung α, k₁.toDressur = k₂.toDressur ∧ k₁.effektiv a ∧ ¬ k₂.effektiv a :=
  ⟨⟨⟨fun _ => u a, fun _ _ => rfl⟩, fun _ => False⟩,
    ⟨⟨fun _ => u a, fun _ _ => rfl⟩, fun _ => True⟩, rfl,
    ⟨hu, fun f => f⟩, fun heff => heff.2 True.intro⟩

/-- **Die Kosten der Korrektur**: Die Basis — nach Typ ein Konstant-Urteil,
also klassenfrei (`dressur_urteil_ist_klassenfrei`) — gewährt `b`, die
Ausnahme trifft `a`, verschont `b`: Schon ist das effektive Urteil nicht
mehr klassenfrei. Wer korrigiert, klassifiziert: Die Instanz-Korrektur ist
selbst eine Klassenbildung und kostet die Klassenfreiheit, die die Basis
aus Ebene 1 mitbringt. Der Preis wird hier bewiesen, nicht bestritten. -/
theorem korrektur_bricht_pauschalitaet {α : Type} [DecidableEq α]
    {k : Bildung α} {a b : α} (hb : k.urteil b) (ha : k.ausnahme a)
    (hnb : ¬ k.ausnahme b) :
    ¬ Klassenfrei (fun x => k.effektiv x) := by
  intro hk
  have heffb : k.effektiv b := ⟨hb, hnb⟩
  have hh : k.effektiv a = k.effektiv b := pauschal_eindeutig hk a b
  have heffa : k.effektiv a := by rw [hh]; exact heffb
  exact heffa.2 ha

/-! ## Ebene 4: Die Merkmals-Achse — Unterscheidung ohne Gruppen-Nennung

Ein externer Review hat ein Konstruktionsloch der Ebenen 1–3 benannt: Diese
urteilen über *nackte* Elemente — bloße Kennungen ohne Merkmal. Dort gilt zu
Recht: Wer unter JEDER Vertauschung invariant bleibt, kann nur konstant
urteilen (`pauschal_eindeutig`). Aber die Kommentare lasen sich so, als
könne eine Regel, die unterscheidet, das nur tun, weil sie eine
*vorbestehende Gruppe* referenziert. Das ist zu viel behauptet: Die Regel
„Alarm oberhalb von 80 °C" (1) fragt keine Kennung ab — sie ist
namens-unabhängig; (2) unterscheidet dennoch Elemente; (3) referenziert
keine vorbestehende Gruppe — die Klassen „Alarm" und „kein Alarm" ENTSTEHEN
im Ergebnis des Urteils, am Merkmal.

Ebenen 1–3 können diese Welt nicht ausdrücken, weil ihre Elemente kein
Merkmal tragen. Ihre Vertauschung bewegt das Element ALS GANZES: Wandert das
Merkmal mit, wandert das Urteil mit. Diese Ebene führt die zweite Achse ein
— Umbenennungen, die NUR die Namen schreiben, während das Merkmal dem Objekt
fest zugeordnet bleibt. Auf der Namen-Achse gilt die alte Identität nicht
mehr: Namens-Unabhängigkeit ist NICHT Konstanz
(`namens_unabhaengig_nicht_identisch_mit_konstant`), Merkmals-Klassen
entstehen ohne Gruppen-Nennung (`merkmalsklassen_sind_klassenbildung`), und
der Kernsatz aus Ebene 1 bleibt trotzdem richtig, weil seine Prämisse hier
schlicht nicht erfüllt ist (`alarm_nicht_invariant_unter_ganztausch`,
`pauschal_eindeutig_gilt_weiterhin`). Diese Ebene ist eine ERWEITERUNG, kein
Umbau: Die 20 Theoreme der Ebenen 1–3 stehen unverändert. -/

/-- Objekt = Kennung + Merkmal. Die Kennung ist der reine Name, das Merkmal
trägt die informationelle Last. Bewusst `Nat` statt `Real` (Review-Vorgabe):
Real-Beweise ziehen über `Classical` die Kernlogik-Axiome nach sich; `Nat`
hält jeden Beweis dieser Ebene konstruktiv und axiom-frei — ein skalarer
Messwert (Grad, Stück, Cent) trägt die Pointe vollständig. -/
structure Objekt where
  kennung : String
  merkmal : Nat
  deriving DecidableEq

/-- Umbenennung auf der NAMEN-Achse: σ schreibt nur das Namensfeld um, das
Merkmal bleibt dem Objekt fest zugeordnet. Das ist der entscheidende
Unterschied zur Vertauschung aus Ebene 1, die (Kennung, Merkmal) als Paar
bewegt: Hier wandert das Merkmal NICHT mit. -/
def umbenenne (σ : String → String) (x : Objekt) : Objekt where
  kennung := σ x.kennung
  merkmal := x.merkmal

/-- **Kennungsfrei**: das Pendant zu `Klassenfrei` auf der Namen-Achse —
gleiche Gestalt, andere Achse. `Klassenfrei` verlangt Invarianz unter
Umbenennungen des ELEMENTRAUMS, `Kennungsfrei` unter Umbenennungen des
NAMENSRAUMS. Ein Urteil, das die Kennung nie liest, ist kennungsfrei — der
Beweis unten nutzt nicht einmal, dass die Umbenennung bijektiv ist. -/
def Kennungsfrei (u : Objekt → Prop) : Prop :=
  ∀ (ρ : Umbenennung String) (x : Objekt), u (umbenenne ρ.vor x) = u x

/-- Die Alarmregel: Alarm genau oberhalb von 80 — sie liest das Merkmal und
nie die Kennung. -/
def alarmRegel : Objekt → Prop := fun x => x.merkmal > 80

/-- Zeuge heiß: Sensor-1, Messwert 90 — Alarm. -/
def heiss : Objekt := ⟨"Sensor-1", 90⟩

/-- Zeuge kalt: Sensor-2, Messwert 70 — kein Alarm. -/
def kalt : Objekt := ⟨"Sensor-2", 70⟩

/-- Zeuge gesunken: Sensor-1 nochmals, Messwert 70 — gleiche Kennung wie
`heiss`, anderes Merkmal. -/
def gesunken : Objekt := ⟨"Sensor-1", 70⟩

/-- **Achsen-Trennung, allgemein**: Jedes Urteil, das nur vom Merkmal abhängt
(u = f ∘ merkmal), ist kennungsfrei — unter jeder Umbenennung der Namen
bleibt es sich gleich. Der Beweis nutzt die Bijektivität nicht einmal: Die
Umbenennung schreibt nur an dem Feld, das ein Merkmal-Urteil nie liest. -/
theorem merkmalurteil_ist_kennungsfrei (f : Nat → Prop) :
    Kennungsfrei (fun x => f x.merkmal) :=
  fun _ _ => rfl

/-- **Ebene 4, Kern 1**: Namens-Unabhängigkeit ist NICHT identisch mit dem
Konstant-Urteil. Auf nackten Elementen fielen beide zusammen — Ebenen 1–3
konnten sie nicht trennen. Auf Objekten mit Merkmals-Achse fallen sie
auseinander: Die Alarmregel ist kennungsfrei und trotzdem kein
Konstant-Urteil. Genau der Sensor-Fall: Vertauscht man die Namen, bleibt
jedes Urteil stehen — die Urteile folgen den Merkmalen, nicht den Namen. -/
theorem namens_unabhaengig_nicht_identisch_mit_konstant :
    ¬ (∀ u : Objekt → Prop, Kennungsfrei u → Konstant u) := by
  intro h
  have hf : Kennungsfrei alarmRegel :=
    merkmalurteil_ist_kennungsfrei (fun n => n > 80)
  have heq : alarmRegel heiss = alarmRegel kalt := h alarmRegel hf heiss kalt
  have hh : alarmRegel heiss := by
    show heiss.merkmal > 80
    decide
  have hkein : ¬ alarmRegel kalt := by
    show ¬ (kalt.merkmal > 80)
    decide
  rw [heq] at hh
  exact hkein hh

/-- **Ebene 4, Kern 2**: Merkmals-Klassen sind Klassenbildung — ohne
Gruppen-Nennung. Erstens liest die Alarmregel die Kennung nie: Gleiches
Merkmal, gleiches Urteil, wie die Objekte auch heißen mögen (punktuell
stärker als Umbenennungs-Invarianz). Zweitens unterscheidet sie trotzdem,
und zwar schon bei identischer Kennung: derselbe Sensor, zwei Messungen,
zwei Urteile. Die Klassen „Alarm" und „kein Alarm" entstehen im Ergebnis
des Urteils, am Merkmal — kein vorbestehendes Gruppen-Label wird je
referenziert. Das ist die saubere Form von „Unterscheidung braucht
Merkmals-Referenz, keine Gruppen-Nennung". -/
theorem merkmalsklassen_sind_klassenbildung :
    (∀ x y : Objekt, x.merkmal = y.merkmal → alarmRegel x = alarmRegel y)
    ∧ ∃ x y : Objekt, x.kennung = y.kennung ∧ alarmRegel x ≠ alarmRegel y := by
  constructor
  · intro x y h
    exact congrArg (fun n => n > 80) h
  · refine ⟨heiss, gesunken, rfl, ?_⟩
    intro h
    have hh : alarmRegel heiss := by
      show heiss.merkmal > 80
      decide
    have hkein : ¬ alarmRegel gesunken := by
      show ¬ (gesunken.merkmal > 80)
      decide
    rw [h] at hh
    exact hkein hh

/-- **Der Unterschied der Achsen, bewiesen**: Die Alarmregel ist NICHT
klassenfrei im alten Sinn — Ebene 1s eigene Kontraposition
(`unterscheidung_braucht_klassenbildung`) trifft sie. Der Grund ist
mechanisch: Der Ganzttausch aus Ebene 1 vertauscht (Kennung, Merkmal) als
Paar, die Merkmale wandern mit, und mit ihnen die Urteile — vertauscht man
die heiße und die kalte Messung, steht am Platz der heißen die kalte, und
das Urteil am Platz kehrt sich um. Genau deshalb trifft `pauschal_eindeutig`
die Alarmregel nicht: Seine Prämisse ist hier schlicht nicht erfüllt. Der
scheinbare Widerspruch zu `namens_unabhaengig_nicht_identisch_mit_konstant`
löst sich auf: Die Sätze leben auf verschiedenen Vertauschungen. -/
theorem alarm_nicht_invariant_unter_ganztausch : ¬ Klassenfrei alarmRegel := by
  have hkein : ¬ alarmRegel kalt := by
    show ¬ (kalt.merkmal > 80)
    decide
  have hneu : alarmRegel heiss ≠ alarmRegel kalt := by
    intro h
    have hh : alarmRegel heiss := by
      show heiss.merkmal > 80
      decide
    rw [h] at hh
    exact hkein hh
  exact unterscheidung_braucht_klassenbildung hneu

/-- **Versöhnung**: Der Kernsatz aus Ebene 1 gilt weiterhin — jetzt beweisbar
auch auf dem neuen Typ `Objekt`. Kein Widerspruch zu
`namens_unabhaengig_nicht_identisch_mit_konstant`, denn die Sätze leben auf
verschiedenen Achsen: `pauschal_eindeutig` quantifiziert über
Vertauschungen, die das Objekt ALS GANZES bewegen — wer sie übersteht,
urteilt konstant; die Alarmregel übersteht sie nicht
(`alarm_nicht_invariant_unter_ganztausch`). Grenzfall-Lesart der Ebenen
1–3: Nackte Elemente tragen kein Merkmal, es gibt keine zweite Achse — der
Ganzttausch ist die einzige Vertauschung, deshalb ist dort Invarianz unter
ihm mit dem Konstant-Urteil gleichbedeutend
(`klassenfrei_gilt_genau_wenn_pauschal`). Erst wo Elemente mehr tragen als
den Namen, trennen sich die Achsen — ein Ensemble durchgehend gleichen
Merkmals wäre der Grenzfall, in dem Ganz- und Namenstausch darauf
zusammenfallen. -/
theorem pauschal_eindeutig_gilt_weiterhin {u : Objekt → Prop}
    (h : Klassenfrei u) : Konstant u :=
  pauschal_eindeutig h

/-! ## Bilanz: Prüfen statt glauben

Das Ensemble-Urteil über den Zeugen `Trio` wird hier tatsächlich berechnet
(drei Elemente, zwei erfüllen das Urteil):
- „Alle drei erfüllen es" — entscheidbar, Ergebnis: falsch.
- „Mindestens eines erfüllt es" — entscheidbar, Ergebnis: wahr.
Machbar sind die Mengenurteile also wirklich — das ist keine Redewendung. -/

#eval @decide (∀ x : Trio, trioUrteil x) (ueberAlle_entscheidbar trioEndlich trioInst)
#eval @decide (∃ x : Trio, trioUrteil x) (ueberExistenz_entscheidbar trioEndlich trioInst)

/-! ### Axiom-Bilanz jedes Theorems (Philosophie im Verhalten)

`#print axioms` für jedes Theorem dieses Modells. Das Modell deklariert
KEINE eigenen Axiome — und vermeidet darüber hinaus die Kernlogik-Axiome
von Lean (`propext`, `Quot.sound`, `Classical.choice`): Sogar die
Machbarkeits-Beweise, die Zeugen und die Ebene-4-Beweise (Alarmregel,
Sensor-Fall) kommen mit reiner konstruktiver Logik aus. Die erwartete
Ausgabe ist für ALLE Einträge „does not depend on any axioms"; falls ein
Beweis dennoch eines zieht, steht es hier schwarz auf weiß und wird im
Begleittext benannt. -/

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
#print axioms dressur_urteil_ist_klassenfrei
#print axioms korrektur_spezialisiert_nicht_ersetzt
#print axioms jede_dressur_hat_bildung
#print axioms zwang_am_absoluten_erzeugt_fehler
#print axioms totale_ausnahme_schafft_basis_ab
#print axioms pauschale_bestimmt_nicht_die_instanz
#print axioms korrektur_bricht_pauschalitaet
#print axioms merkmalurteil_ist_kennungsfrei
#print axioms namens_unabhaengig_nicht_identisch_mit_konstant
#print axioms merkmalsklassen_sind_klassenbildung
#print axioms alarm_nicht_invariant_unter_ganztausch
#print axioms pauschal_eindeutig_gilt_weiterhin
