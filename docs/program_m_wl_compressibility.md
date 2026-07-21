# MF-MAN-017 — Raffinement structurel de Weisfeiler–Leman

## Méthode

Le raffinement de couleurs 1-WL attribue d'abord la même couleur à tous les
objets, puis recolore chaque objet selon les multiensembles de couleurs de son
passé et de son futur. L'opération est répétée jusqu'à stabilisation.

Les deux orientations sont traitées comme une paire non ordonnée. Le profil
final des tailles de classes est donc exactement invariant sous renommage et
inversion globale des flèches.

WL est une heuristique classique d'isomorphisme qui encode itérativement les
voisinages
([Grohe et al.](https://arxiv.org/abs/2308.11970)). Il possède aussi des familles
de contre-exemples connues, notamment de type CFI ; il n'est pas complet.

## Calibration

Sur quatre cardinalités, 79 références Poisson calibrent le rang conforme
unilatéral `72/80`, puis 80 réalisations fraîches valident. Le seuil stable est
`2` partout et la couverture observée est 100 %, donc conservatrice.

À `N=256`, le gate rejette :

- les classes de 4 et 8 clones exacts ;
- les familles de 4 et 8 branches à deux niveaux.

Il généralise donc correctement MF-MAN-016 aux sous-structures symétriques de
plusieurs niveaux.

## Limite

Une petite classe WL mesure une absence de symétrie détectable, pas une absence
de description courte. Une construction peut individualiser chaque composant
tout en étant produite par une règle extrêmement simple. MF-ADV-004 exploite
exactement cette différence.

## Reproduction

```text
python scripts/audit_program_m_wl_compressibility.py \
  --output outputs/program_m/mf_man_017_wl_compressibility.json
```
