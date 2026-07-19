# MF-REP-001 — Faire apparaître deux coordonnées sans les supposer

## Idée

Un poset possède une représentation par deux coordonnées ordonnées exactement
quand il est l'intersection de deux ordres linéaires. Le nombre minimal d'ordres
nécessaires est la dimension de Dushnik–Miller. Cette définition est intrinsèque :
elle utilise seulement la relation du poset, sans coordonnées préexistantes.

MF-REP-001 énumère les extensions linéaires et cherche deux extensions dont
l'intersection redonne exactement la relation observée. Lorsqu'elles existent,
leurs positions fournissent les deux coordonnées ordinales recherchées.

## Pourquoi le rang six est nécessaire

L'audit énumère tous les posets rendus compatibles avec un étiquetage
topologique naturel jusqu'à cinq objets. Tout poset admet un tel étiquetage et
la dimension est invariante par renommage; cette énumération couvre donc tous
les types pertinents, avec répétitions possibles.

| Objets | Relations transitives examinées | Sans réalisation par deux ordres |
| ---: | ---: | ---: |
| 1 | 1 | 0 |
| 2 | 2 | 0 |
| 3 | 7 | 0 |
| 4 | 40 | 0 |
| 5 | 357 | 0 |

À six objets, le poset standard `S3` possède 48 extensions linéaires, mais
aucune paire ne le réalise. Sa dimension vaut 3. Le rang 4 de MF-PAT-003 ne
pouvait donc pas révéler si les deux coordonnées étaient réellement présentes :
tous les petits posets passaient automatiquement.

## Portée

L'absence de `S3` dans un échantillon n'est pas, à elle seule, une preuve
globale de dimension 2. Le prochain test doit mesurer la fréquence des motifs
de dimension supérieure à 2 à partir du rang 6, puis chercher une cohérence des
deux réalisateurs lorsque la taille augmente.

Le script est `scripts/audit_program_m_two_order_representation.py`; la sortie
est `outputs/program_m/mf_rep_001_two_order_representation.json`.
