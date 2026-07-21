# MF-CERT-002 — Audit des hypothèses du certificat exact

MF-CERT-001 est un bon test fini, mais il ne constitue pas encore une preuve
exacte de Minkowski. MF-CERT-002 sépare les résultats acquis des ponts encore
manquants.

## Chaîne auditée

| Étape | État |
| --- | --- |
| Loi de posets échangeable et projective | interface formelle et théorie publiée |
| Tous les sous-posets finis ont dimension ≤ 2 | prémisse universelle ouverte |
| Compacité vers deux ordres globaux | théorème publié, pas encore formalisé |
| Lift aléatoire échangeable des deux ordres | dérivé conditionnellement par MF-REP-004 |
| Représentation continue sans atomes par un permuton | conséquence de la paire d'ordres échangeable |
| Égalité exacte de la loi au rang 4 | seulement preuves statistiques finies |
| Rang 4 force le permuton uniforme | théorème publié + MF-PAT-003 |
| Reconstruction d'une métrique | pas encore obtenue ici |

MF-REP-004 résout le problème du choix sans imposer une règle déterministe : un
lift aléatoire est construit par sélection borélienne, moyennage sur les groupes
finis et compacité. Dans le cas ergodique, un lift extrémal donne un permuton
déterministe. L'hypothèse encore ouverte en amont est que tous les sous-posets
finis aient effectivement dimension au plus 2.

Janson représente toute loi de posets échangeable par un noyau de posets
([arXiv:0902.0306](https://arxiv.org/abs/0902.0306)), tandis que la théorie des
permutons représente les limites de permutations. MF-REP-004 donne le pont
conditionnel entre ces cadres.

Lean enregistre donc le résultat de forçage comme un paramètre explicite
`ExactMinkowskiBridge`, avec quatre prémisses exactes. Une observation
`FiniteCertificateObservation` ne produit aucune de ces prémisses.

Le script est `scripts/audit_program_m_exact_certificate_hypotheses.py`; la
sortie est `outputs/program_m/mf_cert_002_exact_hypotheses.json`.
