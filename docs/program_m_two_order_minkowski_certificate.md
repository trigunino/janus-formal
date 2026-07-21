# MF-CERT-001 — Certificat combiné vers Minkowski 1+1

## Pourquoi combiner

La reconstruction de deux ordres ne suffit pas : MF-ADV-009 possède réellement
deux ordres mais leur loi n'est pas uniforme. Inversement, un accord statistique
à petit rang ne doit pas introduire secrètement une représentation globale.

MF-CERT-001 exige donc simultanément :

1. une paire d'ordres reconstruite intrinsèquement sur dix objets ;
2. l'accord de la distribution complète des 16 posets de rang 4 avec Minkowski.

Le second seuil (`0.0244954`) est repris sans modification de la calibration
Minkowski indépendante de MF-ADV-009. Chaque validation utilise 8192 motifs et
32 nouvelles graines.

## Résultats

| Modèle | Deux ordres | Rang 4 | Combiné |
| --- | ---: | ---: | ---: |
| Minkowski 1+1 | 32/32 | 32/32 | 32/32 |
| MF-ADV-009 | 32/32 | 0/32 | 0/32 |
| MF-ADV-008 | 32/32 | 0/32 | 0/32 |
| Ordre produit 3D | 25/32 | 0/32 | 0/32 |

## Chaîne mathématique exacte visée

Si tous les sous-posets finis ont dimension au plus 2, la compacité fournit deux
ordres globaux. Sous échangeabilité et continuité, ils donnent un permuton. Si sa
loi des posets de rang 4 égale exactement celle de Minkowski, MF-PAT-003 fournit
une somme `Σ-forcing`; le théorème publié force alors le permuton uniforme.

L'expérience finie ne prouve pas les prémisses universelles « tous les
sous-posets » et « égalité exacte ». Elle fournit un certificat statistique
réfutable, pas une preuve achevée de l'émergence géométrique.

Le script est `scripts/audit_program_m_two_order_minkowski_certificate.py`; la
sortie est `outputs/program_m/mf_cert_001_two_order_minkowski.json`.
