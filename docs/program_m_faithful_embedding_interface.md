# MF-MAN-001 — Interface de plongement fidèle

## Résultat

`FaithfulEmbeddingSpecification` rend explicites les données minimales d'un
candidat : injection préservant et reflétant l'ordre, régions et volumes,
densité et tolérances, fenêtre d'échelles, hypothèse d'échantillonnage et borne
de probabilité d'échec. La loi nombre-volume est conditionnelle à cette
hypothèse. Un `FaithfulEmbeddingCertificate` exige une preuve de celle-ci.

## Limites

L'interface ne prouve pas qu'un certificat existe. Sa cible est encore un
ordre partiel abstrait : aucune variété lorentzienne, mesure, dimension ou
géométrie n'est construite. La probabilité d'échec est bornée entre 0 et 1,
mais aucune mesure de probabilité ni borne statistique n'est encore démontrée.
L'unicité approximative de cibles concurrentes reste ouverte.

MF-MAN-002 prouve en outre que tout ordre partiel fini peut satisfaire ce
contrat si cible et volume sont choisis après coup. Voir
[`program_m_faithful_embedding_nogo.md`](program_m_faithful_embedding_nogo.md).

Cette étape empêche donc de rebaptiser un simple plongement d'ordre en
« géométrie émergente ». Elle n'introduit ni Janus ni une gorge. Une future
classe géométrique pourra spécialiser la cible, les régions, le volume et les
échelles ; le programme P ne recevra que les géométries certifiées.
