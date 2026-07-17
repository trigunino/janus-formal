# Programme B — Bianchi covariant et matière

Pour l'unique potentiel Hassan–Rosen, l'invariance sous les difféomorphismes
diagonaux donne l'identité inhomogène

`sqrt(-g) nabla_g V_g + sqrt(-f) nabla_f V_f = 0`.

Les deux actions de matière étant séparément invariantes, leurs équations
donnent sur couche

`nabla_g T_plus=0`, `nabla_f T_minus=0`.

Aucun transport direct d'un tenseur matière vers l'autre métrique n'est requis
dans Candidate A. Au contraire, copier `T_minus` dans l'équation `g` sans terme
variationnel croisé casserait la fermeture et pourrait réintroduire le ghost.

Le point 4 est donc fermé pour le système minimal natif de Candidate A. Mais
cela révèle une limite : la matrice de source croisée signée de Janus ne découle
pas de ce couplage minimal. Elle nécessiterait un nouveau couplage covariant,
qui devrait repasser les tests ADM/BD.

## Pont fourni par le Programme P

P mécanise maintenant, sur un second jet scalaire covariant 4D,
\[
\nabla_\mu T^{\mu\nu}=(\Box\phi-V'(\phi))\nabla^\nu\phi.
\]
La conservation native utilisée ici découle donc explicitement de l'équation
scalaire dans ce secteur local, y compris avec la connexion de Levi-Civita
construite depuis le premier jet métrique. Cela ne constitue pas encore un
théorème global pour des champs lisses ni un couplage croisé signé.
