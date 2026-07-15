# Programme B — domaine réel de la racine bimétrique

Pour `A=g_plus^-1 g_minus`, la racine principale réelle et analytique existe
sur le domaine spectral où `spectrum(A)` évite l'axe réel négatif fermé.

Une racine réelle non principale peut exister avec des valeurs propres
négatives seulement si, pour chaque valeur propre négative, les blocs de
Jordan de chaque taille apparaissent en nombre pair.

La branche proportionnelle positive `A=c² I`, `c>0`, appartient au domaine et
possède `sqrt(A)=c I`. Une collision spectrale avec l'axe négatif marque une
frontière de branche.

Le domaine point par point est ainsi classifié. Prouver qu'une solution
spatio-temporelle entière n'atteint jamais sa frontière demande les équations
d'évolution et les données initiales de P/E.

## Tube quantitatif autour de la branche proportionnelle

Le critère de Gershgorin fournit maintenant une condition suffisante locale,
valable même si `A` n'est pas symétrique :
\[
 \|A-c^2I\|_\infty<c^2\quad\Longrightarrow\quad
 \operatorname{Re}\sigma(A)>0.
\]
La racine principale réelle reste donc analytique dans ce tube. Pour une
évolution absolument continue, l'inégalité
\[
 \|A(0)-c^2I\|_\infty+
 \int_0^T\|\dot A(t)\|_\infty dt<c^2
\]
prouve sa préservation jusqu'à `T`. C'est une preuve conditionnelle complète :
P/E doit encore fournir une borne sur l'intégrale de vitesse pour une solution
physique donnée. L'égalité n'est pas certifiée, car la marge doit être stricte.
