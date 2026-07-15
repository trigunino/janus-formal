# Action bimétrique minimale — gabarit de travail

Ce document est un gabarit, pas une théorie validée.

## Action

\[
S = S_{EH}[g_+] + S_{EH}[g_-] + S_{int}[g_+,g_-]
    + S_{matter}[\psi_+,g_+] + S_{matter}[\psi_-,g_-].
\]

On peut écrire provisoirement :

\[
S_{int}=m^2 M^2\int d^4x\,\sqrt{-g_+}\,V(g_+^{-1}g_-).
\]

Le potentiel \(V\) doit être choisi dans une classe sans fantôme de
Boulware–Deser. Le potentiel quartique utilisé dans le modèle jouet ne suffit
pas à garantir cette propriété.

## Secteurs quantiques

Les champs \(\psi_+\) et \(\psi_-\) vivent d’abord dans des secteurs séparés :

\[
S_{matter}=S_+[\psi_+,g_+]+S_-[\psi_-,g_-].
\]

Une interaction directe \(\psi_+\psi_-\) serait ajoutée seulement comme
terme expérimental, afin de déterminer si la bimétrie seule peut la générer.

## Critères de rejet

- présence d’un degré de liberté fantôme ;
- Hamiltonien non borné sans prescription physique ;
- violation de l’unitarité ;
- signalisation supraluminique ;
- absence de limite vers la relativité générale et la mécanique quantique
  connues.

## Prochaine implémentation

Commencer en dimension 1+1 avec deux métriques fixes et un potentiel scalaire
\(V=\beta(\mathrm{Tr}(g_+^{-1}g_-)-2)^2/2\). Ensuite seulement, tester si la
variation de ce potentiel peut reproduire le couplage \(X_+X_-\) du modèle
jouet.
