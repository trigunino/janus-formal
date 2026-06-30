# Programme Axiome Janus

Position de travail : **Janus est suppose vrai**.

Cette position n'est pas une conclusion publique ; c'est une methode de recherche. Quand une observation semble contredire l'implementation actuelle, on cherche d'abord quelle hypothese standard a ete importee par erreur.

## Consequence Methodologique

Pour chaque tension :

1. identifier l'hypothese standard cachee ;
2. la remplacer par une hypothese Janus explicite ;
3. calculer la correction requise par les donnees ;
4. verifier si cette correction est simple, stable et derivable ;
5. seulement ensuite parler de prediction.

## Cas DESI BAO

Le score BAO direct de Janus est mauvais. Sous l'axiome Janus, cela veut dire :

- soit la distance BAO Janus utilisee est incomplete ;
- soit la regle standard `r_d` n'est pas un scalaire constant dans le cadre Janus ;
- soit les observables `D_M/r_d` et `D_H/r_d` publiees par DESI ne sont pas directement les bonnes observables Janus ;
- soit le modele Janus d'expansion simple doit etre complete par la physique du regime a constantes variables.

Le script `scripts/infer_janus_bao_ruler.py` inverse le probleme : il demande quelle correction du ruler BAO serait necessaire pour que Janus reproduise DESI.

## Critere De Piste Forte

Une correction requise devient interessante si elle est :

- basse dimension : peu de parametres ;
- monotone ou reliee a une variable Janus naturelle ;
- identique ou explicablement differente entre transverse `D_M` et radial `D_H` ;
- compatible avec les supernovae et le CMB ;
- predictive sur des donnees non utilisees pour l'ajustement.

## Risque Principal

Une correction trop flexible peut tout expliquer. Elle ne vaut rien tant qu'elle n'est pas derivee des equations Janus.

Le but n'est donc pas de sauver Janus avec des parametres libres, mais d'utiliser les parametres requis comme une empreinte pour chercher la bonne equation manquante.
