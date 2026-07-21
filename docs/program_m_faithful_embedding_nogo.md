# MF-MAN-002 — Pourquoi le premier contrat ne sélectionne rien

## Théorème

Tout ordre partiel fini possède un certificat `MF-MAN-001` tautologique :

- la cible est l'ordre lui-même ;
- le plongement est l'identité ;
- les régions sont ses sous-ensembles ;
- leur « volume » est défini comme leur cardinal ;
- densité 1 et tolérance 0 rendent la loi nombre-volume exacte.

La preuve Lean `abstract_faithful_embedding_is_automatic` montre donc que le
contrat abstrait est une interface de vérification, pas encore un critère de
ressemblance à une variété.

## Information manquante

La cible et son volume doivent être définis indépendamment du candidat discret.
Il faut notamment une classe de variétés lorentziennes, leur ordre causal et
leur mesure de volume, puis un contrôle statistique non fabriqué après coup.

La revue de Surya décrit le principe « ordre ↔ ordre causal, nombre ↔ volume »
et souligne que la reconstruction générale reste ouverte :
[Living Reviews in Relativity (2019)](https://link.springer.com/article/10.1007/s41114-019-0023-1).

Un préprint récent propose un renforcement par la correspondance entre longueur
de plus longue chaîne et temps propre, puis obtient sous ses hypothèses une
unicité approximative à haute densité :
[Madsen, 2026](https://arxiv.org/abs/2607.05840). Program M l'enregistre comme
résultat externe récent à auditer, pas comme théorème déjà reproduit en Lean.

## Conséquence

Le prochain contrat devra interdire le choix tautologique en exigeant :

1. une cible appartenant à une classe lorentzienne fixée indépendamment ;
2. un volume et un temps propre issus de cette cible ;
3. une correspondance longueur de chaîne–temps propre à des échelles déclarées ;
4. une notion explicite de proximité entre deux géométries candidates.

Ni Janus ni une gorge ne sont introduits.

