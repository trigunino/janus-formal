# MF-PBRIDGE-002 — Adaptateur signé de M vers P

## Entrée exacte

L'adaptateur accepte une configuration relationnelle équipée de :

- une involution qui préserve les relations ;
- une charge réelle impaire sous cette involution ;
- l'absence de charge nulle.

Il ne contient ni variété, ni métrique, ni dimension, ni gorge, ni action.

## Conversion vers P

Pour chaque charge non nulle `q`, Lean construit :

```text
secteur(q) = positive si q>0, negative si q<0
amplitude(q) = |q|.
```

et prouve exactement :

```text
q = chargeValue(secteur(q)) × amplitude(q),
secteur(-q) = ptCharge(secteur(q)).
```

Ainsi l'involution de M devient l'échange binaire utilisé par l'interface
`JanusCharge` de P. Une amplitude externe se factorise sans identifier le signe
de charge à une masse inertielle négative.

## Hypothèses de P réellement réduites

M peut désormais fournir conditionnellement :

- le support de configurations relationnelles ;
- une transformation involutive admissible ;
- les deux labels de secteur et leur échange ;
- l'algèbre d'une source signée avec magnitude séparée.

Restent entièrement externes : géométrie lisse et lorentzienne, dimension,
champs, gorge, mapping torus, PT géométrique, SpinC, magnitude physique,
normalisation, loi du médiateur, action parente et sélection variationnelle.

La distinction est nécessaire : les no-go de la littérature bimétrique montrent
que des forces exactement opposées ne peuvent pas être déduites d'une simple
interprétation naïve en masses positives/négatives
([Hohmann–Wohlfarth, 2009](https://arxiv.org/abs/0908.3384)). L'adaptateur ne
revendique donc qu'une charge algébrique signée.

Le module formel est
`JanusFormal/Foundations/ProgramMSignedProgramPAdapter.lean`. Le script est
`scripts/audit_program_m_signed_program_p_adapter.py`; la sortie est
`outputs/program_m/mf_pbridge_002_signed_program_p_adapter.json`.
