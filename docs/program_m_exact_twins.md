# MF-MAN-016 — Gate des jumeaux relationnels exacts

## Calibration

La taille maximale d'une classe ayant exactement le même passé et le même
futur est mesurée sur des ordres Poisson frais aux cardinalités
`128, 256, 512, 784`.

Le protocole utilise 199 références, le rang conforme unilatéral `180/200` et
400 validations par taille. À `N=256`, le seuil obtenu est `2` : les paires
naturelles sont conservées, tandis que les multiplicités artificielles 4, 8 et
12 sont rejetées.

Le seuil n'a donc pas été fixé à zéro après observation de MF-ADV-002. Il est
déduit d'une référence indépendante avec une garantie marginale de 90 % sous
échangeabilité.

## Limite

Le gate ne détecte que l'égalité exacte des ensembles passé/futur. Il ne voit
pas nécessairement des quasi-jumeaux ou plusieurs sous-ordres isomorphes dont
les sommets portent des identités relationnelles différentes.

## Reproduction

```text
python scripts/audit_program_m_exact_twins.py \
  --output outputs/program_m/mf_man_016_exact_twins.json
```
