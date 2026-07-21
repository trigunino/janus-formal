# MF-GEO-002 — Le collage local sélectionne-t-il la géométrie ?

## Test

On reprend le préordre de MF-GEO-001 : `0<1`, avec `2` et `3` isolés. Il est
couvert par deux morceaux `{0,1,2}` et `{0,1,3}`, recollés sur l'interface
`{0,1}`. Toutes les relations primitives sont visibles localement.

Pour la reconstruction métrique de rang enregistrée dans MF-MAN-008 :

- chaque morceau possède exactement une classe métrique ;
- l'interface possède exactement une classe métrique ;
- le collage global possède pourtant deux classes métriques.

## Conclusion

L'unicité locale et l'accord sur l'interface ne sélectionnent pas une géométrie
globale unique. L'information perdue concerne ici la paire `{2,3}`, qui
n'apparaît ensemble dans aucun morceau.

Le principe envisagé doit donc être renforcé. Il faut soit une règle contrôlant
les relations géométriques entre points non conjointement observés, soit une
véritable loi de raffinement garantissant que toute paire pertinente finit par
être testée. Cette condition reste à formuler sans introduire une métrique à la
main.

Ce résultat est un no-go fini pour la reconstruction de rang déclarée, pas un
théorème contre toute reconstruction continue ou probabiliste.

Le script est `scripts/audit_program_m_geometric_gluing_selection.py`; la
sortie est `outputs/program_m/mf_geo_002_geometric_gluing_selection.json`.
