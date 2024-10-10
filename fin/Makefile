
%.dot: %.lagda.md
	agda --dependency-graph=$@ $<

%.svg: %.dot
	dot -Tsvg $< >$@
