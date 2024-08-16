.PHONY: pdf web serve all

TARGETS := pdf web serve all

# Usage: make <pdf|web|serve|all>
$(TARGETS):
	rm -rf blueprint/print
	mkdir blueprint/print
	leanblueprint $@
