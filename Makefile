.PHONY: pdf web serve all

TARGETS := pdf web serve all

# Usage: make <pdf|web|serve|all>
$(TARGETS):
	leanblueprint $@
