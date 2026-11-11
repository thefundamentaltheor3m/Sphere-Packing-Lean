.PHONY: blueprint serve

# Build the Verso blueprint site into `_out/site/html-multi`.
blueprint:
	lake exe vbp build

# Build the blueprint and serve it locally (prints the preview URL).
serve:
	lake exe vbp build --serve
