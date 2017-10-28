all: \
	meta/structured-names.maude

# `pd` is a patched version of `pandoc` capable of writing code files

meta/%.maude: meta.md/%.md
	pd --from markdown --to 'code{.maude}' $< > $@
