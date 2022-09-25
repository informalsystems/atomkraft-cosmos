all:
	@echo "Targets:"
	@echo "\ttraces"
	@echo "\tclean"

.PHONY: traces
traces:
	time ./generate-traces.sh

.PHONY: clean
clean:
	rm -f ./*_TTrace_*.tla
	rm -frd ./states
	rm -frd ./_apalache-out

