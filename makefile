lean:
	cd ./lean && lake build

rocq:
	cd ./rocq && $(MAKE)

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIRS) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -name "*.glob" \) -delete
	$(Q)rm -f rocq/.timing.sqlite3
	rm -f rocq/.rocqdeps.d

.PHONY: default lean rocq
.DELETE_ON_ERROR:

