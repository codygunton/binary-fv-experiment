# make -C tools/zmap map: static map (only when the ELF hash differs from static.json's or it was
# built without join cuts), proof status, merge, queue, page, cost model. Outputs in P/map/.
P      := $(abspath $(dir $(lastword $(MAKEFILE_LIST)))/../..)
MAP    := $(P)/map
ELF    ?= /home/cody/zesislar/build/stock-zisk/zesu-zisk.elf
SHA256 ?= e44c18d54ae3d77832df92aceb6eb7119de8eb2e8f1f1b4e585a6e33ea04ff95
OBJ    ?= /home/cody/zesislar-archive/stock-inputs/dcd4b1bec1b02f94d7c4bca3d8323c386cfc7b780995235d6947790bb68d1afe-zesu.o
ZMAP   := cd $(P)/tools && python3 -m zmap

.PHONY: map static status test

map: static status
	$(ZMAP) merge --static $(MAP)/static.json --status $(MAP)/status.json \
	  --reviews $(MAP)/reviews.json --ledger $(MAP)/ledger.jsonl --out $(MAP)/map.json
	$(ZMAP) queue --map $(MAP)/map.json --out $(MAP)/QUEUE.md --json $(MAP)/queue.json
	$(ZMAP) site --map $(MAP)/map.json --queue $(MAP)/queue.json --out $(MAP)/site
	$(ZMAP) costmodel --map $(MAP)/map.json --ledger $(MAP)/ledger.jsonl --out $(MAP)/COSTMODEL.md

static:
	@have=$$(python3 -c 'import json,sys; s=json.load(open(sys.argv[1])); print(s["elf_sha256"] + ("" if s.get("join_cuts") else ":nojoin"))' \
	  $(MAP)/static.json 2>/dev/null); \
	now=$$(sha256sum $(ELF) | cut -d' ' -f1); \
	if [ "$$have" = "$$now" ]; then echo "zmap: static.json is for ELF $$now; not rebuilt"; \
	else $(ZMAP) build --elf $(ELF) --sha256 $(SHA256) --debug-object $(OBJ) --out $(MAP)/static.json; fi

# The status JSON is the output of `lake exe zesu-status` (the fixture in tests/ is for tests only).
status:
	cd $(P) && lake build zesu-status >&2
	cd $(P) && lake exe zesu-status > $(MAP)/status.json.tmp && mv $(MAP)/status.json.tmp $(MAP)/status.json

test:
	cd $(P) && python3 -m unittest discover -s tools/zmap/tests
