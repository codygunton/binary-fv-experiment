# Developer tools

The retained tools are target-independent building blocks for the next authentic Zesu proof:

- `analyze_rv64.py`: direct-control-flow analysis over RV64 disassembly.
- `lean_profile.py`: capture and merge Lean profiler output.
- `ngram_motifs.py`: normalized instruction-window discovery.
- `analyze_machine_proof_corridors.py`: retrieve similar composition-backed proof shapes.
- `binary-regions-ui/`: retained target-neutral viewer shell; its next data generator will consume the
  authentic target's machine regions and proof manifests.

These live tools have target-independent inputs. The earlier Elfling and machine-region generators
contained substantial `decodeRaw` policy and therefore remain in the archive branch rather than
being mislabeled generic; their reusable extraction pieces will be recovered when the new target
schema is defined. Similarity ranking suggests templates but never establishes a proof.

Run focused Python tests with `python3 -m unittest discover -s tools -p '*_test.py'`.
