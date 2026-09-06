# forge

The codegen pipeline orchestrator. Owns: invoking lake emitters, byte-tie
checking (`forge gen --check`), wasm component linking, OCI layout store.
Never contains: emitters (Lean owns those), devenv logic (shell stays thin).
