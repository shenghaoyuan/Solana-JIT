code:
	@echo "Analyzing code statistics"
	@echo "SBPF Syntax"
	cd theory && cloc --force-lang="OCaml" Mem.thy Val.thy ebpf.thy rBPFCommType.thy rBPFSyntax.thy vm_state.thy 
	@echo "SBPF Semantics"
	cd theory && cloc --force-lang="OCaml" rBPFSem.thy 
	@echo "SBPF JIT"
	cd theory && cloc --force-lang="OCaml" JITPer_aux.thy JITFlat.thy 
	@echo "SBPF JIT Proof"
	cd theory && cloc --force-lang="OCaml" JITPer_*.thy JITPer.thy 
	@echo "SBPF x64 Model"
	cd theory && cloc --force-lang="OCaml" x64Assembler.thy x64Syntax.thy x64Semantics.thy x64Disassembler.thy 
	@echo "SBPF x64 Proof"
	cd theory && cloc --force-lang="OCaml" BitsOpMore.thy BitsOpMore2.thy BitsOpMore3.thy BitsOpMore4.thy Proof1.thy x64DecodeProofAux.thy
	@echo "SBPF JIT Extraction"
	cd theory && cloc --force-lang="OCaml" JITExtraction.thy rBPFDecoder.thy