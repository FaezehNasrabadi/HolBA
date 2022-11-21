This is an implementation of the symbolic execution engine used in CryptoBAP toolchain.
This implementation also includes the translation of the symbolic tree into an intermediate model language.


It includes the following:

	- binaries/balrob/ : A directory contains the source code of the protocols we analysed: simple mac, simple xor, RPC, RPC-enc, NSL and TinySSH at ARMv8 binary code.
	- PreProcess/ : A directory consists of the source codes for preprocessing the BIR program before executing by our symbolic execution.
	- IML/ : A directory includes the intermediate model language (IML) syntax implemented on top of the theorem prover HOL4.
	- libload/ : A directory contains the source codes of our crypto-aware symbolic execution.
	- Tests/ : A directory includes the IML output and the input files for each of our use-cases, such as :
		- The function names used in the protocol implementation 
		- The names of cryptographic functions used in the protocol implementation 
		- The name of functions used for network communications in the protocol implementation and we anoint them adversary function names
		- The number of entries for cryptographic functions used in the protocol implementation
		- The number of entries for adversary functions used in the protocol implementation
		- The name of events we release during the execution of the protocol


How to setup and compile
========================

1) Set up HolBA framework in the root directory using README.md
2) In binaries/balrob/binariesBalrobDefsLib.sml : Specify which binary file and which blocks inside it you want to transpile into the binary intermediate representation (BIR)
3) In order to generate a BIR program of your specified binary file when you are in binaries/balrob/ directory execute the following lines :
	- source ../../../../../../env.sh
	- Holmake

You can find the BIR program stored in binariesTheory.sig file

4) Now you can go to the root directory and verify your desired use-case in the Tests/ directory with the command make as following:
	- make src/tools/symbexec/examples/Tests/

5) You can find the IML result in IML_Translation.txt file in subdirectory of the tests/ directory
