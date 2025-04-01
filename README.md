# Towards a Formally Verified eBPF Just-in-Time Compiler for Solana

We have tested our project on:
- Windows 11 + WSL2 (Ubuntu 22.04 LTS)
- Ubuntu 22.04 LTS

plus `CPU: Intel(R) Core(TM) Ultra 7 155H   1.40 GHz` + `RAM 32G` + `Core: 16`



# 1. How to install

### 1. Install Isabelle/HOL and AFP

- [Isabelle/HOL 2024](https://isabelle.in.tum.de/) (please set your PATH with e.g. `/YOUR-PATH/Isabelle2024`)

- [Isabelle AFP](https://www.isa-afp.org/download/) (unzip the AFP to your PATH, e.g. `/YOUR-PATH/afp`)

```shell
# set PATH 
vim  ~/.bashrc # export PATH=$PATH:/YOUR-PATH/Isabelle2024/bin:...
source ~/.bashrc

# test isabelle/hol
isabelle version # Isabelle2024

# config AFP
cd /YOUR-PATH/afp/thys
isabelle components -u . # Add AFP to ...

# go to our repo folder and open this project in jedit
cd /OUR-REPO

# adding the following libs when install on WSL2 with Ubuntu 22.04.3 LTS (GNU/Linux 5.15.153.1-microsoft-standard-WSL2 x86_64)
sudo apt-get install libxi6 libxtst6 libxrender1 fontconfig
```

### 1.2 Install Rust, OCaml and related packages

First, check the Official [Rust web](https://www.rust-lang.org/tools/install) to install Rust.
The following instructions explains how to install OCaml + packages

```shell
# install opam

sudo apt install opam
# In the case you fail to install opam
# Note1: you may need the two commands before install opam, i.e. `add-apt-repository ppa:avsm/ppa` and `apt update`
# Note2: you may need to change your source list to focal source if `add-apt-repository ppa:avsm/ppa` fails


# install ocaml+coq by opam
opam init
# install ocaml
opam switch create sbpf ocaml-base-compiler.4.14.1

eval $(opam env)

opam switch list
#   switch  compiler      description
->  sbpf     ocaml.4.14.1  sbpf

# Note3: Once you get a warning here, please do `eval $(opam env)`, restart your computer/VM, and do `eval $(opam env)` again

# make sure your ocaml is 4.14.1 and from `/home/bob/.opam/sbpf/bin/ocaml`
which ocaml

# install necessary packages
opam install ocamlfind yojson
```

### 1.3 Install the `cloc` tool

```shell
sudo apt-get install cloc
```



# 2. PerIR

### 2.1 Link to paper

| Paper                   | Code                           |
| ----------------------- | ------------------------------ |
| Step:per_step (Section 4.2)    |    `theory/x64Semtancis.thy#L226`                            |
| Semantics:per_sem (Section 4.2) | `theory/x64Semtancis.thy#L253` |

# 3. PerJIT

### 3.1 Check PerJIT
This command starts up the IDE of Isabelle/HOL (JEdit), opens the `JITPer.thy` file, and checks the semantics automatically.
```shell
# at root directory
make
```
If you want to check another file, just click it on JEdit and the Isabelle/HOL checker then validates it automatically.

Note that we have

### 3.2 Link to paper

| Paper      | Code      |
| ------------- | ------------- |
| JIT Design (Section 5.1) | `theory/JITPer_aux.thy#L259` |
| JIT Rules (Section 5.2) | `theory/JITPer_aux.thy#L71-L257` |
| Proof of JIT Correctness (Section 5.3) | `theory/JITPer.thy#L472` |



# 4. Evaluation

### 4.1 PerJIT Validation

To obtain the validation results for PerJIT, run the following command:

```shell
# at the root directory
cd tests && make
```

This will automatically compile the latest PerJIT model and display the passed results in green:

```shell
1 arsh r3, r5                              result: true
2 lsh r4, r4                               result: true
...
```

Note that you can ignore the warning messages as long as the program runs successfully.

Use `make clean` to remove redundant files.


### 4.2 Code Statistics 
Run the following command to get the lines of code:

```shell
# at the root directory
make code
```

The code shown here includes all components of the formal model. In contrast, the code statistics in our paper reflect only the newly added code in this paper.

Note that currently, `cloc` doesn't support Isabelle/HOL now, we specify the language to OCaml because both use `(* *)` as comments.

### 4.3 Link to paper

| Paper                            | Code                                                         |
| -------------------------------- | ------------------------------------------------------------ |
| Validation Framework (Section 6.1) | isabell/hol: glue code `theory/JITExtraction.thy#L44` + extraction declration `theory/JITExtraction.thy#L59`, OCaml: glue code `tests/jit.ml`, PerJIT_test `tests/jit_val.ml` |



