# Intermediate Memory Model (IMM) and compilation correctness proofs for it

This repository contains Coq code supplementing the paper *Bridging the Gap Between Programming Languages and Hardware Weak Memory Models*
([arXiv](https://arxiv.org/abs/1807.07892)) by Anton Podkopaev, Ori Lahav, and Viktor Vafeiadis.

## Building the Project

### Requirements
* [Coq 8.8.1](https://coq.inria.fr)
* [Hahn library](https://github.com/vafeiadis/hahn) (`coq-hahn`)
* [The Coq development of A Promising Semantics for Relaxed-Memory Concurrency](https://github.com/anlun/promising-coq/tree/opam_red) (`coq-promising`)

### Building Manually

To build the project, one needs to install some libraries (`sflib`, `paco`, `promising-coq`, and `hahn`), which the project
depends on. This might be done by running `./configure`.
The command installs `Coq` as well. After that, one needs to run `make` (or `make -j4` for a faster build).

### Installation via OPAM
The project may be built and installed via OPAM:
```bash
opam repo add coq-released https://coq.inria.fr/opam/released
opam remote add coq-weakmemory-local -k git https://github.com/weakmemory/local-coq-opam-archive
opam install coq-imm
```

### Building in a virtual machine
Download the VirtualBox image from [here](http://plv.mpi-sws.org/imm/popl19-imm-artifact.ova) (or [here](http://podkopaev.net/popl19-imm-artifact)),
import it into VirtualBox, and boot the machine.
The image has been tested with VirtualBox 5.2.18 with Oracle VM VirtualBox Extension pack.

The login is `popl` and the password is `popl`.

All necessary software is installed, and the project is checked out to `/home/popl/imm`.
Additionally, Emacs and Proof General are installed so that you can browse the sources.

The proofs might be checked by opening a terminal and running
```bash
cd /home/popl/imm
make clean; make -j2
```
There might be some warnings about notations. The build terminating without printing "error" is successful.

### Building in a Docker container
First, one needs to build a Docker image with the project and its dependencies
```bash
sudo docker build -t weakmemory/imm .
```
or to pull it from Docker Hub
```bash
docker pull weakmemory/imm
```
After that, one has to connect to the container

```bash
docker run -it weakmemory/imm /bin/bash
```
and execute the following to update container's environment variables
and rebuild the project
```bash
eval `opam config env`
cd /imm
make clean; make -j4
```

## Description of code and its relation to the paper
* **Section 2.** `src/basic`. Definitions and statements about programs and execution graphs.
  - *Prog.v*—a definition of the program language (**Fig. 2**).
  - *Events.v*—definitions related to events (**Section 2.2**).
  - *Execution.v*, *Execution\_eco.v*—execution graphs (**Section 2.2**).
  - *ProgToExecution.v*—construction of execution graphs from sequential programs (**Fig. 3**).
  - *ProgToExecutionProperties.v*—properties of the construction.

* **Section 3.** `src/imm`. Definitions and statements about IMM
and IMMs, a version of IMM with RC11-style definition of happens-before (HB).
  - *CombRelations.v*, *CombRelationsMore.v*—definitions of relation VF (in the development called `furr`)
     and linked relations and their properties.
  - *imm\_common\_more.v*, *imm\_common.v*—common definitions for both models.
  - *imm\_hb.v*—a definition of HB for IMM (**Section 3.1**).
  - *imm\_s\_hb.v*—the RC11-style definition of HB for IMMs.
  - *imm.v*—a definition of IMM (**Def. 3.11**).
  - *imm\_s.v*—a definition of IMMs.
  - *imm\_sToimm.v*—a proof that IMMs is weaker than IMM.

* **Section 4.** `src/hardware`. Definitions of hardware models and proofs about them.
  - *Power\_fences.v*,
    *Power\_ppo.v*,
    *Power.v*—a definition of POWER (Alglave-al:TOPLAS14).
  - *Rel\_opt.v*—a correctness proof for release write transformation (**Thm. 4.1**).
  - *immToPower.v*—a compilation correctness proof from IMM to POWER (**Thm. 4.3**).
  - *Arm.v*—a definition of ARMv8.3 (Pulte-al:POPL18).
  - *immToARM.v*—a compilation correctness proof from IMM to ARMv8.3 (**Thm. 4.5**).
  - *TSO.v*—a definition of TSO (Alglave-al:TOPLAS14, Owens-al:TPHOLs09).
  - *immToTSO.v*—a compilation correctness proof from IMM to TSO.

* `src/c11`. Definition of C11 model w/o SC and NA accesses and a compilation correctness proof from it to IMM.
  - *C11.v*—a definition of C11 (Batty-al:POPL11).
  - *C11Toimm\_s.v*—a compilation correctness proof from C11 to IMMs.

* `src/rc11`. Definition of RC11 model w/o SC and NA accesses and a compilation correctness proof from it to IMM.
  - *RC11.v*—a definition of RC11 (Lahav-al:PLDI17).
  - *RC11Toimm\_s.v*—a compilation correctness proof from RC11 to IMMs.

* **Section 5.** `src/promiseToImm`. The compilation correctness from Promise to IMM.
  - *Promise.v*—a definition of a Promise outcome (**Def. 5.1**).
  - *PromiseFuture.v*— a proof that it is enough to show certification
    only for a restricted set of future memories (**Remark 3**).
  - *TraversalConfig.v*, *Traversal.v*—a small traversal step of IMM-consistent execution graphs
      used to prove properties of the traversal (**Def. 5.3 and 5.7**).
  - *SimTraversal.v*—traversal of IMM-consistent execution graphs (**Fig. 6 and Prop. 5.8**).
  - *SimTraversalProperties.v*—properties of the normal traversal.
  - *SimulationRel.v*—a simulation relation (**Section 5.3**).
  - *SimulationPlainStep.v*— a proof of simulation step (**Prop. 5.9**).
  - *PlainStepBasic.v*,
    *WritePlainStep.v*,
    *FencePlainStep.v*,
    *RMWPlainStep.v*,
    *ReadPlainStep.v*,
    *ReadPlainStepHelper.v*—auxiliary lemmas for the simulation step proof.
  - *SubExecution.v*,
    *CertCOhelper.v*,
    *CertExecution1.v*,
    *CertExecution2.v*,
    *Receptiveness.v*, *CertExecutionMain.v*—construction of the certification graph and proofs of its properties (**Section 5.4**).
  - *PromiseToIMM.v*—a proof of the compilation correctness from Promise to IMM (**Prop. 5.12 and 5.13, Thm. 5.14**).

Auxiliary files:
- *AuxRel.v*,
*MaxValue.v*,
*Monotone.v*,
*Event\_imm\_promise.v*,
*SimStateHelper.v*,
*SimulationPlainStepAux.v*,
*SimulationRelAux.v*,
*TraversalConfigAlt.v*,
*TraversalCounting.v*,
*ViewRelHelpers.v*,
*ViewRel.v*,
*MemoryAux.v*.
