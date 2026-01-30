# Requirements and Installation
To use this automation of the small inversions, you need Rocq and the library MetaRocq.
To install them, first install the package manager opam.
## Requirements
This code is intended for Rocq 9.1.0, and MetaRocq version 1.4.1+9.1.
## Summary of installation
A detailed procedure is provided below.
Using `opam install TODO` should install every dependency and the plugin.
# Installation Guide
## Installing opam
To install opam, follow the instructions on their [website](https://opam.ocaml.org/doc/Install.html).

Then, to initialize it, run the following commands : 

```bash
opam init
eval $(opam env)
```
Every shell that is used to run opam commands or to compile Rocq code must have `eval $(opam env)` run in it beforehand. 
## Installing the plugin
Once opam is initialised, run the following command to add the main repository of Rocq opam packages:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

Finally, only the plugin needs to be installed.
The following command will install the plugin as well as all of its dependencies.  

```bash
opam pin git+https://github.com/DeLectionnes/proxy-based-small-inversions
```