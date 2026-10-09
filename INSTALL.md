# Requirements and Installation
To use this automation of proxy-based small inversions, you need Rocq and the library MetaRocq.
This version is intended for Rocq 9.1, and MetaRocq version 1.4.1+9.1.

## Requirements
If you are here, you probably have already installed Rocq,
possibly with the package manager opam.
If this is not the case, please see basic instructions below (`Installing opam`).

## Installing the plugin

Our plugin can be installed using two methods.

### Method 1: using opam

If you used opam, the simplest way is as follows.
First, run the following command to add the main repository of Rocq opam packages:

```bash
opam repo add coq-released https://coq.inria.fr/opam/released
```

Then, the following command will install the plugin as well as all of its dependencies,
including MetaRocq.  

```bash
opam pin git+https://github.com/BasileGros/proxy-based-small-inversions
```

### Method 2: using a local version of this repository
This method can be used if you already have installed Rocq and MetaRocq.
After the usual `git clone` command on this repository
and assuming that you are on the suitable branch,
first check that the above requirements are satisfied:  

```bash
make check-version
```

If you already installed a previous version of our plugin:

```bash
make allclean
```

Then run the following commands:  

```bash
make
make install
```


## Installing opam
To install opam, follow the instructions on their [website](https://opam.ocaml.org/doc/Install.html).

Then, to initialize it, run the following commands:  

```bash
opam init
eval $(opam env)
```
Every shell that is used to run opam commands or to compile Rocq code must have `eval $(opam env)` run in it beforehand. 
