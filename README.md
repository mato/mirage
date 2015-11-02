## Mirage

Mirage is a programming framework for constructing secure, high-performance
network applications across a variety of cloud computing and mobile platforms.
Code can be developed on a normal OS such as Linux or MacOS X, and then compiled
into a fully-standalone, specialised unikernel that runs under the Xen
hypervisor. Since Xen powers most public cloud computing infrastructure such as
Amazon EC2, this lets your servers run more cheaply, securely and finer control
than with a full software stack.

The most up-to-date documentation can be found at the
[homepage](http://www.mirage.io). The site is self-hosted and a useful
[example](https://github.com/mirage/mirage-www). Simpler
[skeleton applications](https://github.com/mirage/mirage-skeleton) are also
available online.

[![Build Status](https://travis-ci.org/mirage/mirage.svg)](https://travis-ci.org/mirage/mirage)
[![docs](https://img.shields.io/badge/doc-online-blue.svg)](https://mirage.github.io/mirage/)

### This repository

This repository includes:

* a command-line tool to create and deploy applications with Mirage; and
* in `types/`, a library of type signatures that compliant applications use.

There are several diverse backends in Mirage that require rather specialised
build steps (from JavaScript to Xen unikernels), and this complexity is wrapped
up in the tool.

To work with Mirage, you'll need the following prerequisites installed:

* a working [OCaml](http://ocaml.org) compiler (4.01.0 or higher).
* the [OPAM](https://opam.ocaml.org) source package manager (1.2.0 or higher).
* an x86\_64 or armel Linux host to compile Xen kernels, or FreeBSD, OpenBSD or
  MacOS X for the userlevel version.

There are two stages to using `mirage`:

* a *configure* phase where OPAM package dependencies are satisfied.
* a *build* phase where the compiler and any support scripts are run.

### Configuration files

`mirage` currently uses a configuration file to build a Mirage unikernel. While
we're documenting it all, please see the `lib_test` directory in this repository
for the regression examples. The latest instructions are also to be found at
<http://openmirage.org/docs>

### Configuring Mirage Applications

Provided that one and only one file of name `<foo>.conf` (where `<foo>` can be
any string) is present in the current working directory, the command:

```
mirage configure
```

will configure your project. It will generate a `Makefile` and `main.ml` with
the appropriate boilerplate for your chosen platform.

To configure for the Unix-direct target (using tap interfaces), do:

```
mirage configure --unix
```

To build for the Xen target, do:

```
mirage configure --xen
```

### Building Mirage Applications

To compile your application, use:

```
make
```

### Running Mirage Applications

Every mirage backend will have a different way to be deployed. On Unix, the
unikernel will run as a Unix process, using a virtual interface (tap) if needed:

```
./mir-<project-name>
```

On Xen, the unikernel will run as a virtual machine. For instance, using the
`xl` command-line tool:

```
xl create <project-name>.xl
```

Configuration files for `xe` and `libvirt` are also generated by the tool (see
the files `<project-name>_libvirt.xml` and `<project-name>.xe` in the build
directory).

### Compiling to Xen and deploying to the cloud

In order to deploy a Mirage unikernel to Amazon EC2, you need to install the AWS
tools on your machine, build a unikernel with the `--xen` option and then use
the `ec2.sh` script (in directory `script`) in order to register your kernel
with AWS. Then you can start your kernel with the web interface to AWS or any
other means AWS provides to start EC2 instances.
