# TYPES 
* A repository containing an implementation of certain Types (such as Nat, Bool, etc.) in Coq, with Theorems and Functions

## REPOSITORY
* [coq-types](https://github.com/jssandh2/coq-types)

## INSTALLATION
### Clone the Repository
* To clone the repository :
    * `cd /directory/to/clone/in`
    * `git clone git@github.com:jssandh2/coq-types.git`
### Install Coq 
* The current code can compile with Coq 8.5 and higher
* My suggestion is to install Coq 8.6 using Brew :
    * `brew install coq`
* Compilation of Coq files _can_ be done from the Command line _or_ inside the [Editor](https://coq.inria.fr/refman/Reference-Manual018.html) itself :
    * `cd /directory/of/coq/file`
    * `coqc filename.v`

## STRUCTURE
### Directories
* Each `Type` is implemented in a _separate_ directory inside :
    * Bool : `src/Bool/*`
    * Nat : `src/Nat/*`


### Functions
* Each type is implemented, with functions that are _verified_ using `Example` **and** `Proof`
* The majority of the code is inspired from [**Software Foundations**](https://www.cis.upenn.edu/~bcpierce/sf/current/index.html), and therefore, there is significant overlap in the code. However, the main idea here is to solve the Exercises and reimplement certain functions on my own

