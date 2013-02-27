#lang scribble/doc
@(require (for-label swindle/turbo))

@title{Swindle Turbo}

@defmodulelang[swindle/turbo]

This module combines the `base', `setf', and `misc', modules to create a
new language module.  Use this module to get most of Swindle's
functionality which is unrelated to the object system.

 (set! place value ...)  [*syntax*]
 (pset! place value ...) [*syntax*]
 (set!-values (place ...) expr) [*syntax*]
  This module renames `setf!', `psetf!', and `setf!-values' from the
  `setf' module as `set!', `pset!' and `set!-values' so the built-in
  `set!' and `set!-values' syntaxes are overridden.

 #%module-begin
  `turbo' is a language module -- it redefines `#%module-begin' to load
  itself for syntax definitions.

