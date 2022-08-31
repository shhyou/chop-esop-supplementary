#lang info

;; comment
(define version "0.0.1")
(define name "concolic-hop-prototype")
(define collection 'multi)
(define build-deps '("rackunit-lib"
                     ))
(define deps       '("base"
                     ["rosette" #:version "4.0"]
                     "data-lib"
                     "data-enumerate-lib"
		     "gui-lib"
                     "rackunit-lib"
                     ))

(define compile-omit-paths
 '("tests"))
