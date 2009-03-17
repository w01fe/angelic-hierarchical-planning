;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Road trip
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In this domain, there are a set of locations
; Each location has a certain amount of available fuel, at a given price
; The goal is to get to the destination while minimizing the sum of travel
; time and fuel cost.
; In some versions, there might also be variable driving speeds.
; gas tank always holds 100 gallons.

(define (domain SIMPLE-ROAD-TRIP)
  (:requirements :strips :typing :numbers)
  (:types loc)
  (:numeric-types gas price dist)
  (:predicates 
   (at ?l - loc) 
   (road-between ?l1 - loc ?l2 - loc) )
  (:numeric-functions
   (gas)                             - gas
   (gas-price ?l - loc)              - price
   (road-length ?l1 - loc ?l2 - loc) - dist)

  (:action refuel
     :parameters   (?l - loc ?g - gas)
     :split-points (and (= ?g 0)
			(= ?g (- 100 (gas))))
     :precondition 
       (and (at ?l)
	    (>= ?g 0)
	    (<= ?g (- 100 (gas))))
     :effect (= (gas) (+ (gas) ?g))
     :cost   (+ 0 (* (gas-price ?l) ?g)))

  (:action drive
     :parameters   (?from - loc ?to - loc)
     :precondition 
       (and (at ?from)
	    (road-between ?from ?to)
	    (>= (gas) (road-length ?from ?to)))
     :effect       
       (and (not (at ?from))
	    (at ?to)
	    (= (gas) (- (gas) (road-length ?from ?to))))
     :cost   (road-length ?from ?to))

  )
