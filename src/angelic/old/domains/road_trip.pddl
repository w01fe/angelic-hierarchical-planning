;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Road trip
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; In this domain, there are a set of locations
; Each location has a certain amount of available fuel, at a given price
; The goal is to get to the destination while minimizing the sum of travel
; time and fuel cost.
; In some versions, there might also be variable driving speeds.

(define (domain ROAD-TRIP)
  (:requirements :strips :typing :numbers)
  (:types loc)
  (:numeric-types gas price dist)
  (:predicates 
   (at ?l - loc) 
   (road-between ?l1 - loc ?l2 - loc)
;   (has-gas ?l - loc)
    )
  (:numeric-functions
   (gas)                             - gas
   (tank-size)                       - gas
   (gas-at ?l - loc)                 - gas
   (gas-price ?l - loc)              - price
   (road-length ?l1 - loc ?l2 - loc) - dist)

  (:action refuel
     :parameters   (?l - loc ?g - gas)
     :split-points (and (= ?g 0)
			(= ?g (- (tank-size) (gas)))
			(= ?g (gas-at ?l)))
     :precondition 
       (and (at ?l)
;	    (has-gas ?l)
	    (>= ?g 0)
	    (<= ?g (- (tank-size) (gas)))
	    (<= ?g (gas-at ?l)))
     :effect       
       (and (= (gas) (+ (gas) ?g))
	    (= (gas-at ?l) (- (gas-at ?l) ?g)))
     :cost (* (gas-price ?l) ?g))

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
     :cost (road-length ?from ?to))


  )
