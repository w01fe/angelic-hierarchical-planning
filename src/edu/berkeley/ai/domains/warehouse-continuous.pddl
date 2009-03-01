;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Warehouse world
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; everything has height 1 
; (0,0) is at bottom left.
; gripper has width 0 unless holding a block.
; Positions are [left, right) and [bottom, top) intervals.?
; Edge must be flush with blocks to pick up / put down.

(define (domain WAREHOUSE-HYBRID)
  (:requirements :strips :typing :equality :numbers)
  (:types block)
  (:numeric-types x y)
  (:predicates 
   (on ?b - block ?c - block)
   (clear ?b - block)
   (holding ?b - block)
   (gripperempty)
   (facingright))
  (:numeric-functions
   (width)                    - x
   (height)                   - y
   (blockwidth ?b - block)    - x
   (gripperx)                 - x
   (gripperbottomy)           - y
   (blockleftx ?b - block)    - x
   (blockbottomy ?b - block)) - y

  (:action get-l
	   :parameters   (?b - block ?c - block ?bx - x ?bw - x ?gx - x ?y - y)
	   :precondition (and (= (+ ?bx ?bw) ?gx)
			      (gripperx ?gx)
			      (gripperbottomy ?y)
			      (blockleftx ?bx)
			      (blockbottomy ?y)
			      (= (blockwidth ?b) ?bw)
			      (on ?b ?c)
			      (clear ?b)
			      (gripperempty)
			      (not (facingright)))
	   :effect       (and (not (gripperempty))
			      (not (on ?b ?c))
			      (holding ?b)
			      (clear ?c)))

  (:action get-r
	   :parameters   (?b - block ?c - block ?bx - x ?y - y)
	   :precondition (and (gripperx ?bx)
			      (gripperbottomy ?y)
			      (blockleftx ?bx)
			      (blockbottomy ?y)
			      (on ?b ?c)
			      (clear ?b)
			      (gripperempty)
			      (facingright))
	   :effect       (and (not (gripperempty))
			      (not (on ?b ?c))
			      (holding ?b)
			      (clear ?c)))

  (:action put-l
	   :parameters   (?b - block ?c - block ?bx - x ?bw - x ?gx - x ?by - y ?cx - x ?cw - x ?cy - y)
	   :precondition (and (= (+ ?bx ?bw) ?gx)
			      (gripperx ?gx)
			      (gripperbottomy ?y)
			      (blockleftx ?bx)
			      (blockbottomy ?y)
			      (= (blockwidth ?b) ?bw)
			      (on ?b ?c)
			      (clear ?b)
			      (gripperempty)
			      (not (facingright)))
	   :effect       (and (not (gripperempty))
			      (not (on ?b ?c))
			      (holding ?b)
			      (clear ?c)))

  (:action put-l
             :parameters (?b - block ?c - block ?bx - xc ?gx - xc ?cy - yc ?gy - yc)
	     :precondition (and (leftof ?bx ?gx)
				(above ?gy ?cy)
				(gripperat ?gx ?gy)
				(blockat ?c ?bx ?cy)
				(holding ?b)
				(clear ?c)
				(not (facingright)))
	     :effect       (and (blockat ?b ?bx ?gy)
				(someblockat ?bx ?gy)
				(gripperempty)
				(on ?b ?c)
				(not (holding ?b))
				(not (clear ?c))))

  (:action put-r
             :parameters (?b - block ?c - block ?bx - xc ?gx - xc ?cy - yc ?gy - yc)
	     :precondition (and (leftof ?gx ?bx)
				(above ?gy ?cy)
				(gripperat ?gx ?gy)
				(blockat ?c ?bx ?cy)
				(holding ?b)
				(clear ?c)
				(facingright))
	     :effect       (and (blockat ?b ?bx ?gy)
				(someblockat ?bx ?gy)
				(gripperempty)
				(on ?b ?c)
				(not (holding ?b))
				(not (clear ?c))))

  (:action left
             :parameters (?cx - xc ?dx - xc ?y - yc)
	     :precondition (and (leftof ?dx ?cx)
				(gripperat ?cx ?y)
				(not (someblockat ?dx ?y)))
	     :effect       (and (not (gripperat ?cx ?y))
				(gripperat ?dx ?y)))

  (:action right
             :parameters (?cx - xc ?dx - xc ?y - yc)
	     :precondition (and (leftof ?cx ?dx)
				(gripperat ?cx ?y)
				(not (someblockat ?dx ?y)))
	     :effect       (and (not (gripperat ?cx ?y))
				(gripperat ?dx ?y)))

  (:action up
             :parameters (?x - xc ?cy - yc ?dy - yc)
	     :precondition (and (above ?dy ?cy)
				(gripperat ?x ?cy)
				(not (someblockat ?x ?dy)))
	     :effect       (and (not (gripperat ?x ?cy))
				(gripperat ?x ?dy)))

  (:action down
             :parameters (?x - xc ?cy - yc ?dy - yc)
	     :precondition (and (above ?cy ?dy)
				(gripperat ?x ?cy)
				(not (someblockat ?x ?dy)))
	     :effect       (and (not (gripperat ?x ?cy))
				(gripperat ?x ?dy)))

  (:action turn-l
	     :parameters (?x - xc ?y - yc)
	     :precondition (and (gripperat ?x ?y)
				(topy ?y)
				(facingright))
	     :effect       (not (facingright)))

  (:action turn-r
	     :parameters (?x - xc ?y - yc)
	     :precondition (and (gripperat ?x ?y)
				(topy ?y)
				(not (facingright)))
	     :effect       (facingright))

  )
