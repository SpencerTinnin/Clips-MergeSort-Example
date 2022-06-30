(deftemplate node "Fact used to store values during each step of the sorting process"
	(slot id (type SYMBOL) (default-dynamic (gensym*))) ;A unique identifier for each node
	(slot child-id (type SYMBOL) (default nil)) ;The id of the node to be merged into, if one exists
	(slot color (type SYMBOL) (default red)) ;The "color" of the node used to denote if it is being used as a parent or child
	(multislot values (type NUMBER)) ;the numbers to be sorted
)

(defrule split "Split a fact in the form (values <NUMBER>+) into individual nodes, then start sort stage"
	?list <- (values ?val $?back)
	=>
	(retract ?list)
    (assert (node (values ?val)))
	;if there are more values in the list, reassert it, otherwise start the sort stage
    (if (> (length$ $?back) 0)
        then
	    (assert (values $?back))
        else
		(printout t "Begining sort" crlf)
		(facts)

		(assert (colors red black))
        (assert (stage sort))
        )
)

(defrule make-child-nodes "Create an empty child node for 2 nodes in current color that have no child-id assigned"
	(stage sort)
	(colors ?parent-color ?child-color)
	;get 2 nodes of the correct color that don't have a child
	?parent1 <- (node (color ?parent-color) (child-id nil))
	?parent2 <- (node (color ?parent-color) (child-id nil))
	(test (neq ?parent1 ?parent2)) ;make sure parents aren't the same facts
	=>
	(bind ?cid (gensym*)); make a new unique symbol to use as the child node's id
	(assert (node (id ?cid) (color ?child-color))); create a new node
	;change the parents' child-ids to the id of the new child
	(modify ?parent1 (child-id ?cid))
	(modify ?parent2 (child-id ?cid))
)

(defrule promote-last "If only 1 node is left in the current color, promote it to the next color"
	(stage sort)
	(colors ?parent-color ?child-color)
	?parent1 <- (node (id ?pid) (color ?parent-color) (child-id nil))
	; make sure no other nodes exist with the current color and no child
	(not (node (id ?pid2&:(neq ?pid ?pid2)) (color ?parent-color) (child-id nil)))
	=>
	;change the parent's color to the next color
	(modify ?parent1 (color ?child-color))
)

(defrule append-last-parent "When only 1 parent has values, add all to end of child, and retract both parents"
	(stage sort)
	;find 2 parents of the same child where 1 has no values
	?parent1 <- (node (child-id ?cid) (values $?p1-vals))
	?parent2 <- (node (child-id ?cid) (values))
	(test (neq ?parent1 ?parent2))
	?child <- (node (id ?cid) (values $?c-vals))
	=>
	(retract ?parent1 ?parent2)
	(modify ?child (values $?c-vals $?p1-vals))
)


(defrule merge-middle "When both parents have values, pop the smaller one off and put it on the end of the child"
	(stage sort)
	?parent1 <- (node (child-id ?cid) (values ?p1-val $?p1-end))
	;parent2 won't be used aside from the comparison, so its end values don't need to be known
	?parent2 <- (node (child-id ?cid) (values ?p2-val $?))
	;make sure parents are different facts
	(test (neq ?parent1 ?parent2))
	;make sure parent1 has the smaller value at its end
	(test (<= ?p1-val ?p2-val))
	;find a node with an id matching the parents' child-id
	?child <- (node (id ?cid) (values $?c-vals))
	=>
	;remove last value on parent1
	(modify ?parent1 (values $?p1-end))
	;parent2's value isn't used, so it is unchanged
	;add parent1's last value to the end of child's values
	(modify ?child (values $?c-vals ?p1-val ))
)

(defrule swap-colors "Swap the current and next colors so another iteration can run"
	(stage sort)
	?c <- (colors ?parent-color ?child-color)
	;check that no nodes exist with the current color
	(not (node (color ?parent-color)))
	;make sure more than one node in the next color exist to prevent an infiniate loop
	(node (id ?id1) (color ?child-color))
	(node (id ?id2&:(neq ?id1 ?id2)) (color ?child-color))
	
	=>
	(retract ?c)
	(assert (colors ?child-color ?parent-color))
	(printout t "Finished iteration. Current fact list:" crlf)
	(facts)
)

(defrule finish-sort "Finish the sorting process when only 1 node remains"
	?stage <- (stage sort)
	?c <- (colors $?)
	;the final sorted node
	?last-node <- (node (id ?last-id) (values $?sorted-vals))
	;make sure no other nodes exist
	(not (node (id ?id1&:(neq ?last-id ?id1))))
	=>
	;retract the final node and create a fact named "sorted-values" with the sorted numbers
	(retract ?c ?stage ?last-node)
	(assert (sorted-values $?sorted-vals))

	(printout t "Sorting completed. Sorted values: " $?sorted-vals crlf)
)