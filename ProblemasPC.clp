         CLIPS (6.30 3/17/15)
CLIPS> ;;********************************
;;MATEO GALLEGO CHAVERRA 1035920314
;;JHON SEBASTIAN MOLINA ARIAS 1036657136
;;DATE : 03/10/2020
;;VERSION: DEMO
;;PROFESOR: JORGE ELIECER GIRALDO
;;INTELIGENCIA ARTIFICAL
;;FACULTAD DE INGENIERIA 
;;POLITECNICO JAIME ISAZA CADAVID
;;*******************************
;;**************
;; DEFFUCTIONS
;; DEFFUCCIONES
;;**************
(deffunction ask-question (?question $?allowed-values)
	(printout t ?question)
	(bind ?answer (read))
	(if (lexemep ?answer)
		then (bind ?answer (lowcase ?answer)))
	(while (not (member ?answer ?allowed-values)) do
		(printout t ?question)
		(bind ?answer (read))
		(if (lexemep ?answer)
			then (bind ?answer (lowcase ?answer))))
	?answer)

(deffunction yes-or-no-p (?question)
	(bind ?response (ask-question ?question yes no y n))
	(if (or (eq ?response yes) (eq ?response y))
		then TRUE
		else FALSE)

;;***********
;;PC STATE RULES
;;ESTADOS DEL PC
;;************


(defrule normal-pc-state-conclusions ""
	(declare (salience 10))
	(working-state pc normal)
	=>
	(assert (repair "No repair needed."))
	(assert (monitor-state pc normal))
	(assert (charge-state battery charged))
	(assert (output-state pc))
	(assert (intput-state pc)))

(defrule unsatisfactory-pc-state-conclusions ""
	(declare (salience 10))
	(working-state pc unsatisfactory)
	=>
	(assert (charge-state battery charged))
	(assert (output-state pc))
	(assert (intput-state pc)))

;;*************
;;QUERY RULES
;;REGLAS DE CONSULTA 
;;*************


(defrule determine-pc-state ""
	(not (working-state pc ?))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Does the pc start (yes/no)? ")
		then
		(if (yes-or-no-p "Does the pc run normally (yes/no) ")
			then (assert (working-state pc normal))
			else (assert (working-state pc unsatisfactory)))
			else
			(assert (working-state pc does-not-start)))

(defrule determine-monitor-state ""
	(workig-state pc does-not-start)
	(not (monitor-state pc?))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Does the monitor start (yes/no)? ")
		then
		(assert (monitor-state pc start))
		else
		(assert (monitor-state pc does-not-start)))

(defrule determine-sluggishness ""
	(working-state pc unsatisfactory)
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the pc sluggish (yes/no)? ")
		then
		(assert (repair "Clean the pc."))))

(defrule determine-misfiring ""
	(working-state pc unsatisfactory)
	(not (repair ?))
	=>
	(if (yes-or-no-p "Does the pc misfire (yes/no)? ")
		then
		(assert (repair "weld point gap adjustment."))))

(defrule determine-flicker ""
	(working-state pc unsatisfactory)
	(not (monitor-state pc?))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Does the monitor fleks (yes/no)? ")
		then
		(assert (repair "Cable adjustment."))))

(defrule determine-damaged-output ""
	(working-state pc unsatisfactory)
	(not (symptom pc damaged-output | not-damaged-output))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the output of the pc damaged (yes/no)? ")
		then
		(assert (symptom pc damaged-output))
		else
		(assert (symptom pc not-damaged-output))))

(defrule determine-damaged-input ""
	(working-state pc unsatisfactory)
	(not (symptom pc damaged-input | not-damaged-input))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the input of the pc damaged (yes/no)? ")
		then
		(assert (symptom pc damaged-input))
		else
		(assert (symptom pc not-damaged-input))))

(defrule determine-state-ram ""
	(working-state pc unsatisfactory)
	(not (symptom pc damaged-ram | not-damaged-ram))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the RAM of the pc damaged (yes/no)? ")
		then
		(assert (symptom pc damaged-ram))
		else
		(assert (symptom pc not-damaged-ram))))


(defrule determine-state-motherboard ""
	(working-state pc unsatisfactory)
	(not (symptom pc damaged-motherboard | not-damaged-motherboard))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the mothedboard of the pc damaged (yes/no)? ")
		then
		(assert (symptom pc damaged-motherboard
		else
		(assert (symptom pc not-damaged-motherboard))))

(defrule determine-state-hdd ""
	(working-state pc unsatisfactory)
	(not (symptom pc damaged-hdd | not-damaged-hdd))
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the hdd of the pc damaged (yes/no)? ")
		then
		(assert (symptom pc damaged-hdd
		else
		(assert (symptom pc not-damaged-hdd))))

(defrule determine-battery-state ""
	(working-state pc does-not-start)
	(charge-state battery charged)
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the battery charged (yes/no)? ")
		then
		(assert (charge-state battery charged))
		else
		(assert (repair "Charge the battery."))
		(assert (charge-state battery dead))))


(defrule determine-battery-level ""
	(working-state pc does-not-start)
	(charge-state battery charged)
	(not (repair ?))
	=>
	(if (not (yes-or-no-p "Does the charger have any charge (yes/no)? ")
		then
		(assert (repair "Add charger."))))


(defrule determine-point-surface-state-welded ""
	(or (and (working-state pc does-not-start)
		 (symptom pc damaged-output))
	(not (repair ?))
	=>
	(bind ?response
		(ask-question "What is the state of the surface of the solder points (normal/medium/high? "
				normal medium high
	(if (eq ?response medium)
		then
		(assert (repair "Replace the points."))
		else (if(eq ?response high)
			then (assert(repair "Clean the points."))))

(defrule determine-conductivity-test ""
	(working-state pc does-not-start)
	(monitor-state pc does-not-start)
	(charge-state battery charged)
	(not (repair ?))
	=>
	(if (yes-or-no-p "Is the ignition monitor conductivity test positive (yes/no)? ")
		then
		(assert (repair "Repair the distributor monitor."))
		else
		(assert (repair "Replace the motherboard."))))

(defwule no-repais ""
	(declare (salience -10))
	(not (repair ?))
	=>
	(assert (repair "Take your pc to a technical.")))
	

;;****************
;;STARTUP AND REPAIR RULES 
;;NORMAS DE PUESTA EN MARCHA Y REPARACIÓN 
;;****************


(defrule system-banner ""
	(declare (salience 10))
	=>
	(printout t crlf crlf)
	(printout t "The PC Diagnosis Expert System")
	(printout t crlf crlf))

defrule print-repair ""
	(declare (salience 10))
	(repair ?item)
	=>
	(printout t crlf crlf)
	(printout t "Suggested Repair:")
	(printout t crlf crlf)
	(format t " %s%n%n%n" ?item))
CLIPS> 
