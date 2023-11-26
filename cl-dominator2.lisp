(cl:defpackage :cl-dominator2
  (:use :cl))

(cl:in-package :cl-dominator2)

(defclass node ()
  ((name
    :accessor name
    :initform 'anonymous
    :initarg :name
    :type symbol)
   (successors
    :accessor successors
    :initarg :successors
    :initform nil
    :type list)
   (predecessors
    :accessor predecessors
    :initarg :predecessors
    :initform nil
    :type list)))

(defun make-node (&key name successors predecessors)
  (make-instance 'node
                 :name name
                 :successors successors
                 :predecessors predecessors))

(defclass graph ()
  ((nodes
    :accessor nodes
    :initform nil
    :type list)
   (num-of-nodes
    :accessor num-of-nodes
    :initform 0)))

(defmethod print-object ((node node) stream)
  (print-unreadable-object (node stream :type t :identity t)
    (princ (name node) stream)))

(defun make-graph ()
  (make-instance 'graph))

(defun add-node (graph node)
  (push node (nodes graph))
  (incf (num-of-nodes graph))
  graph)

(defun remove-node (graph node)
  ;; TODO linear search is slow
  (when (member node (nodes graph))
    (dolist (predecessor (predecessors node))
      (setf (successors predecessor) (delete node (successors predecessor))))
    (dolist (successor (successors node))
      (setf (predecessors successor) (delete node (predecessors successor))))
    (setf (nodes graph) (delete node (nodes graph)))
    (decf (num-of-nodes graph)))
  graph)

(defun make-graph-node (graph &rest args)
  (let ((node (apply #'make-node args)))
    (add-node graph node)
    node))

(defun link-nodes (node-1 node-2)
  (push node-2 (successors node-1))
  (push node-1 (predecessors node-2))
  (values))

(defclass flow-graph (graph)
  ((entry
    :accessor entry
    :initform (error "Must supply a entry node")
    :initarg :entry
    :type node)))

(defun make-flow-graph (&optional entry)
  (let* ((entry (or entry (make-node :name 'entry)))
         (flow-graph (make-instance 'flow-graph :entry entry)))
    (add-node flow-graph entry)
    flow-graph))

(defun graph->graphviz (graph &optional (stream t))
  (let ((visited (make-hash-table)))
    (labels ((print-node (node)
               (setf (gethash node visited) t)
               (dolist (succ (successors node))
                 (format stream "  \"~A\" -> \"~A\"~%"
                         (name node) (name succ))
                 (unless (gethash succ visited)
                   (print-node succ)))))
      (format stream "digraph G {~%")
      (dolist (node (nodes graph))
        (unless (gethash node visited)
         (print-node node)))
      (format stream "}~%"))))

(defvar *node-0* (make-node :name 'node-0))
(defvar *flow-graph* (make-flow-graph *node-0*))
(defvar *node-1* (make-graph-node *flow-graph* :name 'node-1))
(defvar *node-2* (make-graph-node *flow-graph* :name 'node-2))
(defvar *node-3* (make-graph-node *flow-graph* :name 'node-3))
(defvar *node-4* (make-graph-node *flow-graph* :name 'node-4))
(defvar *node-5* (make-graph-node *flow-graph* :name 'node-5))
(defvar *node-6* (make-graph-node *flow-graph* :name 'node-6))
(defvar *node-7* (make-graph-node *flow-graph* :name 'node-7))
(defvar *node-8* (make-graph-node *flow-graph* :name 'node-8))
(link-nodes *node-0* *node-1*)
(link-nodes *node-1* *node-2*)
(link-nodes *node-1* *node-5*)
(link-nodes *node-2* *node-3*)
(link-nodes *node-5* *node-6*)
(link-nodes *node-5* *node-8*)
(link-nodes *node-6* *node-7*)
(link-nodes *node-8* *node-7*)
(link-nodes *node-7* *node-3*)
(link-nodes *node-3* *node-4*)

(defclass hash-set ()
  ((table
    :accessor table
    :initform (error "Must supply a table")
    :initarg :table)
   (test
    :accessor test
    :initform (error "Must supply the test function of the table")
    :initarg :test)))

(defun make-hash-set (&key (test #'equal))
  (make-instance 'hash-set
                 :table (make-hash-table :test test)
                 :test test))

(defun hash-set-count (hash-set)
  (hash-table-count (table hash-set)))

(defun hash-set-add (hash-set element)
  (setf (gethash element (table hash-set)) t))

(defun hash-set-remove (hash-set element)
  (remhash element (table hash-set)))

(defun hash-set-exists (hash-set element)
  (gethash element (table hash-set)))

(defmacro do-hash-set ((var hash-set-form) &body body)
  (let ((body-fn-var (gensym "body-fn-var"))
        (element-var (gensym "element"))
        (value-var (gensym "value")))
    `(let ((,body-fn-var (lambda (,var) ,@body)))
       (maphash (lambda (,element-var ,value-var)
                  (declare (ignore ,value-var))
                  (funcall ,body-fn-var ,element-var))
                (table ,hash-set-form)))))

;; It seems not a good idea to specialize on `print-object',
;; the number of hash-set elements may be large.
(defun print-hash-set (hash-set &optional (stream t))
  (format stream "{")
  (let ((first t))
    (do-hash-set (element hash-set)
      (unless first (format stream " "))
      (prin1 element stream)
      (setf first nil)))
  (format stream "}"))

(defun hash-set-copy (hash-set)
  (let ((result (make-hash-set)))
    (do-hash-set (element hash-set)
      (hash-set-add result element))
    result))

(defun hash-set-difference (hash-set-1 hash-set-2)
  (let ((result (make-hash-set :test (test hash-set-1))))
    (do-hash-set (element hash-set-1)
      (unless (hash-set-exists hash-set-2 element)
        (hash-set-add result element)))
    result))

(defun hash-set-intersection (hash-set-1 hash-set-2)
  (let ((result (make-hash-set :test (test hash-set-1))))
    (do-hash-set (element hash-set-1)
      (when (hash-set-exists hash-set-2 element)
        (hash-set-add result element)))
    result))

(defun hash-set-intersection* (&rest hash-sets)
  (if (null hash-sets)
      (make-hash-set)
      (reduce (lambda (acc hash-set)
                (hash-set-intersection acc hash-set))
              (rest hash-sets)
              :initial-value (hash-set-copy (first hash-sets)))))

(defun hash-set-notany (hash-set predicate &optional ignore)
  (block nil
    (do-hash-set (element hash-set)
      (when (and (or (null ignore)
                     (not (funcall ignore element)))
                 (funcall predicate element))
        (return nil)))
    t))

(defun hash-set-every (hash-set predicate &optional ignore)
  (block nil
    (do-hash-set (element hash-set)
      (when (and (or (null ignore)
                     (not (funcall ignore element)))
                 (not (funcall predicate element)))
        (return nil)))
    t))

(defun hash-set-equal (hash-set-1 hash-set-2)
  (and (eql (hash-set-count hash-set-1)
            (hash-set-count hash-set-2))
       (hash-set-every hash-set-1
                       (lambda (element)
                         (hash-set-exists hash-set-2 element)))))

(defun reachable (node &optional ignore-node)
  (let ((visited (make-hash-set)))
    (labels ((rec (node)
               (hash-set-add visited node)
               (dolist (succ (successors node))
                 (unless (or (hash-set-exists visited succ)
                             (eql succ ignore-node))
                   (rec succ)))))
      (if (eql node ignore-node)
          (hash-set-add visited node)
          (rec node)))
    visited))

(defun nodes-in-reverse-postorder (start-node)
  ;; TODO build a fine abstraction to remove duplicates.
  (let ((nodes nil)
        (visited (make-hash-set)))
    (labels ((rec (node)
               (hash-set-add visited node)
               (dolist (succ (successors node))
                 (unless (hash-set-exists visited succ)
                   (rec succ)))
               (push node nodes)))
      (rec start-node))
    nodes))

(defun nodes-in-reverse-postorder-with-rpo-nums (start-node)
  (let ((nodes (nodes-in-reverse-postorder start-node))
        (rpo-nums (make-hash-table))
        (rpo-num 0))
    (dolist (node nodes)
      (setf (gethash node rpo-nums) rpo-num)
      (incf rpo-num))
    (values nodes rpo-nums)))

(defun verify-flow-graph (flow-graph &optional (allow-link-to-entry t))
  "Verify whether the FLOW-GRAPH is valid, signals an error if it's invalid.
A FLOW-GRAPH is valid if and only if the following are true:
1. Every nodes of FLOW-GRAPH is reachabled from the entry node.
2. If ALLOW-LINK-TO-ENTRY is nil, there are no nodes link to the entry node."
  (unless allow-link-to-entry
    (assert (null (predecessors (entry flow-graph)))))
  (let ((reachable (reachable (entry flow-graph))))
    (every (lambda (node) (hash-set-exists reachable node))
           (nodes flow-graph)))
  (values))

(verify-flow-graph *flow-graph* nil)

(defun dominator-purdom (flow-graph)
  "Compute the dominators of each node within the FLOW-GRAPH
using the Purdom algorithm.
The result is returned as a hash-table, with nodes of FLOW-GRAPH
as key and corresponding dominators as values.
Each node's dominators is stored as hash-set."
  (let ((result (make-hash-table)))
    (dolist (node (nodes flow-graph))
      (setf (gethash node result) (make-hash-set)))
    (hash-set-add (gethash (entry flow-graph) result) (entry flow-graph))
    (dolist (node (nodes flow-graph))
      (let ((reachable-before (reachable (entry flow-graph)))
            (reachable-after (reachable (entry flow-graph) node)))
        (do-hash-set (node-2 (hash-set-difference reachable-before
                                                  reachable-after))
          (hash-set-add (gethash node-2 result) node))))
    result))

(defun dominator-iterative (flow-graph &key verify-flow-graph)
  "Compute the dominators of each node within the FLOW-GRAPH
using the iterative algorithm.
The format of the result is the same as `dominator-purdom'."
  ;; Verify the flow-graph, the iterative algorithm doesn't allow the
  ;; entry node has any predecessors.
  (when verify-flow-graph (verify-flow-graph flow-graph nil))
  (do ((doms-table
        (let ((doms-table (make-hash-table))
              (entry (entry flow-graph)))
          (dolist (node (nodes flow-graph))
            (let ((hash-set (make-hash-set)))
              (cond ((eql node entry)
                     (hash-set-add hash-set node))
                    (t
                     (dolist (node (nodes flow-graph))
                       (hash-set-add hash-set node))))
              (setf (gethash node doms-table) hash-set)))
          doms-table))
       (changed t))
      ((not changed) doms-table)
    (setf changed nil)
    (dolist (node (nodes-in-reverse-postorder (entry flow-graph)))
      (let ((new-doms (apply #'hash-set-intersection*
                             (mapcar (lambda (node) (gethash node doms-table))
                                     (predecessors node)))))
        (hash-set-add new-doms node)
        (unless (hash-set-equal new-doms (gethash node doms-table))
          (setf (gethash node doms-table) new-doms)
          (setf changed t))))))

(defun dominator-cooper (flow-graph &key verify-flow-graph)
  (when verify-flow-graph (verify-flow-graph flow-graph nil))
  (do ((idoms-table
        (let ((idoms-table (make-hash-table))
              (entry (entry flow-graph)))
          ;; Set the immediate dominator of entry to be itself to
          ;; simplify the implementation, we will set entry's
          ;; immediate dominator to nil in the end.
          (setf (gethash entry idoms-table) entry)
          idoms-table))
       (changed t))
      ((not changed)
       (setf (gethash (entry flow-graph) idoms-table) nil)
       idoms-table)
    (labels ((intersection-by-rpo-nums (idoms-table rpo-nums node-1 node-2)
               (do* ((head-1 node-1)
                     (head-2 node-2)
                     (head-1-rpo-num
                      (gethash head-1 rpo-nums)
                      (gethash head-1 rpo-nums))
                     (head-2-rpo-num
                      (gethash head-2 rpo-nums)
                      (gethash head-2 rpo-nums)))
                    ((= head-1-rpo-num head-2-rpo-num) head-1)
                 (cond ((> head-1-rpo-num head-2-rpo-num)
                        (setf head-1 (gethash head-1 idoms-table)))
                       ((> head-2-rpo-num head-1-rpo-num)
                        (setf head-2 (gethash head-2 idoms-table))))))
             (intersection-by-rpo-nums* (idoms-table rpo-nums &rest nodes)
               (let ((inited-nodes (remove-if-not (lambda (node) (gethash node idoms-table)) nodes)))
                 ;; Special case: INITED-NODES has only one element,
                 ;; this means the node has only one processed
                 ;; predecessor. In this case, `reduce' returns the
                 ;; processed predecessor, and it is correct.
                 (when inited-nodes
                   (reduce (lambda (acc node) (intersection-by-rpo-nums idoms-table rpo-nums acc node))
                           inited-nodes)))))
      (setf changed nil)
      (multiple-value-bind (nodes rpo-nums) (nodes-in-reverse-postorder-with-rpo-nums (entry flow-graph))
        (dolist (node nodes)
          (let ((new-idom (apply #'intersection-by-rpo-nums* idoms-table rpo-nums (predecessors node))))
            (unless (or (null new-idom) (eql (gethash node idoms-table) new-idom))
              (setf (gethash node idoms-table) new-idom)
              (setf changed t))))))))

(defun doms-table->idoms-table (doms-table)
  "Convert dominators to immediate dominators.
DOMS-TABLE is a hash table with nodes as keys and
corresponding dominators hash-set as values.
Returns immediate dominators as a hash table with nodes as keys
and corresponding immediate dominator as values.
Note that the entry node will always exist as a key,
and its value will be nil."
  (let ((result (make-hash-table)))
    (maphash
     (lambda (node doms)
       (let ((value-set nil))
         (do-hash-set (dom doms)
           (when (and (not (eql dom node))
                      (hash-set-notany
                       doms
                       (lambda (dom-2)
                         (hash-set-exists (gethash dom-2 doms-table) dom))
                       (lambda (dom-2)
                         (or (eql dom-2 dom)
                             (eql dom-2 node)))))
             (setf (gethash node result) dom)
             (setf value-set t)))
         (unless value-set (setf (gethash node result) nil))))
     doms-table)
    result))

(defun idoms-table-equal (idoms-table-1 idoms-table-2)
  (and (eql (hash-table-size idoms-table-1)
            (hash-table-size idoms-table-2))
       (let ((result t))
         (block nil
           (maphash (lambda (node idom)
                      (unless (eql (gethash node idoms-table-2) idom)
                        (setf result nil)
                        (return)))
                    idoms-table-1))
         result)))

(defun idoms-table-equal* (&rest idoms-tables)
  (every (lambda (idoms-table-1 idoms-table-2)
           (idoms-table-equal idoms-table-1 idoms-table-2))
         idoms-tables (cdr idoms-tables)))

(defun idoms-table->graph (idoms-table)
  (let ((tree (make-graph))
        (to-tree-node (make-hash-table)))
    (maphash (lambda (node idom)
               (declare (ignore idom))
               (setf (gethash node to-tree-node)
                     (make-graph-node tree :name (name node))))
             idoms-table)
    (maphash (lambda (node idom)
               (let ((node-tree-node (gethash node to-tree-node))
                     (idom-tree-node (gethash idom to-tree-node)))
                 (when idom-tree-node
                   (link-nodes idom-tree-node node-tree-node))))
             idoms-table)
    (values tree to-tree-node)))

(defun idoms-table->graphviz (idoms-table)
  (graph->graphviz (idoms-table->graph idoms-table)))

(defvar *expected-idoms*
  (let ((table (make-hash-table)))
    (dolist (pair (list (list *node-0* nil)
                        (list *node-1* *node-0*)
                        (list *node-2* *node-1*)
                        (list *node-3* *node-1*)
                        (list *node-4* *node-3*)
                        (list *node-5* *node-1*)
                        (list *node-6* *node-5*)
                        (list *node-7* *node-5*)
                        (list *node-8* *node-5*)))
      (setf (gethash (first pair) table) (second pair)))
    table))

(defvar *purdom-doms* (dominator-purdom *flow-graph*))
(defvar *purdom-idoms* (doms-table->idoms-table *purdom-doms*))
(assert (idoms-table-equal *purdom-idoms* *expected-idoms*))
;; (idoms-table->graphviz *purdom-idoms*)

(defvar *iterative-doms* (dominator-iterative *flow-graph*))
(defvar *iterative-idoms* (doms-table->idoms-table *iterative-doms*))
(assert (idoms-table-equal *iterative-idoms* *expected-idoms*))
;; (idoms-table->graphviz *iterative-idoms*)

(defvar *cooper-idoms* (dominator-cooper *flow-graph*))
(assert (idoms-table-equal *cooper-idoms* *expected-idoms*))
(idoms-table->graphviz *cooper-idoms*)

(defun make-random-flow-graph (expected-num-of-nodes expected-num-of-edges)
  (when (<= expected-num-of-nodes 0)
    (error "expected-num-of-nodes should >= 1."))
  (let* ((entry (make-node :name 'entry))
         (flow-graph (make-flow-graph entry))
         (nodes (make-sequence 'vector expected-num-of-nodes)))
    (setf (elt nodes 0) entry)
    (dotimes (i (1- expected-num-of-nodes))
      (setf (elt nodes (+ i 1))
            (make-graph-node flow-graph :name (gensym (format nil "NODE-~A" (+ i 1))))))
    (dotimes (i expected-num-of-edges)
      (let ((node-1 (elt nodes (random expected-num-of-nodes)))
            (node-2 (elt nodes (random expected-num-of-nodes))))
        (unless (or (eql node-2 entry)
                    (member node-2 (successors node-1)))
          (link-nodes node-1 node-2))))
    (let ((reachable (reachable entry)))
      (map nil (lambda (node) (unless (hash-set-exists reachable node) (remove-node flow-graph node))) nodes))
    (verify-flow-graph flow-graph nil)
    flow-graph))

(defvar *random-flow-graph* (let ((count 1000)) (make-random-flow-graph count (* 3 count))))
(assert (idoms-table-equal* (doms-table->idoms-table (dominator-purdom *random-flow-graph*))
                            (doms-table->idoms-table (dominator-iterative *random-flow-graph*))
                            (dominator-cooper *random-flow-graph*)))
