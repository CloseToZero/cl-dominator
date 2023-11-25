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

(defun hash-set-difference (hash-set-1 hash-set-2)
  (assert (eql (test hash-set-1) (test hash-set-2)))
  (let ((result (make-hash-set :test (test hash-set-1))))
    (do-hash-set (element hash-set-1)
      (unless (hash-set-exists hash-set-2 element)
        (hash-set-add result element)))
    result))

(defun hash-set-notany (hash-set predicate &optional ignore)
  (block nil
    (do-hash-set (element hash-set)
      (when (and (or (null ignore)
                     (not (funcall ignore element)))
                 (funcall predicate element))
        (return nil)))
    t))

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
  "Compute the dominators of each node within the FLOW-GRAPH.
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

(defvar *purdom-doms* (dominator-purdom *flow-graph*))
(defvar *purdom-idoms* (doms-table->idoms-table *purdom-doms*))
(idoms-table->graphviz *purdom-idoms*)
