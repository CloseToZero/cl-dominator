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
