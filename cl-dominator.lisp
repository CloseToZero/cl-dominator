(cl:defpackage :cl-dominator
  (:use :cl))

(cl:in-package :cl-dominator)

(defclass flow-graph ()
  ((entry :accessor entry
          :initform (error "Must supply a entry node")
          :initarg :entry)
   (nodes :accessor nodes
          :initform nil)))

(defclass node ()
  ((name :accessor node-name
         :initform (error "Must supply a name")
         :initarg :name)
   (successors :accessor successors :initform nil)
   (predecessors :accessor predecessors :initform nil)))

(defmethod print-object ((node node) stream)
  (print-unreadable-object (node stream :type t :identity t)
    (princ (node-name node) stream)))

(defun link-nodes (a b)
  (pushnew b (successors a))
  (pushnew a (predecessors b)))

(defun make-node (name)
  (make-instance 'node :name name))

(defun make-flow-graph (entry)
  (let ((flow-graph (make-instance 'flow-graph :entry entry)))
    (push entry (nodes flow-graph))
    flow-graph))

(defun add-node (graph name)
  (let ((node (make-node name)))
    (pushnew node (nodes graph) :key #'node-name :test #'string=)
    node))

(defvar *b0* (make-node "b0"))
(defvar *flow-graph* (make-flow-graph *b0*))
(defvar *b1* (add-node *flow-graph* "b1"))
(defvar *b2* (add-node *flow-graph* "b2"))
(defvar *b3* (add-node *flow-graph* "b3"))
(defvar *b4* (add-node *flow-graph* "b4"))
(defvar *b5* (add-node *flow-graph* "b5"))
(defvar *b6* (add-node *flow-graph* "b6"))
(defvar *b7* (add-node *flow-graph* "b7"))
(defvar *b8* (add-node *flow-graph* "b8"))

(link-nodes *b0* *b1*)
(link-nodes *b1* *b2*)
(link-nodes *b1* *b5*)
(link-nodes *b2* *b3*)
(link-nodes *b5* *b6*)
(link-nodes *b5* *b8*)
(link-nodes *b6* *b7*)
(link-nodes *b8* *b7*)
(link-nodes *b7* *b3*)
(link-nodes *b3* *b4*)

(defun flow-graph->graphviz (flow-graph stream)
  (let ((visited (make-hash-table)))
    (labels ((convert-node (node)
               (setf (gethash node visited) t)
               (loop for succ in (successors node)
                     do (format stream "  ~A -> ~A~%" (node-name node) (node-name succ))
                        (unless (gethash succ visited)
                          (convert-node succ)))))
      (format stream "digraph G {~%")
      (convert-node (entry flow-graph))
      (format stream "}~%"))))

(defun reachable (node black-node)
  (let ((result nil)
        (visited (make-hash-table)))
    (labels ((rec (node)
               (push node result)
               (setf (gethash node visited) t)
               (unless (eq node black-node)
                 (loop for succ in (successors node)
                       do (unless (or (eq succ black-node)
                                      (gethash succ visited))
                            (rec succ))))))
      (rec node))
    result))

(defun dominator-purdom (flow-graph)
  (let ((doms (make-hash-table))
        (entry (entry flow-graph))
        (nodes (nodes flow-graph)))
    (setf (gethash entry doms) (list entry))
    (loop for node in nodes
          do (let ((no-reachable-nodes (set-difference nodes (reachable entry node))))
               (loop for no-reachable-node in no-reachable-nodes
                     do (push node (gethash no-reachable-node doms)))))
    doms))

(defvar *doms* (dominator-purdom *flow-graph*))

(defun idom-from-doms (target doms)
  (let ((target-doms (gethash target doms)))
    (find-if (lambda (candidate)
               (when (not (eq candidate target))
                 (notany (lambda (node)
                           (and (member candidate (gethash node doms))
                                (not (eq candidate node))
                                (not (eq node target))))
                         target-doms)))
             target-doms)))

(defun idoms-from-doms (doms)
  (let ((idoms (make-hash-table)))
    (loop for node being the hash-keys of doms
          for idom = (idom-from-doms node doms)
            do (setf (gethash node idoms) idom))
    idoms))

(defvar *idoms* (idoms-from-doms *doms*))

(defun idoms->dominator-tree-graphviz (idoms stream)
  ;; abuse flow-graph as tree.
  (let* ((root (make-node "entry"))
         (tree (make-flow-graph root))
         (name->tree-node (make-hash-table :test #'equal)))
    (loop for node being the hash-keys of idoms
            using (hash-value idom)
          do
             (let* ((node-name (node-name node))
                    (tree-node (add-node tree node-name)))
               (if idom
                   (setf (gethash node-name name->tree-node) tree-node)
                   (progn (setf (node-name root) node-name)
                          (setf (gethash node-name name->tree-node) root)))))
    (loop for node being the hash-keys of idoms
            using (hash-value idom)
          when idom
            do (link-nodes (gethash (node-name idom) name->tree-node)
                           (gethash (node-name node) name->tree-node)))
    (flow-graph->graphviz tree stream)))
