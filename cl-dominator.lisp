(cl:defpackage :cl-dominator
  (:use :cl))

(cl:in-package :cl-dominator)

(defclass flow-graph ()
  ((entry :accessor entry
          :initform (error "Must supply a entry node")
          :initarg :entry)
   (nodes :accessor nodes
          :initform nil)
   (num-of-nodes :accessor num-of-nodes :initform 0)))

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

(defun add-node (flow-graph name)
  (let ((node (make-node name)))
    (let* ((old-first (first (nodes flow-graph))))
      (unless (eq old-first (car (pushnew node (nodes flow-graph) :key #'node-name :test #'string=)))
        (incf (num-of-nodes flow-graph)))
      node)))

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

(defun dfs (node &key preorder-fn postorder-fn)
  (let ((visited (make-hash-table)))
    (labels ((rec (incoming-node node)
               (setf (gethash node visited) t)
               (let ((preorder-fn-result nil))
                 (when preorder-fn
                   (setf preorder-fn-result (funcall preorder-fn incoming-node node)))
                 (unless (eql preorder-fn-result :skip)
                   (loop for succ in (successors node)
                         unless (gethash succ visited)
                           do (rec node succ))))
               (when postorder-fn
                 (funcall postorder-fn incoming-node node))))
      (rec nil node))))

(defun reachable (node black-node)
  (let ((result nil))
    (dfs node
         :preorder-fn
         (lambda (incoming-node node)
           (when (or (not (eq node black-node))
                     (null incoming-node))
             (push node result))
           (when (eq node black-node)
             :skip)))
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

(defun reverse-postorder-nums (flow-graph)
  (let ((num (1- (num-of-nodes flow-graph)))
        (nums (make-hash-table)))
    (dfs (entry flow-graph)
         :postorder-fn
         (lambda (incoming-node node)
           (declare (ignore incoming-node))
           (setf (gethash node nums) num)
           (decf num)))
    nums))

(defun nodes-in-reverse-postorder (flow-graph)
  (let ((nums (reverse-postorder-nums flow-graph)))
    (sort (copy-list (nodes flow-graph))
          (lambda (node1 node2)
            (< (gethash node1 nums)
               (gethash node2 nums))))))

(defun dominator-iterative (flow-graph)
  (let ((change t)
        (entry (entry flow-graph))
        (nodes (nodes-in-reverse-postorder flow-graph))
        (doms (make-hash-table)))
    (loop for node in nodes
          do (cond ((eq node entry)
                    (setf (gethash node doms) (list entry)))
                   (t (setf (gethash node doms) nodes))))
    (loop while change
          do (setf change nil)
             (loop for node in nodes
                   do  (let ((result (let ((predecessor (car (predecessors node))))
                                       (when predecessor
                                         (gethash predecessor doms)))))
                         (loop for predecessor in (cdr (predecessors node))
                               do (setf result (intersection result (gethash predecessor doms))))
                         (setf result (union result (list node)))
                         (unless (null (set-exclusive-or result (gethash node doms)))
                           (setf (gethash node doms) result)
                           (setf change t)))))
    doms))

(defvar *purdom-doms* (dominator-purdom *flow-graph*))
(defvar *purdom-idoms* (idoms-from-doms *purdom-doms*))
;; (idoms->dominator-tree-graphviz *purdom-idoms* t)

(defvar *iterative-doms* (dominator-iterative *flow-graph*))
(defvar *iterative-idoms* (idoms-from-doms *iterative-doms*))
;; (idoms->dominator-tree-graphviz *iterative-idoms* t)
