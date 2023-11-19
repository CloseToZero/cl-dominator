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

(defun add-node (flow-graph node)
  (let* ((old-first (first (nodes flow-graph))))
      (unless (eq old-first (car (pushnew node (nodes flow-graph) :key #'node-name :test #'string=)))
        (incf (num-of-nodes flow-graph)))
      node))

(defun add-node-by-name (flow-graph name)
  (let ((node (make-node name)))
    (add-node flow-graph node)))

(defvar *b0* (make-node "b0"))
(defvar *flow-graph* (make-flow-graph *b0*))
(defvar *b1* (add-node-by-name *flow-graph* "b1"))
(defvar *b2* (add-node-by-name *flow-graph* "b2"))
(defvar *b3* (add-node-by-name *flow-graph* "b3"))
(defvar *b4* (add-node-by-name *flow-graph* "b4"))
(defvar *b5* (add-node-by-name *flow-graph* "b5"))
(defvar *b6* (add-node-by-name *flow-graph* "b6"))
(defvar *b7* (add-node-by-name *flow-graph* "b7"))
(defvar *b8* (add-node-by-name *flow-graph* "b8"))

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

(defun random-flow-graph (num-of-nodes)
  (when (<= num-of-nodes 0)
    (error "num-of-nodes should >= 1"))
  (let* ((entry (make-node "entry"))
         (flow-graph (make-flow-graph entry))
         (count 1)
         (nodes (make-sequence 'vector num-of-nodes)))
    (setf (elt nodes 0) entry)
    (loop repeat (1- num-of-nodes)
          do (setf (elt nodes count)
                   (make-node (format nil "b~A" count)))
             (incf count))
    (loop repeat (* 3 num-of-nodes)
          do (let ((node1 (elt nodes (random count)))
                   (node2 (elt nodes (random count))))
               (unless (eq node2 entry)
                 (link-nodes node1 node2))))
    (let* ((reachable-nodes (reachable entry nil))
           (reachable-map (make-hash-table)))
      (loop for node in reachable-nodes
            do (setf (gethash node reachable-map) t))
      (loop for node in reachable-nodes
            do (add-node flow-graph node)
               (setf (predecessors node)
                     (remove-if-not #'(lambda (predecessor)
                                        (gethash predecessor reachable-map))
                                    (predecessors node)))
               (setf (successors node)
                     (remove-if-not #'(lambda (successor)
                                        (gethash successor reachable-map))
                                    (successors node)))))
    flow-graph))

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
          do (let ((node-name (node-name node)))
               (if idom
                   (setf (gethash node-name name->tree-node) (add-node-by-name tree node-name))
                   (progn (setf (node-name root) node-name)
                          (setf (gethash node-name name->tree-node) root)))))
    (loop for node being the hash-keys of idoms
            using (hash-value idom)
          when idom
            do (link-nodes (gethash (node-name idom) name->tree-node)
                           (gethash (node-name node) name->tree-node)))
    (flow-graph->graphviz tree stream)))

(defun %dominator-trees-equal (idoms1 idoms2)
  (and (eql (hash-table-size idoms1)
            (hash-table-size idoms2))
       (loop for node1 being the hash-keys of idoms1
               using (hash-value idom1)
             always
             (eq idom1 (gethash node1 idoms2)))))

(defun dominator-trees-equal (&rest more-idoms)
  (and more-idoms
       (loop for prev in more-idoms
             for next in (cdr more-idoms)
             always (%dominator-trees-equal prev next))))

(defun nodes-in-reverse-postorder (flow-graph)
  (let ((num (1- (num-of-nodes flow-graph)))
        (nums (make-hash-table))
        (nodes nil))
    (dfs (entry flow-graph)
         :postorder-fn
         (lambda (incoming-node node)
           (declare (ignore incoming-node))
           (setf (gethash node nums) num)
           (push node nodes)
           (decf num)))
    (values nodes nums)))

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

(defun dominator-cooper (flow-graph)
  (let ((change t)
        (idoms (make-hash-table)))
    ;; Indicate that the idom of entry have initialized,
    ;; laster, we will set the idom of entry to be nil.
    (setf (gethash (entry flow-graph) idoms) (entry flow-graph))
    (multiple-value-bind (nodes rpo-nums) (nodes-in-reverse-postorder flow-graph)
      (labels ((intersect (node1 node2)
                 (cond ((and (null (gethash node1 idoms))
                             (null (gethash node2 idoms)))
                        nil)
                       ((null (gethash node1 idoms)) node2)
                       ((null (gethash node2 idoms)) node1)
                       (t (loop for rpo1 = (gethash node1 rpo-nums)
                                for rpo2 = (gethash node2 rpo-nums)
                                for idom1 = (gethash node1 idoms)
                                for idom2 = (gethash node2 idoms)
                                while (/= rpo1 rpo2)
                                when (> rpo1 rpo2)
                                  do (setf node1 idom1)
                                else
                                  do (setf node2 idom2)
                                finally (return node1))))))
        (loop while change
              do (setf change nil)
                 (loop for node in nodes
                       do (let ((new-idom nil))
                            (loop for predecessor in (predecessors node)
                                  do (setf new-idom (intersect new-idom predecessor)))
                            (unless (or (null new-idom)
                                        (eq (gethash node idoms) new-idom))
                              (setf (gethash node idoms) new-idom)
                              (setf change t)))))))
    (setf (gethash (entry flow-graph) idoms) nil)
    idoms))

(defvar *purdom-doms* (dominator-purdom *flow-graph*))
(defvar *purdom-idoms* (idoms-from-doms *purdom-doms*))
;; (idoms->dominator-tree-graphviz *purdom-idoms* t)

(defvar *iterative-doms* (dominator-iterative *flow-graph*))
(defvar *iterative-idoms* (idoms-from-doms *iterative-doms*))
;; (idoms->dominator-tree-graphviz *iterative-idoms* t)

(defvar *cooper-idoms* (dominator-cooper *flow-graph*))
;; (idoms->dominator-tree-graphviz *cooper-idoms* t)

(assert (dominator-trees-equal *purdom-idoms* *iterative-idoms* *cooper-idoms*))

(defvar *random-flow-graph* (random-flow-graph 1000))
;; (flow-graph->graphviz *random-graph*)
;; (assert (dominator-trees-equal
;;          (idoms-from-doms (dominator-purdom *random-flow-graph*))
;;          (idoms-from-doms (dominator-iterative *random-flow-graph*))
;;          (dominator-cooper *random-flow-graph*)))
