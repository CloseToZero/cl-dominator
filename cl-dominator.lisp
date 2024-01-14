(cl:defpackage :cl-dominator
  (:use :cl))

(cl:in-package :cl-dominator)

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
  (setf (gethash element (table hash-set)) t)
  hash-set)

(defun hash-set-remove (hash-set element)
  (remhash element (table hash-set))
  hash-set)

(defun hash-set-exists (hash-set element)
  (gethash element (table hash-set)))

(defmacro do-hash-set ((var hash-set-form) &body body)
  (let ((body-fn-var (gensym "body-fn"))
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
  "Returns the intersection of two hash-sets."
  (let ((result (make-hash-set :test (test hash-set-1))))
    (do-hash-set (element hash-set-1)
      (when (hash-set-exists hash-set-2 element)
        (hash-set-add result element)))
    result))

(defun special-hash-set-intersection (hash-set-1 hash-set-2)
  "Just like `hash-set-intersection', but treat nil as universal set.
We treat nil as universal set so that some algorithms
don't need to construct universal set explicitly,
which is costly for large flow graphs.
Note that the return value may be nil if the result of intersection is
the universal set."
  (cond ((and (null hash-set-1) (null hash-set-2)) nil)
        ((or (null hash-set-1) (null hash-set-2))
         (or hash-set-1 hash-set-2))
        (t (let ((result (make-hash-set :test (test hash-set-1))))
             (do-hash-set (element hash-set-1)
               (when (hash-set-exists hash-set-2 element)
                 (hash-set-add result element)))
             result))))

(defun hash-set-intersection* (&rest hash-sets)
  (if (null hash-sets)
      (make-hash-set)
      (reduce (lambda (acc hash-set)
                (hash-set-intersection acc hash-set))
              (rest hash-sets)
              :initial-value (hash-set-copy (first hash-sets)))))

(defun special-hash-set-intersection* (&rest hash-sets)
  (if (null hash-sets)
      (make-hash-set)
      (reduce (lambda (acc hash-set)
                (special-hash-set-intersection acc hash-set))
              (rest hash-sets)
              :initial-value (when (first hash-sets) (hash-set-copy (first hash-sets))))))

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

(defun depth-first-search-default-fn (node tree-parent)
  (declare (ignore node tree-parent))
  nil)

(defun depth-first-search-default-skip-fn (node tree-parent)
  (declare (ignore node tree-parent))
  nil)

(defun depth-first-search (start-node
                           &key
                             (preorder-fn #'depth-first-search-default-fn)
                             (postorder-fn #'depth-first-search-default-fn)
                             (skip-fn #'depth-first-search-default-skip-fn))
  (let ((visited (make-hash-set)))
    (labels ((rec (node tree-parent)
               (hash-set-add visited node)
               (funcall preorder-fn node tree-parent)
               (dolist (succ (successors node))
                 (unless (or (hash-set-exists visited succ)
                             (funcall skip-fn succ node))
                   (rec succ node)))
               (funcall postorder-fn node tree-parent)))
      (unless (funcall skip-fn start-node nil)
        (rec start-node nil)))
    visited))

(defun reachable (start-node &optional skip-node)
  (if (eql start-node skip-node)
      (hash-set-add (make-hash-set) start-node)
      (depth-first-search
       start-node
       :skip-fn (lambda (node tree-parent)
                  (declare (ignore tree-parent))
                  (eql node skip-node)))))

(defun nodes-in-reverse-postorder (start-node)
  (let ((nodes nil))
    (depth-first-search
     start-node
     :postorder-fn (lambda (node tree-parent)
                     (declare (ignore tree-parent))
                     (push node nodes)))
    nodes))

(defun list-with-index-table (list)
  (let ((indexes (make-hash-table))
        (index 0))
    (dolist (e list)
      (setf (gethash e indexes) index)
      (incf index))
    (values list indexes)))

(defun nodes-in-reverse-postorder-with-rpo-nums (start-node)
  (list-with-index-table (nodes-in-reverse-postorder start-node)))

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
Each node's dominators is stored as a hash-set."
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
              (entry (entry flow-graph))
              (hash-set (make-hash-set)))
            (hash-set-add hash-set entry)
            (setf (gethash entry doms-table) hash-set)
          doms-table))
       (changed t))
      ((not changed) doms-table)
    (setf changed nil)
    (dolist (node (nodes-in-reverse-postorder (entry flow-graph)))
      (let ((new-doms (apply #'special-hash-set-intersection*
                             (mapcar (lambda (node) (gethash node doms-table))
                                     (predecessors node)))))
        (hash-set-add new-doms node)
        (when (let ((old-doms (gethash node doms-table)))
                (or (null old-doms) (not (hash-set-equal new-doms old-doms))))
          (setf (gethash node doms-table) new-doms)
          (setf changed t))))))

(defun dominator-cooper (flow-graph &key verify-flow-graph)
  "Compute the dominators of each node within the FLOW-GRAPH
using the Cooper algorithm.
The result is returned as a hash-table, with nodes of FLOW-GRAPH
as key and corresponding immediate dominator as values.
Note that the entry node will always exist as a key,
and its value will be nil."
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

(defun dominator-tarjan-core (flow-graph vtree-link-nodes-fn node-with-min-semi-dom-on-path-fn)
  (let ((entry (entry flow-graph))
        (node-with-min-semi-dom-table (make-hash-table))
        (vtree-parent-table (make-hash-table))
        (semi-dom-buckets (make-hash-table))
        (nodes-vector (make-sequence 'vector (num-of-nodes flow-graph)))
        ;; NOTE: Before the semi-dominator of a node n is computed,
        ;; semi-nums-table[n] is n's preorder number, after n's semi-dominator have computed,
        ;; semi-nums-table[n] is the preorder number of n's semi-dominator.
        (semi-nums-table (make-hash-table))
        (tree-parent-table (make-hash-table))
        (idoms-table (make-hash-table)))
    (let ((next-index 0))
      (depth-first-search
       entry
       :preorder-fn (lambda (node tree-parent)
                      (setf (elt nodes-vector next-index) node)
                      (setf (gethash node semi-nums-table) next-index)
                      (setf (gethash node node-with-min-semi-dom-table) node)
                      (setf (gethash node tree-parent-table) tree-parent)
                      (incf next-index))))
    ;; Skip the node with preorder number 0 (entry)
    (loop for i from (1- (length nodes-vector)) above 0
          for node = (elt nodes-vector i)
          do
             (dolist (pred (predecessors node))
               (let ((pred-node-with-min-semi-dom-on-path
                       (funcall node-with-min-semi-dom-on-path-fn
                                pred semi-nums-table vtree-parent-table node-with-min-semi-dom-table)))
                 (when (< (gethash pred-node-with-min-semi-dom-on-path semi-nums-table)
                          (gethash node semi-nums-table))
                   (setf (gethash node semi-nums-table)
                         (gethash pred-node-with-min-semi-dom-on-path semi-nums-table)))))
             ;; At this point, we have computed the semi-dominator of node
             ;; and now semi-nums-table[node] is the preorder number of node's semi-dominator.
             (push node (gethash (elt nodes-vector (gethash node semi-nums-table)) semi-dom-buckets))
             (let ((parent (gethash node tree-parent-table)))
               (funcall vtree-link-nodes-fn parent node
                        semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
               (dolist (node (gethash parent semi-dom-buckets))
                 (let ((node-with-min-semi-dom-on-path
                         (funcall node-with-min-semi-dom-on-path-fn
                                  node semi-nums-table vtree-parent-table node-with-min-semi-dom-table)))
                   (setf (gethash node idoms-table)
                         (cond ((< (gethash node-with-min-semi-dom-on-path semi-nums-table )
                                   (gethash node semi-nums-table))
                                ;; In this case, the immediate dominator of node
                                ;; is the same as the immediate dominator of node-with-min-semi-dom-on-path,
                                ;; so we link node to node-with-min-semi-dom-on-path in idoms-table
                                ;; and resolve the link in the end.
                                node-with-min-semi-dom-on-path)
                               (t
                                ;; In this case, the immediate dominator of node is just its
                                ;; semi-dominator which is parent (the parent variable, not node's parent).
                                parent))))))
             ;; Clear the bucket so it won't affect the calcuation of other subtree branchs
             ;; with the same root node as (gethash node tree-parent-table).
             (setf (gethash (gethash node tree-parent-table) semi-dom-buckets) nil))
    ;; Now, we resolve the links in idoms-table, should do it in preoreder,
    ;; otherwise, we can't resolve these links by just one step.
    (loop for i from 1 below (length nodes-vector)
          for node = (elt nodes-vector i)
          do (unless (eql (gethash node idoms-table)
                          (elt nodes-vector (gethash node semi-nums-table)))
               (setf (gethash node idoms-table) (gethash (gethash node idoms-table) idoms-table))))
    (setf (gethash entry idoms-table) nil)
    idoms-table))

(defun dominator-tarjan-compress-path (node semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
  ;; This function assumes that vtree-parent is non-nil.
  (let ((vtree-parent (gethash node vtree-parent-table)))
    (when (gethash vtree-parent vtree-parent-table)
      (dominator-tarjan-compress-path
       vtree-parent semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
      (when (< (gethash (gethash vtree-parent node-with-min-semi-dom-table) semi-nums-table)
               (gethash (gethash node node-with-min-semi-dom-table) semi-nums-table))
        (setf (gethash node node-with-min-semi-dom-table)
              (gethash vtree-parent node-with-min-semi-dom-table)))
      (setf (gethash node vtree-parent-table)
            (gethash vtree-parent vtree-parent-table)))))

(defun dominator-tarjan-simple (flow-graph)
  (flet ((node-with-min-semi-dom-on-path (node semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
           (cond ((null (gethash node vtree-parent-table))
                  node)
                 (t
                  (dominator-tarjan-compress-path
                   node semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
                  (gethash node node-with-min-semi-dom-table))))
         (vtree-link-nodes (node-1 node-2 semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
           (declare (ignore semi-nums-table node-with-min-semi-dom-table))
           (setf (gethash node-2 vtree-parent-table) node-1)))
    (dominator-tarjan-core flow-graph #'vtree-link-nodes #'node-with-min-semi-dom-on-path)))

(defun dominator-tarjan-sophisticated (flow-graph)
  (let ((size-table (make-hash-table))
        (next-subtree-root-table (make-hash-table)))
    (flet ((node-with-min-semi-dom-on-path
               (node semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
             (cond ((null (gethash node vtree-parent-table))
                    (gethash node node-with-min-semi-dom-table))
                   (t
                    (dominator-tarjan-compress-path
                     node semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
                    (let ((vtree-parent (gethash node vtree-parent-table)))
                      (if (<= (gethash (gethash node node-with-min-semi-dom-table) semi-nums-table)
                              (gethash (gethash vtree-parent node-with-min-semi-dom-table) semi-nums-table))
                          (gethash node node-with-min-semi-dom-table)
                          (gethash vtree-parent node-with-min-semi-dom-table))))))
           (vtree-link-nodes (node-1 node-2 semi-nums-table vtree-parent-table node-with-min-semi-dom-table)
             (let ((current-subtree-root node-2))
               (loop while (< (gethash (gethash node-2 node-with-min-semi-dom-table) semi-nums-table)
                              (gethash (gethash (gethash current-subtree-root next-subtree-root-table)
                                                node-with-min-semi-dom-table)
                                       semi-nums-table 0))
                     for next-subtree-root = (gethash current-subtree-root
                                                       next-subtree-root-table)
                     for next-subtree-root-size = (gethash next-subtree-root
                                                            size-table 0)
                     do (cond ((>= (- (gethash current-subtree-root size-table)
                                      next-subtree-root-size)
                                   (- next-subtree-root-size
                                      (gethash (gethash next-subtree-root
                                                        next-subtree-root-table)
                                               size-table 0)))
                               (setf (gethash next-subtree-root vtree-parent-table)
                                     current-subtree-root)
                               (setf (gethash current-subtree-root
                                              next-subtree-root-table)
                                     (gethash next-subtree-root
                                              next-subtree-root-table)))
                              (t
                               (setf (gethash next-subtree-root
                                              size-table)
                                     (gethash current-subtree-root size-table))
                               (setf (gethash current-subtree-root vtree-parent-table) next-subtree-root
                                     current-subtree-root next-subtree-root))))
               (setf (gethash current-subtree-root node-with-min-semi-dom-table)
                     (gethash node-2 node-with-min-semi-dom-table))
               (setf (gethash node-1 size-table)
                     (+ (gethash node-1 size-table)
                        (gethash node-2 size-table)))
               (when (< (gethash node-1 size-table)
                        (* 2 (gethash node-2 size-table)))
                 (rotatef current-subtree-root
                          (gethash node-1 next-subtree-root-table)))
               (loop while current-subtree-root
                     do (setf (gethash current-subtree-root vtree-parent-table)
                              node-1)
                        (setf current-subtree-root (gethash current-subtree-root
                                                            next-subtree-root-table))))))
      (dolist (node (nodes flow-graph))
        (setf (gethash node size-table) 1))
      (dominator-tarjan-core flow-graph #'vtree-link-nodes #'node-with-min-semi-dom-on-path))))

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
;; (idoms-table->graphviz *cooper-idoms*)

(defvar *tarjan-simple-idoms* (dominator-tarjan-simple *flow-graph*))
(assert (idoms-table-equal *tarjan-simple-idoms* *expected-idoms*))
;; (idoms-table->graphviz *tarjan-simple-idoms*)

(defvar *tarjan-sophisticated-idoms* (dominator-tarjan-sophisticated *flow-graph*))
(assert (idoms-table-equal *tarjan-sophisticated-idoms* *expected-idoms*))
;; (idoms-table->graphviz *tarjan-sophisticated-idoms*)

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
                            (dominator-cooper *random-flow-graph*)
                            (dominator-tarjan-simple *random-flow-graph*)
                            (dominator-tarjan-sophisticated *random-flow-graph*)))
