# -*- coding: utf-8 -*-
"""
The network is represented as a dictionary of dictionaries i.e.:
{ 
0: {1: {'cap': 5, 'flow': 0}, 2: {'cap': 100, 'flow': 10}},
1: {4: {'cap: 3, 'flow': 2}}
}
The above represents a network consisting of nodes 0, 1, 2,  4
and the following arcs startNode--->endNone (flow/capacity):
0---->1 (0/5)
0---->2 (10/100)
1---->4 (2/3)

The graphs are stored in files of the format:
start    end    capacity [flow]

flow is optional. So for the above graph the corresponding file is:
0 1 5
0 2 100 10
1 4 3 2

To run the checks do:

python maximum_flow <network_file> <source> <sink> [LOGLEVEL] [LOGFILE]

If input has to be entered manually, use MANUAL in place of <network_file>

LOGLEVEL is OPTIONAL and can be left out unless you also wish to specify LOGFILE
IF LOGFILE is specified the output is logged to the specified file else to the stdout. 
The mpm function can be used to pass the network to another function if desired.
"""
import time
import platform
import sys
import subprocess
import logging
import heapq as hq
from collections import deque
import pprint
import io
from functools import total_ordering 
import math
import copy
from collections.abc import MutableMapping

sys.setrecursionlimit(10000)

class FibonacciHeap(MutableMapping):

    def __init__(self, *args, **kwargs):
        '''Use the object dict'''
        self.__dict__.update(*args, **kwargs)
    # The next five methods are requirements of the ABC.
    def __setitem__(self, key, value):
        self.__dict__[key] = self.insert(value)
        self.__dict__[key].value = key
    def __getitem__(self, key):
        return self.__dict__[key]
    def __delitem__(self, key):
        del self.__dict__[key]
    def __iter__(self):
        return iter(self.__dict__)
    def __len__(self):
        return len(self.__dict__)
    def __str__(self):
        '''returns simple dict representation of the mapping'''
        return str(self.__dict__)
    def __repr__(self):
        '''echoes class, id, & reproducible representation in the REPL'''
        return '{}, FibonacciHeap({})'.format(super(FibonacciHeap, self).__repr__(), 
                                  self.__dict__)
   

    # internal node class
    class Node:
        def __init__(self, key, value):
            self.key = key
            self.value = value
            self.parent = self.child = self.left = self.right = None
            self.degree = 0
            self.mark = False
            

    # function to iterate through a doubly linked list
    def iterate(self, head):
        node = stop = head
        flag = False
        while True:
            if node == stop and flag is True:
                break
            elif node == stop:
                flag = True
            yield node
            node = node.right
    
    def dict(self):
        my_dict = {node.value:node.key.thr for node in self.iterate(self.root_list)}
        return my_dict

    # pointer to the head and minimum node in the root list
    root_list, min_node = None, None

    # maintain total node count in full fibonacci heap
    total_nodes = 0

    # return min node in O(1) time
    def find_min(self):
        return self.min_node

    # extract (delete) the min node from the heap in O(log n) time
    # amortized cost analysis can be found here (http://bit.ly/1ow1Clm)


    def extract_min(self):
        z = self.min_node
        k = copy.deepcopy(z)
        if z is not None:
            if z.child is not None:
                # attach child nodes to root list
                children = [x for x in self.iterate(z.child)]
                for i in range(0, len(children)):
                    self.merge_with_root_list(children[i])
                    children[i].parent = None
            self.remove_from_root_list(z)
            # set new min node in heap
            if z == z.right:
                self.min_node = self.root_list = None
            else:
                self.min_node = z.right
                self.consolidate()
            self.total_nodes -= 1
            del self[z.value]    
        return k

    # insert new node into the unordered root list in O(1) time
    # returns the node so that it can be used for decrease_key later
    def insert(self, key, value=None):
        n = self.Node(key, value)
        n.left = n.right = n
        self.merge_with_root_list(n)
        if self.min_node is None or n.key < self.min_node.key:
            self.min_node = n
        self.total_nodes += 1
        return n

    # modify the key of some node in the heap in O(1) time
    def decrease_key(self, x, k):
        if k > x.key:
            return None
        x.key = k
        y = x.parent
        if y is not None and x.key < y.key:
            self.cut(x, y)
            self.cascading_cut(y)
        if x.key < self.min_node.key:
            self.min_node = x

    # merge two fibonacci heaps in O(1) time by concatenating the root lists
    # the root of the new root list becomes equal to the first list and the second
    # list is simply appended to the end (then the proper min node is determined)
    def merge(self, h2):
        H = FibonacciHeap()
        H.root_list, H.min_node = self.root_list, self.min_node
        # fix pointers when merging the two heaps
        last = h2.root_list.left
        h2.root_list.left = H.root_list.left
        H.root_list.left.right = h2.root_list
        H.root_list.left = last
        H.root_list.left.right = H.root_list
        # update min node if needed
        if h2.min_node.key < H.min_node.key:
            H.min_node = h2.min_node
        # update total nodes
        H.total_nodes = self.total_nodes + h2.total_nodes
        return H

    # if a child node becomes smaller than its parent node we
    # cut this child node off and bring it up to the root list
    def cut(self, x, y):
        self.remove_from_child_list(y, x)
        y.degree -= 1
        self.merge_with_root_list(x)
        x.parent = None
        x.mark = False

    # cascading cut of parent node to obtain good time bounds
    def cascading_cut(self, y):
        z = y.parent
        if z is not None:
            if y.mark is False:
                y.mark = True
            else:
                self.cut(y, z)
                self.cascading_cut(z)

    # combine root nodes of equal degree to consolidate the heap
    # by creating a list of unordered binomial trees
    def consolidate(self):
        A = [None] * int(math.log(self.total_nodes) * 2)
        nodes = [w for w in self.iterate(self.root_list)]
        for w in range(0, len(nodes)):
            x = nodes[w]
            d = x.degree
            while A[d] != None:
                y = A[d]
                if x.key > y.key:
                    temp = x
                    x, y = y, temp
                self.heap_link(y, x)
                if self.min_node == y:
                    self.min_node = x
                A[d] = None
                d += 1
            A[d] = x
        # find new min node - no need to reconstruct new root list below
        # because root list was iteratively changing as we were moving
        # nodes around in the above loop
        for i in range(0, len(A)):
            if A[i] is not None:
                if A[i].key < self.min_node.key:
                    self.min_node = A[i]

    # actual linking of one node to another in the root list
    # while also updating the child linked list
    def heap_link(self, y, x):
        self.remove_from_root_list(y)
        y.left = y.right = y
        self.merge_with_child_list(x, y)
        x.degree += 1
        y.parent = x
        y.mark = False

    # merge a node with the doubly linked root list
    def merge_with_root_list(self, node):
        if self.root_list is None:
            self.root_list = node
        else:
            node.right = self.root_list.right
            node.left = self.root_list
            self.root_list.right.left = node
            self.root_list.right = node

    # merge a node with the doubly linked child list of a root node
    def merge_with_child_list(self, parent, node):
        if parent.child is None:
            parent.child = node
        else:
            node.right = parent.child.right
            node.left = parent.child
            parent.child.right.left = node
            parent.child.right = node

    # remove a node from the doubly linked root list
    def remove_from_root_list(self, node):
        if node == self.root_list:
            self.root_list = node.right
        node.left.right = node.right
        node.right.left = node.left

    # remove a node from the doubly linked child list
    def remove_from_child_list(self, parent, node):
        if parent.child == parent.child.right:
            parent.child = None
        elif parent.child == node:
            parent.child = node.right
            node.right.parent = parent
        node.left.right = node.right
        node.right.left = node.left

@total_ordering
class thr_array: 
    def __init__(self, arr): 
        self.thr = arr
  
    def __lt__(self, other): 
        return min(self.thr[0], self.thr[1]) < min(other.thr[0],other.thr[1])
  
    def __eq__(self, other): 
        return min(self.thr[0], self.thr[1]) == min(other.thr[0],other.thr[1])
  
    def __le__(self, other): 
        return min(self.thr[0], self.thr[1]) <= min(other.thr[0],other.thr[1])
      
    def __ge__(self, other): 
        return min(self.thr[0], self.thr[1]) >= min(other.thr[0],other.thr[1]) 
          
    def __ne__(self, other): 
        return min(self.thr[0], self.thr[1]) != min(other.thr[0],other.thr[1])
    

FORMAT = '%(asctime)-15s %(levelname)s - %(message)s'


def _to_str(network):
    out = io.StringIO()
    pp = pprint.PrettyPrinter(indent=1, stream=out)
    pp.pprint(network)
    to_return = out.getvalue()
    out.close()
    return to_return
    

def read_network_man():
    network = {}
    print("EDGE SHOULD BE IN FORMAT <start vertex> <end vertex> <capacity> <flow(optional)>")
    while True:
        str = "ENTER AN EDGE OF THE NETWORK OR ENTER --EXIT-- TO END INPUT:\t"
        inp = input(str)
        if inp != "--EXIT--":
            u, v, c, *f = map(int, inp.split())
            flow = f[0] if f else 0
            
            if u not in network:
                network[u] = {}
            if v not in network:
                network[v] = {}
        
            network[u][v] = {'cap': c, 'flow': flow}  

        else:   
            break
    
    return network
                  
        

def read_network_file(f=sys.stdin):
    network = {}
    if platform.system() == "Windows":
        task = subprocess.Popen(["type", f], stdout=subprocess.PIPE, shell=True)
    
    else:
        task = subprocess.Popen(["cat", f], stdout=subprocess.PIPE, shell=True)

    for line in task.stdout:
        
        u, v, c, *f = map(int, line.split())
        flow = f[0] if f else 0
        
        if u not in network:
            network[u] = {}
        if v not in network:
            network[v] = {}
        
        network[u][v] = {'cap': c, 'flow': flow}

    return network


def delete_node(node, network):
    for u, v in (network.copy()).items():
        if node in v:
            logging.debug('Deleting edge: (%d, %d)', u, node)
            del v[node]
        if node in network:
            logging.debug('Removing node %d from network', node)
            del network[node]

def build_residual_graph(source, sink, network):
    logging.debug('Building residual graph')
    nr = {}
    que = deque()
    que.append(source)
    visited = set()
    visited.add(source)
    while len(que) > 0:
        now = que.popleft()
        logging.debug('Processing neigbors of node %d', now)
        for e in network[now]:
            logging.debug('edge(%d, %d)', now, e)
            r = network[now][e]['cap'] - network[now][e]['flow']
            logging.debug('residual cap is %d', r)
            if now not in nr:
                nr[now] = {}
            if e not in nr:
                nr[e] = {}
            if r > 0:
                nr[now][e] = {'cap': r ,'direction': 'F'}
                logging.debug('adding (%d, %d) with cap = %d to na', now, e, r) 
            if network[now][e]['flow'] > 0:
                nr[e][now] = {'cap': network[now][e]['flow'], 'direction': 'B'}
                logging.debug('adding (%d, %d) with cap = %d to na', e, now,
                              network[now][e]['flow'])
            if e not in visited:
                que.append(e)
            visited.add(e)
    logging.info('Residual network:\n%s', _to_str(nr))
    return nr
 
 
def build_auxiliary(source, sink, network):
    logging.info('Building auxiliary')
    na = {}
    que = deque()
    que.append(source)
    vl = {source: 0} # vertex level
    visited = set()
    visited.add(source)
    while len(que) > 0:
        now = que.popleft()
        logging.debug('Processing neigbors of node %d %s', now, 
                      network[now].keys())
        na[now] = {}
        for e in network[now]:
            if e in vl and e != sink:
                continue
            logging.debug('edge(%d, %d)', now, e)
            logging.debug('adding (%d, %d) to aux', now, e)
            na[now][e] = {'cap': network[now][e]['cap'], 
                          'direction': network[now][e]['direction']}
            vl[e] = vl[now] + 1
            if e not in visited:
                que.append(e)
            visited.add(e)
            
    logging.debug('before: %s', repr(na))
    logging.debug('node layers: %s', repr(vl))
    if sink not in na:
        logging.debug('Sink not in na')
        return None
    sink_level = vl[sink]
    logging.debug('removing nodes with level >= %d (except sink node = %d)', 
                  sink_level, sink)
    complete = False
    for node in [k for k in vl if vl[k] >= sink_level]:
        if node == sink:
            complete = True
            continue
        logging.debug('We should delete node: %d', node)
        delete_node(node, na)
    logging.info('Auxiliary network:\n%s', _to_str(na))
    return na if complete else None

    
def build_level_graph(source, sink, network):
    nr = build_residual_graph(source, sink, network)
    na = build_auxiliary(source, sink, nr)
    return na

def calc_throughput(source, sink, auxiliary):
    throughput = {}
    for n, neibors in (auxiliary.copy()).items():
        if n == source:
            in_cap = sys.maxsize
        else:
            in_cap = sum([v[n]['cap'] for u, v in (auxiliary.copy()).items() 
                      if n in v])
        if n == sink:
            out_cap = sys.maxsize
        else:
            out_cap = sum([v['cap'] for _, v in (neibors.copy()).items()])
        
        throughput[n] = thr_array([in_cap, out_cap])
        logging.debug('Throughput[%d]=min(%d, %d)=%d', n, in_cap, out_cap,
                     min(in_cap, out_cap))
        
        fib_heap = FibonacciHeap()
        for u, v in throughput.items():
            fib_heap[u] = v

    return fib_heap
    
 

def delete_zero_throughput(source, sink, auxiliary, throughput):

    while min(throughput.min_node.key.thr[0], throughput.min_node.key.thr[1]) == 0:
            node, cap = throughput.min_node.value, throughput.min_node.key 
            in_cap, out_cap = cap.thr
            thr = min(in_cap, out_cap)
            if node == source or node == sink:
                logging.info('Node %d (sink | source) has 0 throughput', node)
                return False

            logging.debug('Node %d has 0 throughput. Should be deleted', node)
            out_to_update = [(u, d['cap']) for u, d in (auxiliary[node]).copy().items()]
            for n, v in out_to_update:
                tp = throughput[n].key
                logging.debug('Updating incap (%d) of node %d', 
                            tp.thr[0], n)
                (tp.thr)[0] -= v
                logging.debug('New incap is %d', tp.thr[0])
                
            in_to_update = [(u, d[node]['cap']) for u, d in (auxiliary.copy()).items() 
                            if node in d]
            for n, v in in_to_update:
                tp = throughput[n].key
                logging.debug('Updating outcap (%d) of node %d',
                            tp.thr[1], n)
                (tp.thr)[1] -= v
            delete_node(node, auxiliary)
            m = throughput.extract_min() 
            if throughput.min_node == None:
                break
              
    return True

def push(y, h, auxiliary, throughput, g):
    logging.info('Pushing %d unit from %d', h, y)
    q = deque()
    q.append(y)
    req = {u: 0 for u in auxiliary.keys() if u != y}
    req[y] = h
    flows = []
    while len(q) > 0:
        v = q.popleft()
        logging.debug('Doin %d', v)
        for n in auxiliary[v].keys():
            logging.debug(n)
            logging.debug('%s: %s', v, _to_str(auxiliary[v].keys()))
            if req[v] == 0:
                break
            if 'used' in auxiliary[v][n]:
                logging.info('(%d, %d) is used')
                continue
            m = min(auxiliary[v][n]['cap'], req[v])
            auxiliary[v][n]['cap'] -= m
            logging.debug('New capacity of (%d, %d) is %d', 
                          v, n, auxiliary[v][n]['cap'])
            if auxiliary[v][n]['cap'] == 0:
                logging.debug('Removing (%d, %d) from auxiliary', v, n)
                auxiliary[v][n]['used'] = True
                out_to_update = [u for u, d in (auxiliary[v].copy()).items()]
                for nn in out_to_update:
                    ((throughput[nn].key).thr)[0] -= m
            req[v] -= m
            req[n] += m
            logging.debug('Appending %d to queue', n)
            q.append(n)
            direction = auxiliary[v][n]['direction']
            if direction == 'B':
                start, end = n, v
                #v, n = n, v
                m = (-1) * m
            else:
                start, end = v, n
            if start not in g:
                g[start] = {}
            if end not in g[start]:
                g[start][end] = 0
            g[start][end] += m
            flows.append('(%d, %d) = %d %s' %(start, end, g[start][end], direction))
            logging.debug('Flow (%d, %d) is %d changed by %d direction %s'
                          , start, end, g[start][end], m, direction)
    logging.info('Push is done. Flows added:\n%s', _to_str(flows))


def pull(s, y, h, auxiliary, throughput, g):
    logging.info('Pulling %d unit to %d', h, y)
    q = deque([y])
    req = {u: 0 for u in auxiliary.keys() if u != y}
    req[y] = h
    flows = []
    while q:
        v = q.popleft()
        for u, d in (auxiliary.copy()).items():
            if req[v] == 0:
                break
            if v in d:
                if 'used' in auxiliary[u][v]:
                    logging.info('(%d, %d) is used', u, v)
                    continue 
                m = min(auxiliary[u][v]['cap'], req[v])
                logging.debug('Going to pull %d using (%d, %d)', m, u, v)
                auxiliary[u][v]['cap'] -= m
                if auxiliary[u][v]['cap'] == 0:
                    logging.debug('We should remove edge (%d, %d)', u, v)
                    auxiliary[u][v]['used'] = True
                    ((throughput[v].key).thr)[0] -= m
                    ((throughput[u].key).thr)[1] += m
                req[v] -= m
                req[u] += m
                q.append(u)
                direction = auxiliary[u][v]['direction']
                if direction == 'B':
                    u, v = v, u
                    m = (-1) * m
                if u not in g:
                    g[u] = {}
                if v not in g[u]:
                    g[u][v] = 0
                g[u][v] += m
                flows.append('(%d, %d) = %d %s' % (u, v, g[u][v], direction))
                logging.debug('Flow (%d, %d) is %d changed by %d direction %s'
                          , u, v, g[u][v], m, direction)
    logging.info('Flows added:\n%s', _to_str(flows))    
     
            
def construct_blocking_flow(source, sink, auxiliary, network, g):
    logging.info('Finding blocking flow')
    while True:
        throughput = calc_throughput(source, sink, auxiliary)
        ret = delete_zero_throughput(source, sink, auxiliary, throughput)

        if not ret:
            logging.debug('Flow is maximal')
            return
        if source not in auxiliary or sink not in auxiliary:
            logging.debug('Flow is maximal')
            return 
        min_thr = (None, sys.maxsize)
        
    
        current_thr = (throughput.min_node.value, throughput.min_node.key)
        if min((current_thr[1]).thr[0], (current_thr[1]).thr[1]) < min_thr[1]:
            min_thr = (current_thr[0], min((current_thr[1]).thr[0], (current_thr[1]).thr[1]))

        min_node, min_throughput = min_thr
        logging.debug('Node %d has minimum throughput %d', min_node, 
                      min_throughput)
        push(min_node, min_throughput, auxiliary, throughput, g)
        pull(source, min_node, min_throughput, auxiliary, throughput, g)
    


def flow_add(network, g):
    for u, d in (g.copy()).items():
        v = u
        for node, value in (d.copy()).items():
            network[v][node]['flow'] += value


def mpm(source, sink, network):
    i = 0
    while True:
        g = {}
        na = build_level_graph(source, sink, network)
        if not na:
            logging.info('done=yes')
            break
        construct_blocking_flow(source, sink, na, network, g)
        flow_add(network, g)
    logging.info('Maximum Flow:\n%s',_to_str(network))
    outgoin = [v for v in network[source].keys()]
    maxflow_value = sum([network[source][v]['flow'] for v in outgoin])
    logging.info('Maximum Flow value: %s', str(maxflow_value))
    return network, maxflow_value



def main(fname, source, sink):
    logging.info('=====STARTING====')
    if fname == 'MANUAL':
        network = read_network_man()
        logging.info('Network is loaded')
        mpm(source, sink, network)
    else:
        network = read_network_file(fname)
        logging.info('Network is loaded')
        mpm(source, sink, network)
        
    

if __name__ == '__main__':
    if len(sys.argv) < 4 or len(sys.argv) > 6:
        sys.exit('USAGE:\n%s graph_file source sink [loglevel] [logfile]' % sys.argv[0])
    
    loglevel = sys.argv[4] if len(sys.argv) > 4 else 'INFO'
    logfile = sys.argv[5] if len(sys.argv) == 6 else None
    
    logging.basicConfig(format=FORMAT, level=logging.getLevelName(loglevel), 
                        filename=logfile)
    
    start_time = time.time()
    
    main(sys.argv[1], int(sys.argv[2]), int(sys.argv[3]))

    print("--- %s seconds ---" % (time.time() - start_time))
    
