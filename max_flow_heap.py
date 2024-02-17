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
import heapdict as hd
from collections import deque
import pprint
import io
from functools import total_ordering 
  
  
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
    throughput = hd.heapdict()
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
        
    return throughput
 
 
def delete_zero_throughput(source, sink, auxiliary, throughput):
    while True:
        has_zero = False
        for node, cap in (dict(throughput).copy()).items():
            in_cap, out_cap = cap.thr
            thr = min(in_cap, out_cap)
            if thr == 0:
                if node == source or node == sink:
                    logging.info('Node %d (sink | source) has 0 throughput',
                                  node)
                    return False
                has_zero = True
                logging.debug('Node %d has 0 throughput. Should be deleted',
                              node)
                out_to_update = [(u, d['cap']) for u, d in (auxiliary[node].copy()).items()]
                for n, v in out_to_update:
                    logging.debug('Updating incap (%d) of node %d', 
                                  throughput[n].thr[0], n)
                    (throughput[n].thr)[0] -= v
                    logging.debug('New incap is %d', throughput[n].thr[0])
                    
                in_to_update = [(u, d[node]['cap']) for u, d in (auxiliary.copy()).items() 
                                if node in d]
                for n, v in in_to_update:
                    logging.debug('Updating outcap (%d) of node %d',
                                  throughput[n].thr[1], n)
                    (throughput[n].thr)[1] -= v
                delete_node(node, auxiliary)
                del throughput[node]
        if not has_zero:
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
                    (throughput[nn].thr)[0] -= m
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
                    (throughput[v].thr)[0] -= m
                    (throughput[u].thr)[1] += m
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
        current_thr = throughput.peekitem()

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
    
