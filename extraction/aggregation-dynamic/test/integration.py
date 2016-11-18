import os, sys, subprocess, shutil
import unittest
sys.path.append(os.path.realpath(os.path.join(
    os.path.dirname(os.path.realpath(__file__)), '..', 'script')))
from client import Client
import time

TA = os.path.join(os.path.dirname(os.path.realpath(__file__)), '..', 'TreeAggregationMain.native')

class TestTreeAggregation(unittest.TestCase):
    clients = None
    processes = None

    def setUp(self):
        """Start up a cluster"""
        self.processes = []
        self.clients = []
        for i in range(3):
            port = 8000 + i
            args = [TA,
                    '-port', '%d' % port,
                    '-node', '0,localhost:9000',
                    '-node', '1,localhost:9001',
                    '-node', '2,localhost:9002',
                    '-me', '%d' % i]
            FNULL = open(os.devnull, 'w')
            proc = subprocess.Popen(args, stdout=FNULL, stderr=subprocess.STDOUT, close_fds=True)
            self.processes.append(proc)
            time.sleep(1)
            client = Client('localhost', port)
            self.clients.append(client)

    def tearDown(self):
        for i in range(3):
            self.processes[i].terminate()
        self.clients = None
        self.processes = None

    def test_broadcast_local(self):
        self.clients[0].send_broadcast()
        time.sleep(1)
        self.clients[0].send_local(5)
        time.sleep(1)
        self.clients[1].send_local(7)
        time.sleep(1)
        self.clients[2].send_local(2)
        time.sleep(1)
        self.clients[1].send_send_aggregate()
        self.clients[2].send_send_aggregate()
        time.sleep(1)
        self.assertEqual(self.clients[0].send_aggregate_request(), '14')

if __name__ == '__main__':
    unittest.main()

