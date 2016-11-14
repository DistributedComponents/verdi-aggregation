import socket
import re
import uuid
from select import select

def poll(sock, timeout):
    return sock in select([sock], [], [], timeout)[0]

class Client(object):
    re_aggregate_response = re.compile(r'AggregateResponse\W+([0-9]+)')
    re_level_response = re.compile(r'LevelResponse\W+([0-9]+|-)')

    def __init__(self, host, port, sock=None):
        if not sock:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock

    def send_local(self, local):
        self.sock.send('Local' + ' ' + str(local) + '\n')

    def send_send_aggregate(self):
        self.sock.send('SendAggregate\n')

    def send_broadcast(self):
        self.sock.send('Broadcast\n')
               
    def send_aggregate_request(self):
        self.sock.send('AggregateRequest\n')
        return self.process_response(self.re_aggregate_response)

    def send_level_request(self):
        self.sock.send('LevelRequest\n')
        return self.process_response(self.re_level_response)

    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def parse_response(self, data, re):
        try:
            match = re.match(data)
            return self.deserialize(match.group(1))
        except Exception as e:
            print "Parse error, data=%s" % data
            raise e
        
    def process_response(self, re):
        while True:
            data = self.sock.recv(1024).strip()
            if data != '':
                return self.parse_response(data, re)
