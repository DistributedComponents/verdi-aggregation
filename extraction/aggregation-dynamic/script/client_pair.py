import socket
import re
import uuid
from struct import pack, unpack
from select import select

def poll(sock, timeout):
    return sock in select([sock], [], [], timeout)[0]

class SendError(Exception):
    pass

class ReceiveError(Exception):
    pass

class Client(object):
    re_aggregate_response = re.compile(r'AggregateResponse[^0-9-]+(-?[0-9]+)[^0-9-]+(-?[0-9]+)')
    re_level_response = re.compile(r'LevelResponse[^0-9-]+([0-9]+|-)')

    def __init__(self, host, port, sock=None):
        if not sock:
            self.sock = socket.socket(socket.AF_INET, socket.SOCK_STREAM)
            self.sock.connect((host, port))
        else:
            self.sock = sock

    def send_msg(self, msg):
        n = self.sock.send(pack("<I", len(msg)))
        if n < 4:
            raise SendError
        else:
            self.sock.send(msg)

    def recv_msg(self, re):
        len_bytes = self.sock.recv(4)
        if len_bytes == '':
            raise ReceiveError
        else:
            len = unpack("<I", len_bytes)[0]
            data = self.sock.recv(len)
            if data == '':
                raise ReceiveError
            else:
                return self.parse_response(data, re)

    def send_local(self, local1, local2):
        self.send_msg('Local' + ' ' + str(local1) + ' ' + str(local2))

    def send_send_aggregate(self):
        self.send_msg('SendAggregate')

    def send_broadcast(self):
        self.send_msg('Broadcast')
               
    def send_aggregate_request(self):
        self.send_msg('AggregateRequest')
        return self.recv_msg(self.re_aggregate_response)

    def send_level_request(self):
        self.send_msg('LevelRequest')
        return self.recv_msg(self.re_level_response)

    def deserialize(self, data):
        if data == '-':
            return None
        return data

    def parse_response(self, data, re):
        try:
            match = re.match(data)
            return [self.deserialize(match.group(n)) for n in (1,2)]
        except Exception as e:
            print "Parse error, data=%s" % data
            raise e
