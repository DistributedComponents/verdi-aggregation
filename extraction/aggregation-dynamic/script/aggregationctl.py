import argparse
import os
import sys

import client

def create_client(args):
    return client.Client(args.host, int(args.port))

def aggregate(args):
    c = create_client(args)
    res = c.send_aggregate_request()
    print res

def local(args):
    c = create_client(args)
    c.send_local(args.data)

def main():
    parser = argparse.ArgumentParser()

    # global options
    parser.add_argument('--host', required=True)
    parser.add_argument('--port', required=True)
    
    # subcommands
    subparsers = parser.add_subparsers(dest='cmd', help='commands')

    aggregate_parser = subparsers.add_parser('aggregate', help='Check aggregate of node')

    local_parser = subparsers.add_parser('local', help='Issue local data to node')
    local_parser.add_argument('data', action='store', help='Data value')
    
    args = parser.parse_args()
    globals()[args.cmd](args)
    
if __name__ == '__main__':
    main()
