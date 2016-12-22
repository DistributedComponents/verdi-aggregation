import argparse
import os
import sys

import client

def create_client(args):
    return client.Client(args.hostname, int(args.port))

def aggregate(args):
    c = create_client(args)
    res = c.send_aggregate_request()
    print res

def main():
    parser = argparse.ArgumentParser()

    # global options
    parser.add_argument('--hostname', required=True)
    parser.add_argument('--port', required=True)
    
    # subcommands
    subparsers = parser.add_subparsers(dest='cmd', help='commands')

    status_parser = subparsers.add_parser('aggregate', help='Check aggregate of node')
    
    args = parser.parse_args()
    globals()[args.cmd](args)
    
if __name__ == '__main__':
    main()
