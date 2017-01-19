#!/usr/bin/python

import argparse
import math
import client_pair

NUM_SAMPLES=4410
SHORT_NORMALIZE = (1.0/32768.0)

def create_client(args):
    return client_pair.Client(args.host, int(args.port))

def main():
    parser = argparse.ArgumentParser()

    # global options
    parser.add_argument('--host', required=True)
    parser.add_argument('--port', required=True)
    
    args = parser.parse_args()

    c = create_client(args)
    [num_nodes_str, sum_squares_str] = c.send_aggregate_request();
    num_nodes = int(num_nodes_str)
    sum_squares = int(sum_squares_str)
    print math.sqrt((sum_squares * SHORT_NORMALIZE * SHORT_NORMALIZE) / (NUM_SAMPLES * num_nodes))

if __name__ == '__main__':
    main()
