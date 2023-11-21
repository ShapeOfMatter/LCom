# WIP

import choreography as chor
from dataclasses import dataclass
import urllib.request
import galois
import shamir
import protocol_mult

@dataclass
class Gate:
    type: str
    in1: int
    in2: int
    out: int

@dataclass
class Circuit:
    inputs: any
    outputs: any
    gates: any


def bgw(parties, inputs, circuit):

    # @chor.local_function
    # def gen_shares(inp):
    #     share1 = GF_2.Random()
    #     share2 = inp + share1
    #     return share1, share2

    # def share_inputs(p1, p2, p1_wire_vals, p2_wire_vals, inputs, wires):
    #     for inp, wire in zip(inputs, wires):
    #         share1, share2 = gen_shares[p1](inp)
    #         p1_wire_vals[wire] = share1
    #         share2_r = share2 >> p2
    #         p2_wire_vals[wire] = share2_r

    wire_vals = {p: {} for p in parties}
    p1_input_wires, p2_input_wires = circuit.inputs

    # secret share inputs
    # share_inputs(p1, p2, p1_wire_vals, p2_wire_vals, p1_inputs, p1_input_wires)
    # share_inputs(p2, p1, p2_wire_vals, p1_wire_vals, p2_inputs, p2_input_wires)

    # evaluate gates
    for g in circuit.gates:
        if g.type == 'ADD':
            for p in parties:
                wire_vals[p][g.out] = (add@p)(wire_vals[p][g.in1],
                                              wire_vals[p][g.in2])
        elif g.type == 'AND':
            in1_shares = [wire_vals[p][g.in1] for p in parties]
            in2_shares = [wire_vals[p][g.in2] for p in parties]
            results = protocol_mult.f_mult(parties, in1_shares, in2_shares)
            for p in parties:
                wire_vals[p][g.out] = results[p]
        else:
            raise Exception('Unknown gate type', g.type)

    # reconstruct outputs
    outputs = {p: [] for p in parties}

    for wire in circuit.outputs[0]:
        shares = [wire_vals[p][wire] for p in parties]
        collected_shares = {p: [share >> p for share in shares] for p in parties}
        for p in parties:
            val = (shamir.reconstruct@p)(collected_shares[p])
            outputs[p].append(val)

    return outputs



if __name__ == '__main__':
    with open('adder64.txt', 'r') as f:
        adder_txt = f.read()
    adder = parse_circuit(adder_txt)

    p1 = chor.Party('p1')
    p2 = chor.Party('p2')

    p1_inputs = [chor.constant(p1, x) for x in GF_2(int_to_bitstring(5, 64))]
    p2_inputs = [chor.constant(p2, x) for x in GF_2(int_to_bitstring(6, 64))]

    p1_out, p2_out = gmw(p1, p2, p1_inputs, p2_inputs, adder)
    p1_result = bitstring_to_int[p1](p1_out)
    p2_result = bitstring_to_int[p2](p2_out)

    print('RESULTS:')
    print(p1_result)
    print(p2_result)
