from collections import defaultdict
import choreography as chor
import numpy as np
import shamir


def f_mult(parties, a_shares, b_shares):
    # save x-coords for each party
    x_coords = {p: chor.locally(p, lambda x: x[0], a_shares[p]) for p in parties}

    # multiply my shares of the two numbers
    mult_results = {p: (shamir.mult@p)(a_shares[p], b_shares[p]) for p in parties}

    # distribute shares of my product
    all_h_i_js = defaultdict(list)
    for p in parties:
        h_is = chor.unlist((shamir.share@p)(chor.untup(mult_results[p])[1],
                                            len(parties)//2,
                                            len(parties)))

        for i, pp in enumerate(parties):
            all_h_i_js[pp].append(h_is[i] >> pp)

    # perform the degree reduction
    def reduce_share(x_coord, h_i_js):
        Vi = np.linalg.inv(shamir.GF(np.vander(range(1,len(parties)+1), increasing=True)))
        lambda_js = Vi[0]
        prods = [lambda_j * s[1] for lambda_j, s in zip(lambda_js, h_i_js)]
        return (x_coord, shamir.GF(prods).sum())

    outputs = {p: (reduce_share@p)(x_coords[p], all_h_i_js[p]) for p in parties}
    return outputs


if __name__ == '__main__':
    parties = [chor.Party(f'p{i}') for i in range(6)]

    a = 5
    b = 3

    a_shares_d = shamir.share(a, len(parties)//2, len(parties))
    b_shares_d = shamir.share(b, len(parties)//2, len(parties))

    a_shares = {p: chor.constant(p, s) for p, s in zip(parties, a_shares_d)}
    b_shares = {p: chor.constant(p, s) for p, s in zip(parties, b_shares_d)}

    results = f_mult(parties, a_shares, b_shares)
    result_shares = [(chor.untup(results[p])[0].val,
                      chor.untup(results[p])[1].val) for p in parties]
    print('FINAL RESULT:', shamir.reconstruct(result_shares))
