"""Deterministic checks for reading Pu et al.'s NLOS rain-effects model.

This is a check of an explicitly stated interpretation of Eq. (18), not an
audit of the authors' implementation. Normal incidence, nonmagnetic media,
and exp(-i omega t) convention are used. Phases are dimensionless.
"""
import numpy as np


def reflection_backward(indices, phases):
    interfaces = [(a-b)/(a+b) for a, b in zip(indices[:-1], indices[1:])]
    reflection = interfaces[-1]
    for i in reversed(range(len(phases))):
        factor = np.exp(2j*phases[i])
        reflection = (interfaces[i]+reflection*factor)/(1+interfaces[i]*reflection*factor)
    return reflection


def reflection_matrix(indices, phases):
    matrix = np.eye(2, dtype=complex)
    for index, phase in zip(indices[1:-1], phases):
        c, s = np.cos(phase), np.sin(phase)
        matrix = matrix @ np.array([[c, -1j*s/index], [-1j*index*s, c]])
    b = matrix[0, 0]+matrix[0, 1]*indices[-1]
    c = matrix[1, 0]+matrix[1, 1]*indices[-1]
    return (indices[0]*b-c)/(indices[0]*b+c)


def reflection_prefix_interpretation(indices, phases):
    interfaces = [(a-b)/(a+b) for a, b in zip(indices[:-1], indices[1:])]
    reflection = interfaces[0]
    for phase, interface in zip(phases, interfaces[1:]):
        factor = np.exp(2j*phase)
        reflection = (reflection+interface*factor)/(1+reflection*interface*factor)
    return reflection


def attenuation(h, index):
    n1, n3 = 1.0, 3.0
    r12, r23 = (n1-index)/(n1+index), (index-n3)/(index+n3)
    p = np.exp(1j*index*h)  # k0=1, h is dimensionless.
    t = (2*n1/(n1+index))*(2*index/(index+n3))*p/(1+r12*r23*p*p)
    transmitted = n3/n1*abs(t)**2
    return 10*np.log10(0.75/transmitted)


def main():
    # Known closed-form controls: direct boundary and air--n=2--air slab.
    for phase, expected in ((0.0, 0.0), (np.pi/2, 0.36), (np.pi, 0.0)):
        a = reflection_backward([1., 2., 1.], [phase])
        b = reflection_matrix([1., 2., 1.], [phase])
        assert abs(abs(a)**2-expected) < 1e-12
        assert abs(a-b) < 1e-12
    assert abs(reflection_backward([1., 2., 3., 1.], [0., 0.])) < 1e-12
    print('Known closed-form controls: PASS')

    indices, phases = [1., 2., 3., 1.], [np.pi/4, np.pi/3]
    backward = reflection_backward(indices, phases)
    matrix = reflection_matrix(indices, phases)
    prefix = reflection_prefix_interpretation(indices, phases)
    assert abs(backward-matrix) < 1e-12
    print('Four-layer interpreted-prefix reflectance:', abs(prefix)**2)
    print('Four-layer backward/matrix reflectance:', abs(matrix)**2)
    print('Scope: coefficient definitions and reference planes still require review.')

    for index in (2., 2.+0.1j):
        assert abs(attenuation(0., index)) < 1e-12
        print('Local film scaling, index=', index)
        for h in (1e-3, 5e-4, 2.5e-4):
            loss = attenuation(h, index)
            print('h=', h, 'loss=', loss, 'loss/h=', loss/h, 'loss/h^2=', loss/h**2)
    assert 1.*8.**(1/3) == 2.*1.**(1/3)
    print('Simplified h=C*R^(1/3) ambiguity control: PASS')


if __name__ == '__main__':
    main()
