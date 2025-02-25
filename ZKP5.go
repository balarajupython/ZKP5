


//Package details
package ZKP5


import (
   "bufio"
   "bytes"
   "crypto/rand"
   "errors"
   "fmt"
   "io"
   "math/big"
   "os"
   "regexp"
   "strconv"
   "strings"
)

// NewPolynomialField creates a new PolynomialField with the given FiniteField
func NewPolynomialField(f Fq) PolynomialField {
	return PolynomialField{
		f,
	}
}
// NewFq generates a new Fq
func NewFq1() Fq {
	q, _ := new(big.Int).SetString("21888242871839275222246405745257275088548364400416034343698204186575808495617", 10)
	return Fq{
		q,
	}
}

func (pf PolynomialField) R1CSToQAP(a, b, c [][]*big.Int) ([][]*big.Int, [][]*big.Int, [][]*big.Int, []*big.Int) {
	aT := Transpose(a)
	bT := Transpose(b)
	cT := Transpose(c)
	var alphas [][]*big.Int
	for i := 0; i < len(aT); i++ {
		alphas = append(alphas, pf.LagrangeInterpolation(aT[i]))
	}
	var betas [][]*big.Int
	for i := 0; i < len(bT); i++ {
		betas = append(betas, pf.LagrangeInterpolation(bT[i]))
	}
	var gammas [][]*big.Int
	for i := 0; i < len(cT); i++ {
		gammas = append(gammas, pf.LagrangeInterpolation(cT[i]))
	}
	z := []*big.Int{big.NewInt(int64(1))}
	for i := 1; i < len(alphas)-1; i++ {
		z = pf.Mul(
			z,
			[]*big.Int{
				pf.F.Neg(
					big.NewInt(int64(i))),
				big.NewInt(int64(1)),
			})
	}
	return alphas, betas, gammas, z
}
func GetProofResponseFromProof(proof Proof) ProofResponse {
	var proofResponse ProofResponse
	proofResponse = ProofResponse{}

	proofResponse.Alpha_betta = proof.alpha_betta.String()
	proofResponse.A_total = proof.A_total.String()
	proofResponse.B_total = proof.B_total.String()
	proofResponse.CLI0T01 = proof.CLI0T01.String()
	proofResponse.C_hxtx_delta_AS_ADD_BS_SUB_RSdelta = proof.C_hxtx_delta_AS_ADD_BS_SUB_RSdelta.String()
	proofResponse.C_total = proof.C_total.String()
	proofResponse.Hx_Tx = proof.Hx_Tx.String()
	proofResponse.PIA_ADD_ALPHA = ConvertBigIntArrayToCustomArray(proof.PIA_ADD_ALPHA)
	proofResponse.PIA_ADD_Betta = ConvertBigIntArrayToCustomArray(proof.PIA_ADD_Betta)
	proofResponse.PIC1 = ConvertBigIntArrayToCustomArray(proof.PIC1)
	proofResponse.PiA = ConvertBigIntArrayToCustomArray(proof.PiA)
	proofResponse.PiA1 = ConvertBigIntArrayToCustomArray(proof.PiA1)
	proofResponse.PiAp = ConvertBigIntArrayToCustomArray(proof.PiAp)
	proofResponse.PiB1_G2 = [3][2]string{}

	for index, value := range proof.PiB1_G2 {
		proofResponse.PiB1_G2[index] = [2]string{value[0].String(), value[1].String()}
	}
	return proofResponse
}
func GenerateTrustedSetup(witnessLength int, circuit Circuit, u, v, w [][]*big.Int, alpha *big.Int, betta *big.Int, gamma *big.Int, delta *big.Int, X_value *big.Int, R_value *big.Int, S_value *big.Int) (Setup, error) {

	var setup Setup
	var err error

	setup.Toxic.alpha = alpha

	setup.Toxic.betta = betta

	setup.Toxic.gamma = gamma

	setup.Toxic.delta = delta

	setup.Toxic.x = X_value

	setup.Toxic.r = R_value

	setup.Toxic.s = S_value

	for i := 0; i < len(circuit.Signals); i++ {
		Ui_into_x_value := Utils.PF.Eval(u[i], setup.Toxic.x)
		Vi_into_x_value := Utils.PF.Eval(v[i], setup.Toxic.x)
		Wi_into_x_value := Utils.PF.Eval(w[i], setup.Toxic.x)

		Betta_INTO_UI_X := Utils.FqR.Mul(setup.Toxic.betta, Ui_into_x_value)
		Alpha_INTO_VI_X := Utils.FqR.Mul(setup.Toxic.alpha, Vi_into_x_value)

		Betta_INTO_UI_X_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, Betta_INTO_UI_X)
		Alpha_INTO_VI_X_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, Alpha_INTO_VI_X)
		Alpha_INTO_VI_X_G2 := Utils.Bn.G2.MulScalar(Utils.Bn.G2.G, Alpha_INTO_VI_X)
		WI_INTO_X := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, Wi_into_x_value)

		setup.Pk.A = append(setup.Pk.A, Betta_INTO_UI_X_G1)
		setup.Pk.B = append(setup.Pk.B, Alpha_INTO_VI_X_G1)
		setup.Pk.C = append(setup.Pk.C, WI_INTO_X)

		setup.Pk.B_into_G2 = append(setup.Pk.B_into_G2, Alpha_INTO_VI_X_G2)

		Li := Utils.FqR.Add(Utils.FqR.Add(Betta_INTO_UI_X, Alpha_INTO_VI_X), Wi_into_x_value)

		setup.Toxic.LI = append(setup.Toxic.LI, Li)

		LI_into_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, Li)
		setup.Pk.Li_B_Ui_X_A_Vi_X_Wi_X = append(setup.Pk.Li_B_Ui_X_A_Vi_X_Wi_X, LI_into_G1)

	}

	// fmt.Println("done z")
	zpol := []*big.Int{big.NewInt(int64(1))}
	for i := 1; i < len(u)-1; i++ {
		zpol = Utils.PF.Mul(
			zpol, []*big.Int{Utils.FqR.Neg(
				big.NewInt(int64(i))),
				big.NewInt(int64(1)),
			})
	}

	// setup.Pk.Z = zpol

	zt := Utils.PF.Eval(zpol, setup.Toxic.x)
	setup.Pk.Z = zt

	setup.Toxic.alpha_into_G1 = Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, setup.Toxic.alpha)
	setup.Toxic.betta_into_G1 = Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, setup.Toxic.betta)
	setup.Toxic.delta_into_G1 = Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, setup.Toxic.delta)
	// fmt.Println(err)

	setup.Vk.alpha_into_G2 = Utils.Bn.G2.MulScalar(Utils.Bn.G2.G, setup.Toxic.alpha)
	setup.Vk.betta_into_G2 = Utils.Bn.G2.MulScalar(Utils.Bn.G2.G, setup.Toxic.betta)
	setup.Vk.gamma_into_G2 = Utils.Bn.G2.MulScalar(Utils.Bn.G2.G, setup.Toxic.gamma)
	setup.Vk.delta_into_G2 = Utils.Bn.G2.MulScalar(Utils.Bn.G2.G, setup.Toxic.delta)
	if err != nil {
		fmt.Println(err)
	}
	return setup, nil
}
func GenerateProofs(circuit Circuit, pk Setup, w []*big.Int, px *big.Int, u, v, w1 [][]*big.Int) (Proof, error) {
	var proof Proof
	// var err error
	proof.PiA1 = [3]*big.Int{Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero()}

	proof.PiB1_G2 = Utils.Bn.Fq6.Zero()

	proof.PIC1 = [3]*big.Int{Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero()}

	proof.PIA_ADD_ALPHA = [3]*big.Int{Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero()}

	proof.PiAp = [3]*big.Int{Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero(), Utils.Bn.G1.F.Zero()}
	proof.PiB1_G2 = Utils.Bn.Fq6.Zero()

	hx := Utils.PF.DivisorPolynomial([]*big.Int{px}, []*big.Int{pk.Pk.Z})

	hx_tx := Utils.PF.Mul(hx, []*big.Int{pk.Pk.Z})

	// fmt.Println("this px value same pxDIVPKz", hx_tx)
	// fmt.Println(px)

	// R_INTO_Delta :=

	R_into_delta := Utils.FqR.Mul(pk.Toxic.r, pk.Toxic.delta)

	S_into_delta := Utils.FqR.Mul(pk.Toxic.s, pk.Toxic.delta)

	delta_inti_delta := Utils.FqR.Mul(pk.Toxic.delta, pk.Toxic.delta)

	R_into_S_into_delta := Utils.FqR.Mul(Utils.FqR.Mul(pk.Toxic.r, pk.Toxic.s), delta_inti_delta)
	// R_into_S_into_delta := Utils.FqR.Mul(R_into_S, pk.Toxic.delta)

	Aa_U_X_1 := new(big.Int)
	Ba_V_X_1 := new(big.Int)
	for i := 0; i < len(circuit.Signals); i++ {

		Ui_into_x_value := Utils.PF.Eval(u[i], pk.Toxic.x)
		Vi_into_x_value := Utils.PF.Eval(v[i], pk.Toxic.x)

		A_X_U := Utils.FqR.Mul(Ui_into_x_value, w[i])
		B_X_v := Utils.FqR.Mul(Vi_into_x_value, w[i])

		Aa_U_X_1 = Utils.FqR.Add(Aa_U_X_1, A_X_U)
		Ba_V_X_1 = Utils.FqR.Add(Ba_V_X_1, B_X_v)

	}

	A_total_value := Utils.FqR.Add(Utils.FqR.Add(pk.Toxic.alpha, Aa_U_X_1), R_into_delta)

	B_total_value := Utils.FqR.Add(Utils.FqR.Add(pk.Toxic.betta, Ba_V_X_1), S_into_delta)

	A_TOTAL_VALUE_INTO_S := Utils.FqR.Mul(Utils.FqR.Mul(A_total_value, pk.Toxic.s), pk.Toxic.delta)

	B_TOTAL_VALUE_INTO_R := Utils.FqR.Mul(Utils.FqR.Mul(B_total_value, pk.Toxic.r), pk.Toxic.delta)

	C_LI2to8 := new(big.Int)

	C_LI0to1 := new(big.Int)

	for i := circuit.NPublic + 1; i < circuit.NVars; i++ {

		C_LI := Utils.FqR.Mul(pk.Toxic.LI[i], w[i])
		C_LI2to8 = Utils.FqR.Add(C_LI2to8, C_LI)

	}

	for i := 0; i < 2; i++ {
		// WI1 := Utils.PF.Eval(w1[i], pk.Toxic.x)
		C_LI1 := Utils.FqR.Mul(pk.Toxic.LI[i], w[i])
		C_LI0to1 = Utils.FqR.Add(C_LI0to1, C_LI1)

	}

	C_ADD_01TO8 := Utils.FqR.Add(C_LI0to1, C_LI2to8)
	C_total := C_ADD_01TO8

	proof.A_total = A_total_value

	proof.B_total = B_total_value
	proof.C_total = C_total

	proof.Hx_Tx = hx_tx[0]

	C_Hx_TX := Utils.FqR.Add(C_LI2to8, hx_tx[0])

	C_Hx_TX_Delta_AS_ADD_BS := Utils.FqR.Add(Utils.FqR.Add(A_TOTAL_VALUE_INTO_S, B_TOTAL_VALUE_INTO_R), C_Hx_TX)

	C_Hx_TX_Delta_AS_ADD_BS_SUB_RSdelta := Utils.FqR.Sub(C_Hx_TX_Delta_AS_ADD_BS, R_into_S_into_delta)

	// A_B := Utils.FqR.Mul(A_total_value, B_total_value)

	// LHC
	LHC1 := Utils.FqR.Mul(pk.Toxic.alpha, pk.Toxic.betta)

	LHC2 := C_LI0to1

	LHC3 := C_Hx_TX_Delta_AS_ADD_BS_SUB_RSdelta
	proof.alpha_betta = LHC1
	proof.CLI0T01 = LHC2
	proof.C_hxtx_delta_AS_ADD_BS_SUB_RSdelta = LHC3

	// data11 := Utils.FqR.Div(LHC2, pk.Toxic.gamma)
	// data12 := Utils.FqR.Mul(data11, pk.Toxic.gamma)
	// proof.CLI0T01 = data12

	return proof, nil
}
// ArrayOfBigZeros creates a *big.Int array with n elements to zero
func ArrayOfBigZeros(num int) []*big.Int {
	bigZero := big.NewInt(int64(0))
	var r []*big.Int
	for i := 0; i < num; i++ {
		r = append(r, bigZero)
	}
	return r
}
func VerifyProof(proof Proof, data4, data5 *big.Int) bool {

	A_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, proof.A_total)

	B_G2 := Utils.Bn.G2.MulScalar(Utils.Bn.G2.G, proof.B_total)
	// test1 := Utils.Bn.G2.Add()

	A_B_pair := Utils.Bn.Pairing(A_G1, B_G2)

	ALPHA_INTO_BETTA := Utils.FqR.Mul(data4, data5)

	LI_0TO1_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, proof.CLI0T01)

	C_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, proof.C_hxtx_delta_AS_ADD_BS_SUB_RSdelta)

	ALPHA_INTO_BETTA_G1 := Utils.Bn.G1.MulScalar(Utils.Bn.G1.G, ALPHA_INTO_BETTA)

	total := Utils.Bn.G1.Add(Utils.Bn.G1.Add(ALPHA_INTO_BETTA_G1, C_G1), LI_0TO1_G1)

	total_pairG2 := Utils.Bn.Pairing(total, Utils.Bn.G2.G)

	A_B2 := Utils.Bn.Fq12.Equal(A_B_pair, total_pairG2)
	// A_B22 := Utils.Bn.Fq12.Add(A_B_pair, total_pairG2)
	// fmt.Println("this is final test", A_B2)

	if A_B2 == true {
		fmt.Println("This is successfully verification", A_B2)

		return A_B2

	}

	return false
}

func max(a, b int) int {
	if a > b {
		return a
	}
	return b
}
func (pf PolynomialField) CombinePolynomials1(r []*big.Int, ap, bp, cp [][]*big.Int, x *big.Int) (*big.Int, *big.Int, *big.Int, *big.Int) {

	Aa_U_X_1 := new(big.Int)
	Ba_V_X_1 := new(big.Int)
	Ca_V_X_1 := new(big.Int)

	for i := 0; i < len(ap); i++ {
		// fmt.Println("this is X value", x)

		AP := Utils.PF.Eval(ap[i], x)
		BP := Utils.PF.Eval(bp[i], x)
		CP := Utils.PF.Eval(cp[i], x)

		A_X_U := Utils.FqR.Mul(AP, r[i])

		B_X_v := Utils.FqR.Mul(BP, r[i])

		C_X_v := Utils.FqR.Mul(CP, r[i])

		Aa_U_X_1 = Utils.FqR.Add(Aa_U_X_1, A_X_U)

		Ba_V_X_1 = Utils.FqR.Add(Ba_V_X_1, B_X_v)

		Ca_V_X_1 = Utils.FqR.Add(Ca_V_X_1, C_X_v)

	}

	// fmt.Println(ax, bx, cx)
	px1 := Utils.FqR.Mul(Aa_U_X_1, Ba_V_X_1)

	px2 := Utils.FqR.Sub(px1, Ca_V_X_1)

	// px := Utils.FqR.Q.Sub(Utils.FqR.Q.Mul(ax, bx), cx)
	return Aa_U_X_1, Ba_V_X_1, Ca_V_X_1, px2
}
func (g1 G1) Affine(p [3]*big.Int) [2]*big.Int {
	if g1.IsZero(p) {
		return g1.Zero()
	}

	zinv := g1.F.Inverse(p[2])
	zinv2 := g1.F.Square(zinv)
	x := g1.F.Mul(p[0], zinv2)

	zinv3 := g1.F.Mul(zinv2, zinv)
	y := g1.F.Mul(p[1], zinv3)
	return [2]*big.Int{x, y}
}
func (g2 G2) Affine(p [3][2]*big.Int) [3][2]*big.Int {
	if g2.IsZero(p) {
		return g2.Zero()
	}

	zinv := g2.F.Inverse(p[2])
	zinv2 := g2.F.Square(zinv)
	x := g2.F.Mul(p[0], zinv2)

	zinv3 := g2.F.Mul(zinv2, zinv)
	y := g2.F.Mul(p[1], zinv3)

	return [3][2]*big.Int{
		g2.F.Affine(x),
		g2.F.Affine(y),
		g2.F.One(),
	}
}
func exp3(a *big.Int) *big.Int {
	b := big.NewInt(0)
	c := big.NewInt(0)
	b = b.Mul(a, a)
	c = c.Mul(b, a)
	return c
}
func NewScanner(r io.Reader) *Scanner {
	return &Scanner{r: bufio.NewReader(r)}
}
// Add performs an addition on the Fq
func (fq Fq) Add(a, b *big.Int) *big.Int {
	r := new(big.Int).Add(a, b)
	// fmt.Println(fq.Q)
	return new(big.Int).Mod(r, fq.Q)
}
// Transpose transposes the *big.Int matrix
func Transpose(matrix [][]*big.Int) [][]*big.Int {
	var r [][]*big.Int
	for i := 0; i < len(matrix[0]); i++ {
		var row []*big.Int
		for j := 0; j < len(matrix); j++ {
			row = append(row, matrix[j][i])
		}
		r = append(r, row)
	}
	return r
}
// LagrangeInterpolation performs the Lagrange Interpolation / Lagrange Polynomials operation
func (pf PolynomialField) LagrangeInterpolation(v []*big.Int) []*big.Int {
	// https://en.wikipedia.org/wiki/Lagrange_polynomial
	var r []*big.Int
	for i := 0; i < len(v); i++ {
		// fmt.Println("this is lagrage ", i+1, len(v), v[i])
		r = pf.Add(r, pf.NewPolZeroAt(i+1, len(v), v[i]))

		// print("this is NEwPOLZeroAT", r, reflect.TypeOf(r))
	}
	//
	// fmt.Println("this is lagrange interpolation", r)
	return r
}
// Add adds two polinomials over the Finite Field
func (pf PolynomialField) Add(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(max(len(a), len(b)))
	for i := 0; i < len(a); i++ {
		r[i] = pf.F.Add(r[i], a[i])
	}
	for i := 0; i < len(b); i++ {
		r[i] = pf.F.Add(r[i], b[i])
	}
	return r
}
// NewPolZeroAt generates a new polynomial that has value zero at the given value
func (pf PolynomialField) NewPolZeroAt(pointPos, totalPoints int, height *big.Int) []*big.Int {
	fac := 1
	for i := 1; i < totalPoints+1; i++ {
		if i != pointPos {
			fac = fac * (pointPos - i)
		}
	}
	facBig := big.NewInt(int64(fac))
	hf := pf.F.Div(height, facBig)
	r := []*big.Int{hf}
	for i := 1; i < totalPoints+1; i++ {
		if i != pointPos {
			ineg := big.NewInt(int64(-i))
			b1 := big.NewInt(int64(1))
			r = pf.Mul(r, []*big.Int{ineg, b1})
		}
	}
	return r
}
// Div performs the division over the finite field
func (fq Fq) Div(a, b *big.Int) *big.Int {
	d := fq.Mul(a, fq.Inverse(b))
	return new(big.Int).Mod(d, fq.Q)
}// Double performs a doubling on the Fq
func (fq Fq) Double(a *big.Int) *big.Int {
	r := new(big.Int).Add(a, a)
	return new(big.Int).Mod(r, fq.Q)
}
func (fq2 Fq2) MulScalar(p [2]*big.Int, e *big.Int) [2]*big.Int {
	// for more possible implementations see g2.go file, at the function g2.MulScalar()

	q := fq2.Zero()
	d := fq2.F.Copy(e)
	r := p

	foundone := false
	for i := d.BitLen(); i >= 0; i-- {
		if foundone {
			q = fq2.Double(q)
		}
		if d.Bit(i) == 1 {
			foundone = true
			q = fq2.Add(q, r)
		}
	}
	return q
}
// Inverse returns the inverse on the Fq
func (fq Fq) Inverse(a *big.Int) *big.Int {
	return new(big.Int).ModInverse(a, fq.Q)

}
// Double performs a doubling on the Fq2
func (fq2 Fq2) Double(a [2]*big.Int) [2]*big.Int {
	return fq2.Add(a, a)
}// Add performs an addition on the Fq2
func (fq2 Fq2) Add(a, b [2]*big.Int) [2]*big.Int {
	return [2]*big.Int{
		fq2.F.Add(a[0], b[0]),
		fq2.F.Add(a[1], b[1]),
	}
}
func (fq2 Fq2) mulByNonResidue(a *big.Int) *big.Int {
	return fq2.F.Mul(fq2.NonResidue, a)
}
func (bn256 Bn256) doublingStep(current [3][2]*big.Int) (EllCoeffs, [3][2]*big.Int) {
	x := current[0]
	y := current[1]
	z := current[2]

	a := bn256.Fq2.MulScalar(bn256.Fq2.Mul(x, y), bn256.TwoInv)
	b := bn256.Fq2.Square(y)
	c := bn256.Fq2.Square(z)
	d := bn256.Fq2.Add(c, bn256.Fq2.Add(c, c))
	e := bn256.Fq2.Mul(bn256.TwistCoefB, d)
	f := bn256.Fq2.Add(e, bn256.Fq2.Add(e, e))
	g := bn256.Fq2.MulScalar(bn256.Fq2.Add(b, f), bn256.TwoInv)
	h := bn256.Fq2.Sub(
		bn256.Fq2.Square(bn256.Fq2.Add(y, z)),
		bn256.Fq2.Add(b, c))
	i := bn256.Fq2.Sub(e, b)
	j := bn256.Fq2.Square(x)
	eSqr := bn256.Fq2.Square(e)
	current[0] = bn256.Fq2.Mul(a, bn256.Fq2.Sub(b, f))
	current[1] = bn256.Fq2.Sub(bn256.Fq2.Sub(bn256.Fq2.Square(g), eSqr),
		bn256.Fq2.Add(eSqr, eSqr))
	current[2] = bn256.Fq2.Mul(b, h)
	res := EllCoeffs{
		Ell0:  bn256.Fq2.Mul(i, bn256.Twist),
		EllVW: bn256.Fq2.Neg(h),
		EllVV: bn256.Fq2.Add(j, bn256.Fq2.Add(j, j)),
	}

	return res, current
}
func (bn256 Bn256) mixedAdditionStep(base, current [3][2]*big.Int) (EllCoeffs, [3][2]*big.Int) {
	x1 := current[0]
	y1 := current[1]
	z1 := current[2]
	x2 := base[0]
	y2 := base[1]

	d := bn256.Fq2.Sub(x1, bn256.Fq2.Mul(x2, z1))
	e := bn256.Fq2.Sub(y1, bn256.Fq2.Mul(y2, z1))
	f := bn256.Fq2.Square(d)
	g := bn256.Fq2.Square(e)
	h := bn256.Fq2.Mul(d, f)
	i := bn256.Fq2.Mul(x1, f)
	j := bn256.Fq2.Sub(
		bn256.Fq2.Add(h, bn256.Fq2.Mul(z1, g)),
		bn256.Fq2.Add(i, i))

	current[0] = bn256.Fq2.Mul(d, j)
	current[1] = bn256.Fq2.Sub(
		bn256.Fq2.Mul(e, bn256.Fq2.Sub(i, j)),
		bn256.Fq2.Mul(h, y1))
	current[2] = bn256.Fq2.Mul(z1, h)

	coef := EllCoeffs{
		Ell0: bn256.Fq2.Mul(
			bn256.Twist,
			bn256.Fq2.Sub(
				bn256.Fq2.Mul(e, x2),
				bn256.Fq2.Mul(d, y2))),
		EllVW: d,
		EllVV: bn256.Fq2.Neg(e),
	}
	return coef, current
}
func (bn256 Bn256) g2MulByQ(p [3][2]*big.Int) [3][2]*big.Int {
	fmx := [2]*big.Int{
		p[0][0],
		bn256.Fq1.Mul(p[0][1], bn256.Fq1.Copy(bn256.FrobeniusCoeffsC11)),
	}
	fmy := [2]*big.Int{
		p[1][0],
		bn256.Fq1.Mul(p[1][1], bn256.Fq1.Copy(bn256.FrobeniusCoeffsC11)),
	}
	fmz := [2]*big.Int{
		p[2][0],
		bn256.Fq1.Mul(p[2][1], bn256.Fq1.Copy(bn256.FrobeniusCoeffsC11)),
	}

	return [3][2]*big.Int{
		bn256.Fq2.Mul(bn256.TwistMulByQX, fmx),
		bn256.Fq2.Mul(bn256.TwistMulByQY, fmy),
		fmz,
	}
}
// Square performs a square operation on the Fq2
func (fq2 Fq2) Square(a [2]*big.Int) [2]*big.Int {
	ab := fq2.F.Mul(a[0], a[1])
	return [2]*big.Int{
		fq2.F.Sub(
			fq2.F.Mul(
				fq2.F.Add(a[0], a[1]),
				fq2.F.Add(
					a[0],
					fq2.mulByNonResidue(a[1]))),
			fq2.F.Add(
				ab,
				fq2.mulByNonResidue(ab))),
		fq2.F.Add(ab, ab),
	}
}
// Mul performs a multiplication on the Fq2
func (fq2 Fq2) Mul(a, b [2]*big.Int) [2]*big.Int {
	v0 := fq2.F.Mul(a[0], b[0])
	v1 := fq2.F.Mul(a[1], b[1])
	return [2]*big.Int{
		fq2.F.Add(v0, fq2.mulByNonResidue(v1)),
		fq2.F.Sub(
			fq2.F.Mul(
				fq2.F.Add(a[0], a[1]),
				fq2.F.Add(b[0], b[1])),
			fq2.F.Add(v0, v1)),
	}
}
// Inverse returns the inverse on the Fq2
func (fq2 Fq2) Inverse(a [2]*big.Int) [2]*big.Int {
	t0 := fq2.F.Square(a[0])
	t1 := fq2.F.Square(a[1])
	t2 := fq2.F.Sub(t0, fq2.mulByNonResidue(t1))
	t3 := fq2.F.Inverse(t2)
	return [2]*big.Int{
		fq2.F.Mul(a[0], t3),
		fq2.F.Neg(fq2.F.Mul(a[1], t3)),
	}
}
// Mul multiplies two polinomials over the Finite Field
func (pf PolynomialField) Mul(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(len(a) + len(b) - 1)
	for i := 0; i < len(a); i++ {
		for j := 0; j < len(b); j++ {
			r[i+j] = pf.F.Add(
				r[i+j],
				pf.F.Mul(a[i], b[j]))

			// fmt.Println("this is r value\n", r)
		}
	}
	return r
}
// Neg performs a negation on the Fq2
func (fq2 Fq2) Neg(a [2]*big.Int) [2]*big.Int {
	return fq2.Sub(fq2.Zero(), a)
}
func (fq2 Fq2) Equal(a, b [2]*big.Int) bool {
	return fq2.F.Equal(a[0], b[0]) && fq2.F.Equal(a[1], b[1])
}
func (bn256 Bn256) mulBy024(a [2][3][2]*big.Int, ell0, ellVW, ellVV [2]*big.Int) [2][3][2]*big.Int {
	b := [2][3][2]*big.Int{
		[3][2]*big.Int{
			ell0,
			bn256.Fq2.Zero(),
			ellVV,
		},
		[3][2]*big.Int{
			bn256.Fq2.Zero(),
			ellVW,
			bn256.Fq2.Zero(),
		},
	}
	return bn256.Fq12.Mul(a, b)
}
// Sub performs a subtraction on the Fq2
func (fq2 Fq2) Sub(a, b [2]*big.Int) [2]*big.Int {
	return [2]*big.Int{
		fq2.F.Sub(a[0], b[0]),
		fq2.F.Sub(a[1], b[1]),
	}
}
// Mul performs a multiplication on the Fq
func (fq Fq) Mul(a, b *big.Int) *big.Int {
	m := new(big.Int).Mul(a, b)
	// fmt.Println(fq.Q)
	return new(big.Int).Mod(m, fq.Q)
}
// Inverse returns the inverse on the Fq12
func (fq12 Fq12) Inverse(a [2][3][2]*big.Int) [2][3][2]*big.Int {
	t0 := fq12.F.Square(a[0])
	t1 := fq12.F.Square(a[1])
	t2 := fq12.F.Sub(t0, fq12.mulByNonResidue(t1))
	t3 := fq12.F.Inverse(t2)
	return [2][3][2]*big.Int{
		fq12.F.Mul(a[0], t3),
		fq12.F.Neg(fq12.F.Mul(a[1], t3)),
	}
}
// Inverse returns the inverse on the Fq6
func (fq6 Fq6) Inverse(a [3][2]*big.Int) [3][2]*big.Int {
	t0 := fq6.F.Square(a[0])
	t1 := fq6.F.Square(a[1])
	t2 := fq6.F.Square(a[2])
	t3 := fq6.F.Mul(a[0], a[1])
	t4 := fq6.F.Mul(a[0], a[2])
	t5 := fq6.F.Mul(a[1], a[2])

	c0 := fq6.F.Sub(t0, fq6.mulByNonResidue(t5))
	c1 := fq6.F.Sub(fq6.mulByNonResidue(t2), t3)
	c2 := fq6.F.Sub(t1, t4)

	t6 := fq6.F.Inverse(
		fq6.F.Add(
			fq6.F.Mul(a[0], c0),
			fq6.mulByNonResidue(
				fq6.F.Add(
					fq6.F.Mul(a[2], c1),
					fq6.F.Mul(a[1], c2)))))
	return [3][2]*big.Int{
		fq6.F.Mul(t6, c0),
		fq6.F.Mul(t6, c1),
		fq6.F.Mul(t6, c2),
	}
}
// Mul performs a multiplication on the Fq
func (fq Fq) Mul1(a, b *big.Int) *big.Int {
	m := new(big.Int).Mul(a, b)
	fmt.Println("this is m", m)
	return new(big.Int).Mod(m, fq.Q)
}
// Mul performs a multiplication on the Fq6
func (fq6 Fq6) Mul(a, b [3][2]*big.Int) [3][2]*big.Int {
	v0 := fq6.F.Mul(a[0], b[0])
	v1 := fq6.F.Mul(a[1], b[1])
	v2 := fq6.F.Mul(a[2], b[2])
	return [3][2]*big.Int{
		fq6.F.Add(
			v0,
			fq6.mulByNonResidue(
				fq6.F.Sub(
					fq6.F.Mul(
						fq6.F.Add(a[1], a[2]),
						fq6.F.Add(b[1], b[2])),
					fq6.F.Add(v1, v2)))),

		fq6.F.Add(
			fq6.F.Sub(
				fq6.F.Mul(
					fq6.F.Add(a[0], a[1]),
					fq6.F.Add(b[0], b[1])),
				fq6.F.Add(v0, v1)),
			fq6.mulByNonResidue(v2)),

		fq6.F.Add(
			fq6.F.Sub(
				fq6.F.Mul(
					fq6.F.Add(a[0], a[2]),
					fq6.F.Add(b[0], b[2])),
				fq6.F.Add(v0, v2)),
			v1),
	}
}
func (fq12 Fq12) mulByNonResidue(a [3][2]*big.Int) [3][2]*big.Int {
	return [3][2]*big.Int{
		fq12.Fq2.Mul(fq12.NonResidue, a[2]),
		a[0],
		a[1],
	}
}
func (fq Fq) Equal(a, b *big.Int) bool {
	aAff := fq.Affine(a)
	bAff := fq.Affine(b)
	return bytes.Equal(aAff.Bytes(), bAff.Bytes())
}
func (fq6 Fq6) mulByNonResidue(a [2]*big.Int) [2]*big.Int {
	return fq6.F.Mul(fq6.NonResidue, a)
}
// Sub performs a subtraction on the Fq6
func (fq6 Fq6) Sub(a, b [3][2]*big.Int) [3][2]*big.Int {
	return [3][2]*big.Int{
		fq6.F.Sub(a[0], b[0]),
		fq6.F.Sub(a[1], b[1]),
		fq6.F.Sub(a[2], b[2]),
	}
}
func (s *Scanner) scanWhitespace() (token Token, lit string) {
	var buf bytes.Buffer
	buf.WriteRune(s.read())

	for {
		if ch := s.read(); ch == eof {
			break
		} else if !isWhitespace(ch) {
			s.unread()
			break
		} else {
			_, _ = buf.WriteRune(ch)
		}
	}
	return WS, buf.String()
}
// Add performs an addition on the Fq6
func (fq6 Fq6) Add(a, b [3][2]*big.Int) [3][2]*big.Int {
	return [3][2]*big.Int{
		fq6.F.Add(a[0], b[0]),
		fq6.F.Add(a[1], b[1]),
		fq6.F.Add(a[2], b[2]),
	}
}
func (fq Fq) Affine(a *big.Int) *big.Int {
	nq := fq.Neg(fq.Q)

	aux := a
	if aux.Cmp(big.NewInt(int64(0))) == -1 { // negative value
		if aux.Cmp(nq) != 1 { // aux less or equal nq
			aux = new(big.Int).Mod(aux, fq.Q)
		}
		if aux.Cmp(big.NewInt(int64(0))) == -1 { // negative value
			aux = new(big.Int).Add(aux, fq.Q)
		}
	} else {
		if aux.Cmp(fq.Q) != -1 { // aux greater or equal nq
			aux = new(big.Int).Mod(aux, fq.Q)
		}
	}
	return aux
}
func isWhitespace(ch rune) bool {
	return ch == ' ' || ch == '\t' || ch == '\n' || ch == '\r' || ch == '\v' || ch == '\f'
}
func (g1 G1) Zero() [2]*big.Int {
	return [2]*big.Int{g1.F.Zero(), g1.F.Zero()}
}
func (fq2 Fq2) Affine(a [2]*big.Int) [2]*big.Int {
	return [2]*big.Int{
		fq2.F.Affine(a[0]),
		fq2.F.Affine(a[1]),
	}
}
// Square performs a square operation on the Fq6
func (fq6 Fq6) Square(a [3][2]*big.Int) [3][2]*big.Int {
	s0 := fq6.F.Square(a[0])
	ab := fq6.F.Mul(a[0], a[1])
	s1 := fq6.F.Add(ab, ab)
	s2 := fq6.F.Square(
		fq6.F.Add(
			fq6.F.Sub(a[0], a[1]),
			a[2]))
	bc := fq6.F.Mul(a[1], a[2])
	s3 := fq6.F.Add(bc, bc)
	s4 := fq6.F.Square(a[2])

	return [3][2]*big.Int{
		fq6.F.Add(
			s0,
			fq6.mulByNonResidue(s3)),
		fq6.F.Add(
			s1,
			fq6.mulByNonResidue(s4)),
		fq6.F.Sub(
			fq6.F.Add(
				fq6.F.Add(s1, s2),
				s3),
			fq6.F.Add(s0, s4)),
	}
}
func (s *Scanner) read() rune {
	ch, _, err := s.r.ReadRune()
	if err != nil {
		return eof
	}
	return ch
}
func (s *Scanner) unread() {
	_ = s.r.UnreadRune()
}
func isLetter(ch rune) bool {
	return (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z')
}
func isDigit(ch rune) bool {
	return (ch >= '0' && ch <= '9')
}
// Neg performs a negation on the Fq6
func (fq6 Fq6) Neg(a [3][2]*big.Int) [3][2]*big.Int {
	return fq6.Sub(fq6.Zero(), a)
}
// Neg performs a negation on the Fq
func (fq Fq) Neg(a *big.Int) *big.Int {
	m := new(big.Int).Neg(a)
	return new(big.Int).Mod(m, fq.Q)
}

func TrimSpaceNewlineInString() string {
   str := "func exp3(private a):LF\tb = a * aLF\tc = a * bLF\treturn cLFLFfunc main(private s0, public s1):LF\ts3 = exp3(s0)LF\ts4 = s3 + s0LF\ts5 = s4 + 5LF\tequals(s1, s5)LF\tout = 1 * 1"
   re := regexp.MustCompile(`LF`)
   return re.ReplaceAllString(str, "\n")
}
// NewParser creates a new parser from a io.Reader
func NewParser1() *Parser {
   str := TrimSpaceNewlineInString()
   return &Parser{s: NewScanner(strings.NewReader(str))}
}
func (p *Parser) Parse() (*Circuit, error) {
   // funcsMap is a map holding the functions names and it's content as Circuit
   circuits = make(map[string]*Circuit)
   mainExist := false
   circuits["main"] = &Circuit{}
   callsCount := 0


   circuits["main"].Signals = append(circuits["main"].Signals, "one")
   nInputs := 0
   currCircuit := ""
   for {
       constraint, err := p.parseLine()
       if err != nil {
           break
       }
       if constraint.Literal == "func" {
           // the name of the func is in constraint.V1
           // check if the name of func is main
           if constraint.V1 != "main" {
               currCircuit = constraint.V1
               circuits[currCircuit] = &Circuit{}
               circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *constraint)
               continue
           }
           currCircuit = "main"
           mainExist = true
           // l, _ := json.Marshal(constraint)
           // fmt.Println(string(l))


           // one constraint for each input
           for _, in := range constraint.PublicInputs {
               newConstr := &Constraint{
                   Op:  "in",
                   Out: in,
               }
               circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *newConstr)
               nInputs++
               circuits[currCircuit].Signals = addToArrayIfNotExist(circuits[currCircuit].Signals, in)
               circuits[currCircuit].NPublic++
           }
           for _, in := range constraint.PrivateInputs {
               newConstr := &Constraint{
                   Op:  "in",
                   Out: in,
               }
               circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *newConstr)
               nInputs++
               circuits[currCircuit].Signals = addToArrayIfNotExist(circuits[currCircuit].Signals, in)
           }
           circuits[currCircuit].PublicInputs = constraint.PublicInputs
           circuits[currCircuit].PrivateInputs = constraint.PrivateInputs
           continue
       }
       if constraint.Literal == "equals" {
           constr1 := &Constraint{
               Op:      "*",
               V1:      constraint.V2,
               V2:      "1",
               Out:     constraint.V1,
               Literal: "equals(" + constraint.V1 + ", " + constraint.V2 + "): " + constraint.V1 + "==" + constraint.V2 + " * 1",
           }
           circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *constr1)
           constr2 := &Constraint{
               Op:      "*",
               V1:      constraint.V1,
               V2:      "1",
               Out:     constraint.V2,
               Literal: "equals(" + constraint.V1 + ", " + constraint.V2 + "): " + constraint.V2 + "==" + constraint.V1 + " * 1",
           }
           circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *constr2)
           continue
       }
       if constraint.Literal == "return" {
           currCircuit = ""
           continue
       }
       if constraint.Literal == "call" {
           callsCountStr := strconv.Itoa(callsCount)
           // for each of the constraints of the called circuit
           // add it into the current circuit
           signalMap := make(map[string]string)
           for i, s := range constraint.PrivateInputs {
               // signalMap[s] = circuits[constraint.Op].Constraints[0].PrivateInputs[i]
               signalMap[circuits[constraint.Op].Constraints[0].PrivateInputs[i]+callsCountStr] = s
           }
           // add out to map
           signalMap[circuits[constraint.Op].Constraints[len(circuits[constraint.Op].Constraints)-1].Out+callsCountStr] = constraint.Out


           for i := 1; i < len(circuits[constraint.Op].Constraints); i++ {
               c := circuits[constraint.Op].Constraints[i]
               // add constraint, puting unique names to vars
               nc := &Constraint{
                   Op:      c.Op,
                   V1:      subsIfInMap(c.V1+callsCountStr, signalMap),
                   V2:      subsIfInMap(c.V2+callsCountStr, signalMap),
                   Out:     subsIfInMap(c.Out+callsCountStr, signalMap),
                   Literal: "",
               }
               nc.Literal = nc.Out + "=" + nc.V1 + nc.Op + nc.V2
               circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *nc)
           }
           for _, s := range circuits[constraint.Op].Signals {
               circuits[currCircuit].Signals = addToArrayIfNotExist(circuits[currCircuit].Signals, subsIfInMap(s+callsCountStr, signalMap))
           }
           callsCount++
           continue


       }
       if constraint.Literal == "import" {
           circuitFile, err := os.Open(constraint.Out)
           if err != nil {
               panic(errors.New("imported path error: " + constraint.Out))
           }
           parser := NewParser(bufio.NewReader(circuitFile))
           _, err = parser.Parse() // this will add the imported file funcs into the `circuits` map
           continue
       }


       circuits[currCircuit].Constraints = append(circuits[currCircuit].Constraints, *constraint)
       isVal, _ := isValue(constraint.V1)
       if !isVal {
           circuits[currCircuit].Signals = addToArrayIfNotExist(circuits[currCircuit].Signals, constraint.V1)
       }
       isVal, _ = isValue(constraint.V2)
       if !isVal {
           circuits[currCircuit].Signals = addToArrayIfNotExist(circuits[currCircuit].Signals, constraint.V2)
       }


       circuits[currCircuit].Signals = addToArrayIfNotExist(circuits[currCircuit].Signals, constraint.Out)
   }
   circuits["main"].NVars = len(circuits["main"].Signals)
   circuits["main"].NSignals = len(circuits["main"].Signals)
   if mainExist == false {
       return circuits["main"], errors.New("No 'main' func declared")
   }
   return circuits["main"], nil
}
func (circ *Circuit) calculateWitness(privateInputs []*big.Int, publicInputs []*big.Int) ([]*big.Int, error) {
   if len(privateInputs) != len(circ.PrivateInputs) {
       return []*big.Int{}, errors.New("given privateInputs != circuit.PublicInputs")
   }
   if len(publicInputs) != len(circ.PublicInputs) {
       return []*big.Int{}, errors.New("given publicInputs != circuit.PublicInputs")
   }
   w := ArrayOfBigZeros(len(circ.Signals))
   w[0] = big.NewInt(int64(1))
   for i, input := range publicInputs {
       w[i+1] = input
   }
   for i, input := range privateInputs {
       w[i+len(publicInputs)+1] = input
   }
   for _, constraint := range circ.Constraints {
       if constraint.Op == "in" {
       } else if constraint.Op == "+" {
           w[indexInArray(circ.Signals, constraint.Out)] = new(big.Int).Add(grabVar(circ.Signals, w, constraint.V1), grabVar(circ.Signals, w, constraint.V2))
       } else if constraint.Op == "-" {
           w[indexInArray(circ.Signals, constraint.Out)] = new(big.Int).Sub(grabVar(circ.Signals, w, constraint.V1), grabVar(circ.Signals, w, constraint.V2))
       } else if constraint.Op == "*" {
           w[indexInArray(circ.Signals, constraint.Out)] = new(big.Int).Mul(grabVar(circ.Signals, w, constraint.V1), grabVar(circ.Signals, w, constraint.V2))
       } else if constraint.Op == "/" {
           w[indexInArray(circ.Signals, constraint.Out)] = new(big.Int).Div(grabVar(circ.Signals, w, constraint.V1), grabVar(circ.Signals, w, constraint.V2))
       }
   }
   return w, nil
}
func indexInArray(arr []string, e string) int {
	for i, a := range arr {
		if a == e {
			return i
		}
	}
	return -1
}
// GenerateR1CS generates the R1CS polynomials from the Circuit
func (circ *Circuit) GenerateR1CS() ([][]*big.Int, [][]*big.Int, [][]*big.Int) {
   // from flat code to R1CS


   var a [][]*big.Int
   var b [][]*big.Int
   var c [][]*big.Int


   used := make(map[string]bool)
   for _, constraint := range circ.Constraints {
       aConstraint := ArrayOfBigZeros(len(circ.Signals))
       bConstraint := ArrayOfBigZeros(len(circ.Signals))
       cConstraint := ArrayOfBigZeros(len(circ.Signals))


       // if existInArray(constraint.Out) {
       // if used[constraint.Out] {
       // panic(errors.New("out variable already used: " + constraint.Out))
       // }
       used[constraint.Out] = true
       if constraint.Op == "in" {
           for i := 0; i <= len(circ.PublicInputs); i++ {
               aConstraint[indexInArray(circ.Signals, constraint.Out)] = new(big.Int).Add(aConstraint[indexInArray(circ.Signals, constraint.Out)], big.NewInt(int64(1)))
               aConstraint, used = insertVar(aConstraint, circ.Signals, constraint.Out, used)
               bConstraint[0] = big.NewInt(int64(1))
           }
           continue


       } else if constraint.Op == "+" {
           cConstraint[indexInArray(circ.Signals, constraint.Out)] = big.NewInt(int64(1))
           aConstraint, used = insertVar(aConstraint, circ.Signals, constraint.V1, used)
           aConstraint, used = insertVar(aConstraint, circ.Signals, constraint.V2, used)
           bConstraint[0] = big.NewInt(int64(1))
       } else if constraint.Op == "-" {
           cConstraint[indexInArray(circ.Signals, constraint.Out)] = big.NewInt(int64(1))
           aConstraint, used = insertVarNeg(aConstraint, circ.Signals, constraint.V1, used)
           aConstraint, used = insertVarNeg(aConstraint, circ.Signals, constraint.V2, used)
           bConstraint[0] = big.NewInt(int64(1))
       } else if constraint.Op == "*" {
           cConstraint[indexInArray(circ.Signals, constraint.Out)] = big.NewInt(int64(1))
           aConstraint, used = insertVar(aConstraint, circ.Signals, constraint.V1, used)
           bConstraint, used = insertVar(bConstraint, circ.Signals, constraint.V2, used)
       } else if constraint.Op == "/" {
           cConstraint, used = insertVar(cConstraint, circ.Signals, constraint.V1, used)
           cConstraint[indexInArray(circ.Signals, constraint.Out)] = big.NewInt(int64(1))
           bConstraint, used = insertVar(bConstraint, circ.Signals, constraint.V2, used)
       }


       a = append(a, aConstraint)
       b = append(b, bConstraint)
       c = append(c, cConstraint)


   }
   circ.R1CS.A = a
   circ.R1CS.B = b
   circ.R1CS.C = c
   return a, b, c
}
// parseLine parses the current line
func (p *Parser) parseLine() (*Constraint, error) {
	/*
		in this version,
		line will be for example s3 = s1 * s4
		this is:
		val eq val op val
	*/
	c := &Constraint{}
	tok, lit := p.scanIgnoreWhitespace()
	c.Out = lit
	c.Literal += lit

	if c.Literal == "func" {
		// format: `func name(in):`
		line, err := p.s.r.ReadString(':')
		if err != nil {
			return c, err
		}
		// get func name
		fName := strings.Split(line, "(")[0]
		fName = strings.Replace(fName, " ", "", -1)
		fName = strings.Replace(fName, "	", "", -1)
		c.V1 = fName // so, the name of the func will be in c.V1

		// read string inside ( )
		rgx := regexp.MustCompile(`\((.*?)\)`)
		insideParenthesis := rgx.FindStringSubmatch(line)
		varsString := strings.Replace(insideParenthesis[1], " ", "", -1)
		allInputs := strings.Split(varsString, ",")

		// from allInputs, get the private and the public separated
		for _, in := range allInputs {
			if strings.Contains(in, "private") {
				input := strings.Replace(in, "private", "", -1)
				c.PrivateInputs = append(c.PrivateInputs, input)
			} else if strings.Contains(in, "public") {
				input := strings.Replace(in, "public", "", -1)
				c.PublicInputs = append(c.PublicInputs, input)
			} else {
				// TODO give more info about the circuit code error
				fmt.Println("error on declaration of public and private inputs")
				os.Exit(0)
			}
		}
		return c, nil
	}
	if c.Literal == "equals" {
		// format: `equals(a, b)`
		line, err := p.s.r.ReadString(')')
		if err != nil {
			return c, err
		}
		// read string inside ( )
		rgx := regexp.MustCompile(`\((.*?)\)`)
		insideParenthesis := rgx.FindStringSubmatch(line)
		varsString := strings.Replace(insideParenthesis[1], " ", "", -1)
		params := strings.Split(varsString, ",")
		c.V1 = params[0]
		c.V2 = params[1]
		return c, nil
	}
	if c.Literal == "return" {
		_, varToReturn := p.scanIgnoreWhitespace()
		c.Out = varToReturn
		return c, nil
	}
	if c.Literal == "import" {
		line, err := p.s.r.ReadString('\n')
		if err != nil {
			return c, err
		}
		// read string inside " "
		path := strings.TrimLeft(strings.TrimRight(line, `"`), `"`)
		path = strings.Replace(path, `"`, "", -1)
		path = strings.Replace(path, " ", "", -1)
		path = strings.Replace(path, "\n", "", -1)
		c.Out = path
		return c, nil
	}

	_, lit = p.scanIgnoreWhitespace() // skip =
	c.Literal += lit

	// v1
	_, lit = p.scanIgnoreWhitespace()

	// check if lit is a name of a func that we have declared
	if _, ok := circuits[lit]; ok {
		// if inside, is calling a declared function
		c.Literal = "call"
		c.Op = lit // c.Op handles the name of the function called
		// put the inputs of the call into the c.PrivateInputs
		// format: `funcname(a, b)`
		line, err := p.s.r.ReadString(')')
		if err != nil {
			fmt.Println("ERR", err)
			return c, err
		}
		// read string inside ( )
		rgx := regexp.MustCompile(`\((.*?)\)`)
		insideParenthesis := rgx.FindStringSubmatch(line)
		varsString := strings.Replace(insideParenthesis[1], " ", "", -1)
		params := strings.Split(varsString, ",")
		c.PrivateInputs = params
		return c, nil

	}

	c.V1 = lit
	c.Literal += lit
	// operator
	_, lit = p.scanIgnoreWhitespace()
	if lit == "(" {
		panic(errors.New("using not declared function"))
	}
	c.Op = lit
	c.Literal += lit
	// v2
	_, lit = p.scanIgnoreWhitespace()
	c.V2 = lit
	c.Literal += lit
	if tok == EOF {
		return nil, errors.New("eof in parseline")
	}
	return c, nil
}
func prepareUtils() utils {
	bn, err := NewBn256()
	if err != nil {
		panic(err)
	}
	// new Finite Field
	fqR := NewFq(bn.R)
	// new Polynomial Field
	pf := NewPolynomialField(fqR)

	return utils{
		Bn:  bn,
		FqR: fqR,
		PF:  pf,
	}
}
func (fq Fq) Rand() (*big.Int, error) {

	// twoexp := new(big.Int).Exp(big.NewInt(2), big.NewInt(int64(maxbits)), nil)
	// max := new(big.Int).Sub(twoexp, big.NewInt(1))

	maxbits := fq.Q.BitLen()
	b := make([]byte, (maxbits/2)-1)
	_, err := rand.Read(b)
	if err != nil {
		return nil, err
	}
	r := new(big.Int).SetBytes(b)
	rq := new(big.Int).Mod(r, fq.Q)

	// r over q, nil
	return rq, nil
}
func ConvertBigIntArrayToCustomArray(p [3]*big.Int) [3]string {
	arrayToBeReturned := make([]string, len(p))
	//fmt.Println("p", p, "length", len(p))
	for index, value := range p {
		if value != nil {
			arrayToBeReturned[index] = value.String()
		}
	}

	return [3]string{arrayToBeReturned[0], arrayToBeReturned[1], arrayToBeReturned[2]}
}
func addToArrayIfNotExist(arr []string, elem string) []string {
	for _, v := range arr {
		if v == elem {
			return arr
		}
	}
	arr = append(arr, elem)
	return arr
}
func subsIfInMap(original string, m map[string]string) string {
	if v, ok := m[original]; ok {
		return v
	}
	return original
}// NewParser creates a new parser from a io.Reader
func NewParser(r io.Reader) *Parser {
	return &Parser{s: NewScanner(r)}
}
func (p *Parser) scanIgnoreWhitespace() (tok Token, lit string) {
	tok, lit = p.scan()
	if tok == WS {
		tok, lit = p.scan()
	}
	return
}
func insertVarNeg(arr []*big.Int, signals []string, v string, used map[string]bool) ([]*big.Int, map[string]bool) {
	isVal, value := isValue(v)
	valueBigInt := big.NewInt(int64(value))
	if isVal {
		arr[0] = new(big.Int).Add(arr[0], valueBigInt)
	} else {
		if !used[v] {
			panic(errors.New("using variable before it's set"))
		}
		arr[indexInArray(signals, v)] = new(big.Int).Add(arr[indexInArray(signals, v)], big.NewInt(int64(-1)))
	}
	return arr, used
}
func insertVar(arr []*big.Int, signals []string, v string, used map[string]bool) ([]*big.Int, map[string]bool) {
	isVal, value := isValue(v)
	valueBigInt := big.NewInt(int64(value))
	if isVal {
		arr[0] = new(big.Int).Add(arr[0], valueBigInt)
	} else {
		if !used[v] {
			panic(errors.New("using variable before it's set"))
		}
		arr[indexInArray(signals, v)] = new(big.Int).Add(arr[indexInArray(signals, v)], big.NewInt(int64(1)))
	}
	return arr, used
}
func isValue(a string) (bool, int) {
	v, err := strconv.Atoi(a)
	if err != nil {
		return false, 0
	}
	return true, v
}
func grabVar(signals []string, w []*big.Int, vStr string) *big.Int {
	isVal, v := isValue(vStr)
	vBig := big.NewInt(int64(v))
	if isVal {
		return vBig
	} else {
		return w[indexInArray(signals, vStr)]
	}
}// Eval evaluates the polinomial over the Finite Field at the given value x
func (pf PolynomialField) Eval(v []*big.Int, x *big.Int) *big.Int {
	r := big.NewInt(int64(0))
	for i := 0; i < len(v); i++ {
		xi := pf.F.Exp(x, big.NewInt(int64(i)))
		elem := pf.F.Mul(v[i], xi)
		r = pf.F.Add(r, elem)
	}
	return r
}
// Proof contains the parameters to proof the zkSNARK
func (pf PolynomialField) DivisorPolynomial(px, z []*big.Int) []*big.Int {
	quo, _ := pf.Div(px, z)
	return quo
}
// Sub subtracts two polinomials over the Finite Field
func (pf PolynomialField) Sub(a, b []*big.Int) []*big.Int {
	r := ArrayOfBigZeros(max(len(a), len(b)))
	for i := 0; i < len(a); i++ {
		r[i] = pf.F.Add(r[i], a[i])
	}
	for i := 0; i < len(b); i++ {
		r[i] = pf.F.Sub(r[i], b[i])
	}
	return r
}
// Sub performs a subtraction on the Fq
func (fq Fq) Sub(a, b *big.Int) *big.Int {
	r := new(big.Int).Sub(a, b)
	return new(big.Int).Mod(r, fq.Q)
}// NewBn256 returns the BN128
func NewBn256() (Bn256, error) {
	var b Bn256
	q, ok := new(big.Int).SetString("21888242871839275222246405745257275088696311157297823662689037894645226208583", 10)
	if !ok {
		return b, errors.New("err with q")
	}
	b.Q = q

	r, ok := new(big.Int).SetString("21888242871839275222246405745257275088548364400416034343698204186575808495617", 10)
	if !ok {
		return b, errors.New("err with r")
	}
	b.R = r

	b.Gg1 = [2]*big.Int{
		big.NewInt(int64(1)),
		big.NewInt(int64(2)),
	}

	g2_00, ok := new(big.Int).SetString("10857046999023057135944570762232829481370756359578518086990519993285655852781", 10)
	if !ok {
		return b, errors.New("err with g2_00")
	}
	g2_01, ok := new(big.Int).SetString("11559732032986387107991004021392285783925812861821192530917403151452391805634", 10)
	if !ok {
		return b, errors.New("err with g2_00")
	}
	g2_10, ok := new(big.Int).SetString("8495653923123431417604973247489272438418190587263600148770280649306958101930", 10)
	if !ok {
		return b, errors.New("err with g2_00")
	}
	g2_11, ok := new(big.Int).SetString("4082367875863433681332203403145435568316851327593401208105741076214120093531", 10)
	if !ok {
		return b, errors.New("err with g2_00")
	}

	b.Gg2 = [2][2]*big.Int{
		[2]*big.Int{
			g2_00,
			g2_01,
		},
		[2]*big.Int{
			g2_10,
			g2_11,
		},
	}

	b.Fq1 = NewFq(q)
	b.NonResidueFq2, ok = new(big.Int).SetString("21888242871839275222246405745257275088696311157297823662689037894645226208582", 10) // i
	if !ok {
		return b, errors.New("err with nonResidueFq2")
	}
	b.NonResidueFq6 = [2]*big.Int{
		big.NewInt(int64(9)),
		big.NewInt(int64(1)),
	}

	b.Fq2 = NewFq2(b.Fq1, b.NonResidueFq2)
	b.Fq6 = NewFq6(b.Fq2, b.NonResidueFq6)
	b.Fq12 = NewFq12(b.Fq6, b.Fq2, b.NonResidueFq6)

	b.G1 = NewG1(b.Fq1, b.Gg1)
	b.G2 = NewG2(b.Fq2, b.Gg2)

	err := b.preparePairing()
	if err != nil {
		return b, err
	}

	return b, nil
}// NewFq generates a new Fq
func NewFq(q *big.Int) Fq {
	return Fq{
		q,
	}
}
// Pairing calculates the BN128 Pairing of two given values
func (bn256 Bn256) Pairing(p1 [3]*big.Int, p2 [3][2]*big.Int) [2][3][2]*big.Int {
	pre1 := bn256.preComputeG1(p1)
	pre2 := bn256.preComputeG2(p2)
	// fmt.Println("this is pre1")

	r1 := bn256.MillerLoop(pre1, pre2)
	res := bn256.finalExponentiation(r1)
	return res
}
func (fq6 Fq6) Zero() [3][2]*big.Int {
	return [3][2]*big.Int{fq6.F.Zero(), fq6.F.Zero(), fq6.F.Zero()}
}
func (fq12 Fq12) Equal(a, b [2][3][2]*big.Int) bool {
	return fq12.F.Equal(a[0], b[0]) && fq12.F.Equal(a[1], b[1])
}
func (p *Parser) scan() (tok Token, lit string) {
	// if there is a token in the buffer return it
	if p.buf.n != 0 {
		p.buf.n = 0
		return p.buf.tok, p.buf.lit
	}
	tok, lit = p.s.scan()

	p.buf.tok, p.buf.lit = tok, lit

	return
}
func (fq12 Fq12) Exp(base [2][3][2]*big.Int, e *big.Int) [2][3][2]*big.Int {
	// TODO fix bottleneck

	res := fq12.One()
	rem := fq12.Fq2.F.Copy(e)
	exp := base

	// before := time.Now()
	for !bytes.Equal(rem.Bytes(), big.NewInt(int64(0)).Bytes()) {
		if BigIsOdd(rem) {
			res = fq12.Mul(res, exp)
		}
		exp = fq12.Square(exp)
		rem = new(big.Int).Rsh(rem, 1)
	}
	// fmt.Println("time elapsed:", time.Since(before))
	return res
}// Exp performs the exponential over Fq
func (fq Fq) Exp(base *big.Int, e *big.Int) *big.Int {
	res := fq.One()
	rem := fq.Copy(e)
	exp := base

	for !bytes.Equal(rem.Bytes(), big.NewInt(int64(0)).Bytes()) {
		if BigIsOdd(rem) {
			res = fq.Mul(res, exp)
		}
		exp = fq.Square(exp)
		rem = new(big.Int).Rsh(rem, 1)
	}
	return res
}// Div performs the division over the finite field
func (pf PolynomialField) Div(a, b []*big.Int) ([]*big.Int, []*big.Int) {
	// https://en.wikipedia.org/wiki/Division_algorithm
	r := ArrayOfBigZeros(len(a) - len(b) + 1)
	rem := a
	for len(rem) >= len(b) {
		l := pf.F.Div(rem[len(rem)-1], b[len(b)-1])
		pos := len(rem) - len(b)
		r[pos] = l
		aux := ArrayOfBigZeros(pos)
		aux1 := append(aux, l)
		aux2 := pf.Sub(rem, pf.Mul(b, aux1))
		rem = aux2[:len(aux2)-1]
	}
	return r, rem
}
// NewFq12 generates a new Fq12
func NewFq12(f Fq6, fq2 Fq2, nonResidue [2]*big.Int) Fq12 {
	fq12 := Fq12{
		f,
		fq2,
		nonResidue,
	}
	return fq12
}
// NewFq2 generates a new Fq2
func NewFq2(f Fq, nonResidue *big.Int) Fq2 {
	fq2 := Fq2{
		f,
		nonResidue,
	}
	return fq2
}
func (g1 G1) MulScalar(p [3]*big.Int, e *big.Int) [3]*big.Int {
	q := [3]*big.Int{g1.F.Zero(), g1.F.Zero(), g1.F.Zero()}
	d := g1.F.Copy(e)
	r := p
	// fmt.Println("this is d and P values", d, r, d.BitLen())
	// fmt.Println()
	for i := d.BitLen() - 1; i >= 0; i-- {
		// fmt.Println(i)
		// fmt.Println("this is g1 doble", g1.Double(q))

		q = g1.Double(q)
		// fmt.Println("this is q double", q)
		// fmt.Println(q)
		if d.Bit(i) == 1 {
			q = g1.Add(q, r)
			// fmt.Println("this is q and r values add", q, r)

		}
		// fmt.Println(q)
	}

	return q
}
func (g2 G2) MulScalar(p [3][2]*big.Int, e *big.Int) [3][2]*big.Int {
	q := [3][2]*big.Int{g2.F.Zero(), g2.F.Zero(), g2.F.Zero()}
	d := g2.F.F.Copy(e) // d := e
	r := p
	for i := d.BitLen() - 1; i >= 0; i-- {
		q = g2.Double(q)
		if d.Bit(i) == 1 {
			q = g2.Add(q, r)
		}
	}
	return q
}
// NewFq6 generates a new Fq6
func NewFq6(f Fq2, nonResidue [2]*big.Int) Fq6 {
	fq6 := Fq6{
		f,
		nonResidue,
	}
	return fq6
}
func NewG1(f Fq, g [2]*big.Int) G1 {
	var g1 G1
	g1.F = f
	g1.G = [3]*big.Int{
		g[0],
		g[1],
		g1.F.One(),
	}
	return g1
}
func NewG2(f Fq2, g [2][2]*big.Int) G2 {
	var g2 G2
	g2.F = f
	g2.G = [3][2]*big.Int{
		g[0],
		g[1],
		g2.F.One(),
	}
	return g2
}// One returns a One value on the Fq2
func (fq2 Fq2) One() [2]*big.Int {
	return [2]*big.Int{fq2.F.One(), fq2.F.Zero()}
}
func (g1 G1) Add(p1, p2 [3]*big.Int) [3]*big.Int {

	if g1.IsZero(p1) {
		return p2
	}
	if g1.IsZero(p2) {
		return p1
	}

	x1 := p1[0]
	y1 := p1[1]
	z1 := p1[2]
	x2 := p2[0]
	y2 := p2[1]
	z2 := p2[2]

	z1z1 := g1.F.Square(z1)
	z2z2 := g1.F.Square(z2)

	u1 := g1.F.Mul(x1, z2z2)
	u2 := g1.F.Mul(x2, z1z1)

	t0 := g1.F.Mul(z2, z2z2)
	s1 := g1.F.Mul(y1, t0)

	t1 := g1.F.Mul(z1, z1z1)
	s2 := g1.F.Mul(y2, t1)

	h := g1.F.Sub(u2, u1)
	t2 := g1.F.Add(h, h)
	i := g1.F.Square(t2)
	j := g1.F.Mul(h, i)
	t3 := g1.F.Sub(s2, s1)
	r := g1.F.Add(t3, t3)
	v := g1.F.Mul(u1, i)
	t4 := g1.F.Square(r)
	t5 := g1.F.Add(v, v)
	t6 := g1.F.Sub(t4, j)
	x3 := g1.F.Sub(t6, t5)
	t7 := g1.F.Sub(v, x3)
	t8 := g1.F.Mul(s1, j)
	t9 := g1.F.Add(t8, t8)
	t10 := g1.F.Mul(r, t7)

	y3 := g1.F.Sub(t10, t9)

	t11 := g1.F.Add(z1, z2)
	t12 := g1.F.Square(t11)
	t13 := g1.F.Sub(t12, z1z1)
	t14 := g1.F.Sub(t13, z2z2)
	z3 := g1.F.Mul(t14, h)

	return [3]*big.Int{x3, y3, z3}
}
func (g1 G1) IsZero(p [3]*big.Int) bool {
	return g1.F.IsZero(p[2])

}
func (g2 G2) Zero() [3][2]*big.Int {
	return [3][2]*big.Int{g2.F.Zero(), g2.F.One(), g2.F.Zero()}
}
func (g2 G2) IsZero(p [3][2]*big.Int) bool {
	return g2.F.IsZero(p[2])
}
func (fq Fq) IsZero(a *big.Int) bool {
	return bytes.Equal(a.Bytes(), fq.Zero().Bytes())
}
func (g1 G1) Double(p [3]*big.Int) [3]*big.Int {

	// https://en.wikibooks.org/wiki/Cryptography/Prime_Curve/Jacobian_Coordinates
	// http://hyperelliptic.org/EFD/g1p/auto-code/shortw/jacobian-0/doubling/dbl-2009-l.op3
	// https://github.com/zcash/zcash/blob/master/src/snark/libsnark/algebra/curves/alt_bn256/alt_bn256_g1.cpp#L325

	if g1.IsZero(p) {
		return p
	}
	// fmt.Println("this is double function", p)

	a := g1.F.Square(p[0])
	b := g1.F.Square(p[1])
	c := g1.F.Square(b)

	t0 := g1.F.Add(p[0], b)
	t1 := g1.F.Square(t0)
	t2 := g1.F.Sub(t1, a)
	t3 := g1.F.Sub(t2, c)

	d := g1.F.Double(t3)
	e := g1.F.Add(g1.F.Add(a, a), a)
	f := g1.F.Square(e)

	t4 := g1.F.Double(d)
	x3 := g1.F.Sub(f, t4)

	t5 := g1.F.Sub(d, x3)
	twoC := g1.F.Add(c, c)
	fourC := g1.F.Add(twoC, twoC)
	t6 := g1.F.Add(fourC, fourC)
	t7 := g1.F.Mul(e, t5)
	y3 := g1.F.Sub(t7, t6)

	t8 := g1.F.Mul(p[1], p[2])
	z3 := g1.F.Double(t8)
	// fmt.Println("a", a, "b", c, "c", c, "t0,t1,t2,t3", t0, t1, t2, t3, "d,e,f", d, e, f, "t4,x3", t4, x3, "t5,twoc,fourc,t6,t7,y3", t5, twoC, fourC, t6, t7, y3, "t8,z3", t8, z3)

	return [3]*big.Int{x3, y3, z3}
}
// Zero returns a Zero value on the Fq
func (fq Fq) Zero() *big.Int {
	return big.NewInt(int64(0))
}
func (bn256 *Bn256) preparePairing() error {
	var ok bool
	bn256.LoopCount, ok = new(big.Int).SetString("29793968203157093288", 10)
	if !ok {
		return errors.New("err with LoopCount from string")
	}

	bn256.LoopCountNeg = false

	bn256.TwoInv = bn256.Fq1.Inverse(big.NewInt(int64(2)))

	bn256.CoefB = big.NewInt(int64(3))
	bn256.Twist = [2]*big.Int{
		big.NewInt(int64(9)),
		big.NewInt(int64(1)),
	}
	bn256.TwistCoefB = bn256.Fq2.MulScalar(bn256.Fq2.Inverse(bn256.Twist), bn256.CoefB)

	bn256.FrobeniusCoeffsC11, ok = new(big.Int).SetString("21888242871839275222246405745257275088696311157297823662689037894645226208582", 10)
	if !ok {
		return errors.New("error parsing frobeniusCoeffsC11")
	}

	a, ok := new(big.Int).SetString("21575463638280843010398324269430826099269044274347216827212613867836435027261", 10)
	if !ok {
		return errors.New("error parsing a")
	}
	b, ok := new(big.Int).SetString("10307601595873709700152284273816112264069230130616436755625194854815875713954", 10)
	if !ok {
		return errors.New("error parsing b")
	}
	bn256.TwistMulByQX = [2]*big.Int{
		a,
		b,
	}

	a, ok = new(big.Int).SetString("2821565182194536844548159561693502659359617185244120367078079554186484126554", 10)
	if !ok {
		return errors.New("error parsing a")
	}
	b, ok = new(big.Int).SetString("3505843767911556378687030309984248845540243509899259641013678093033130930403", 10)
	if !ok {
		return errors.New("error parsing b")
	}
	bn256.TwistMulByQY = [2]*big.Int{
		a,
		b,
	}

	bn256.FinalExp, ok = new(big.Int).SetString("552484233613224096312617126783173147097382103762957654188882734314196910839907541213974502761540629817009608548654680343627701153829446747810907373256841551006201639677726139946029199968412598804882391702273019083653272047566316584365559776493027495458238373902875937659943504873220554161550525926302303331747463515644711876653177129578303191095900909191624817826566688241804408081892785725967931714097716709526092261278071952560171111444072049229123565057483750161460024353346284167282452756217662335528813519139808291170539072125381230815729071544861602750936964829313608137325426383735122175229541155376346436093930287402089517426973178917569713384748081827255472576937471496195752727188261435633271238710131736096299798168852925540549342330775279877006784354801422249722573783561685179618816480037695005515426162362431072245638324744480", 10)
	if !ok {
		return errors.New("error parsing finalExp")
	}

	return nil

}
func (bn256 Bn256) preComputeG1(p [3]*big.Int) AteG1Precomp {
	pCopy := bn256.G1.Affine(p)
	// fmt.Println("this is oke precompute")
	res := AteG1Precomp{
		Px: pCopy[0],
		Py: pCopy[1],
	}
	return res
}
func (bn256 Bn256) preComputeG2(p [3][2]*big.Int) AteG2Precomp {
	qCopy := bn256.G2.Affine(p)
	res := AteG2Precomp{
		qCopy[0],
		qCopy[1],
		[]EllCoeffs{},
	}
	r := [3][2]*big.Int{
		bn256.Fq2.Copy(qCopy[0]),
		bn256.Fq2.Copy(qCopy[1]),
		bn256.Fq2.One(),
	}
	var c EllCoeffs
	for i := bn256.LoopCount.BitLen() - 2; i >= 0; i-- {
		bit := bn256.LoopCount.Bit(i)

		c, r = bn256.doublingStep(r)
		res.Coeffs = append(res.Coeffs, c)
		if bit == 1 {
			c, r = bn256.mixedAdditionStep(qCopy, r)
			res.Coeffs = append(res.Coeffs, c)
		}
	}

	q1 := bn256.G2.Affine(bn256.g2MulByQ(qCopy))
	if !bn256.Fq2.Equal(q1[2], bn256.Fq2.One()) {
		// return res, errors.New("q1[2] != Fq2.One")
		panic(errors.New("q1[2] != Fq2.One()"))
	}
	q2 := bn256.G2.Affine(bn256.g2MulByQ(q1))
	if !bn256.Fq2.Equal(q2[2], bn256.Fq2.One()) {
		// return res, errors.New("q2[2] != Fq2.One")
		panic(errors.New("q2[2] != Fq2.One()"))
	}

	if bn256.LoopCountNeg {
		r[1] = bn256.Fq2.Neg(r[1])
	}
	q2[1] = bn256.Fq2.Neg(q2[1])

	c, r = bn256.mixedAdditionStep(q1, r)
	res.Coeffs = append(res.Coeffs, c)

	c, r = bn256.mixedAdditionStep(q2, r)
	res.Coeffs = append(res.Coeffs, c)

	return res
}
func (bn256 Bn256) finalExponentiation(r [2][3][2]*big.Int) [2][3][2]*big.Int {
	res := bn256.Fq12.Exp(r, bn256.FinalExp)
	return res
}
func (bn256 Bn256) MillerLoop(pre1 AteG1Precomp, pre2 AteG2Precomp) [2][3][2]*big.Int {
	// https://cryptojedi.org/papers/dclxvi-20100714.pdf
	// https://eprint.iacr.org/2008/096.pdf

	idx := 0
	var c EllCoeffs
	f := bn256.Fq12.One()

	for i := bn256.LoopCount.BitLen() - 2; i >= 0; i-- {
		bit := bn256.LoopCount.Bit(i)

		c = pre2.Coeffs[idx]
		idx++
		f = bn256.Fq12.Square(f)

		f = bn256.mulBy024(f,
			c.Ell0,
			bn256.Fq2.MulScalar(c.EllVW, pre1.Py),
			bn256.Fq2.MulScalar(c.EllVV, pre1.Px))

		if bit == 1 {
			c = pre2.Coeffs[idx]
			idx++
			f = bn256.mulBy024(
				f,
				c.Ell0,
				bn256.Fq2.MulScalar(c.EllVW, pre1.Py),
				bn256.Fq2.MulScalar(c.EllVV, pre1.Px))
		}
	}
	if bn256.LoopCountNeg {
		f = bn256.Fq12.Inverse(f)
	}

	c = pre2.Coeffs[idx]
	idx++
	f = bn256.mulBy024(
		f,
		c.Ell0,
		bn256.Fq2.MulScalar(c.EllVW, pre1.Py),
		bn256.Fq2.MulScalar(c.EllVV, pre1.Px))

	c = pre2.Coeffs[idx]
	idx++

	f = bn256.mulBy024(
		f,
		c.Ell0,
		bn256.Fq2.MulScalar(c.EllVW, pre1.Py),
		bn256.Fq2.MulScalar(c.EllVV, pre1.Px))

	return f
}
func (fq6 Fq6) Equal(a, b [3][2]*big.Int) bool {
	return fq6.F.Equal(a[0], b[0]) && fq6.F.Equal(a[1], b[1]) && fq6.F.Equal(a[2], b[2])
}// One returns a One value on the Fq
func (fq Fq) One() *big.Int {
	return big.NewInt(int64(1))
}
// Square performs a square operation on the Fq12
func (fq12 Fq12) Square(a [2][3][2]*big.Int) [2][3][2]*big.Int {
	ab := fq12.F.Mul(a[0], a[1])

	return [2][3][2]*big.Int{
		fq12.F.Sub(
			fq12.F.Mul(
				fq12.F.Add(a[0], a[1]),
				fq12.F.Add(
					a[0],
					fq12.mulByNonResidue(a[1]))),
			fq12.F.Add(
				ab,
				fq12.mulByNonResidue(ab))),
		fq12.F.Add(ab, ab),
	}
}// Square performs a square operation on the Fq
func (fq Fq) Square(a *big.Int) *big.Int {
	m := new(big.Int).Mul(a, a)
	return new(big.Int).Mod(m, fq.Q)
}
func (s *Scanner) scan() (tok Token, lit string) {
	ch := s.read()

	if isWhitespace(ch) {
		// space
		s.unread()
		return s.scanWhitespace()
	} else if isLetter(ch) {
		// letter
		s.unread()
		return s.scanIndent()
	} else if isDigit(ch) {
		s.unread()
		return s.scanIndent()
	}

	switch ch {
	case eof:
		return EOF, ""
	case '=':
		return EQ, "="
	case '+':
		return PLUS, "+"
	case '-':
		return MINUS, "-"
	case '*':
		return MULTIPLY, "*"
	case '/':
		return DIVIDE, "/"
	case '^':
		return EXP, "^"
	}

	return ILLEGAL, string(ch)
}
// One returns a One value on the Fq12
func (fq12 Fq12) One() [2][3][2]*big.Int {
	return [2][3][2]*big.Int{fq12.F.One(), fq12.F.Zero()}
}
func (s *Scanner) scanIndent() (tok Token, lit string) {
	var buf bytes.Buffer
	buf.WriteRune(s.read())

	for {
		if ch := s.read(); ch == eof {
			break
		} else if !isLetter(ch) && !isDigit(ch) {
			s.unread()
			break
		} else {
			_, _ = buf.WriteRune(ch)
		}
	}
	switch buf.String() {
	case "var":
		return VAR, buf.String()
	}

	if len(buf.String()) == 1 {
		return Token(rune(buf.String()[0])), buf.String()
	}
	if buf.String() == "out" {
		return OUT, buf.String()
	}
	return IDENT, buf.String()
}
// One returns a One value on the Fq6
func (fq6 Fq6) One() [3][2]*big.Int {
	return [3][2]*big.Int{fq6.F.One(), fq6.F.Zero(), fq6.F.Zero()}
}
func (fq2 Fq2) Copy(a [2]*big.Int) [2]*big.Int {
	return [2]*big.Int{
		fq2.F.Copy(a[0]),
		fq2.F.Copy(a[1]),
	}
}
// Zero returns a Zero value on the Fq2
func (fq2 Fq2) Zero() [2]*big.Int {
	return [2]*big.Int{fq2.F.Zero(), fq2.F.Zero()}
}
func (fq Fq) Copy(a *big.Int) *big.Int {
	return new(big.Int).SetBytes(a.Bytes())
}
func BigIsOdd(n *big.Int) bool {
	one := big.NewInt(int64(1))
	and := new(big.Int).And(n, one)
	return bytes.Equal(and.Bytes(), big.NewInt(int64(1)).Bytes())
}
// Mul performs a multiplication on the Fq12
func (fq12 Fq12) Mul(a, b [2][3][2]*big.Int) [2][3][2]*big.Int {
	// Multiplication and Squaring on Pairing-Friendly .pdf; Section 3 (Karatsuba)
	v0 := fq12.F.Mul(a[0], b[0])
	v1 := fq12.F.Mul(a[1], b[1])
	return [2][3][2]*big.Int{
		fq12.F.Add(v0, fq12.mulByNonResidue(v1)),
		fq12.F.Sub(
			fq12.F.Mul(
				fq12.F.Add(a[0], a[1]),
				fq12.F.Add(b[0], b[1])),
			fq12.F.Add(v0, v1)),
	}
}
func (g2 G2) Double(p [3][2]*big.Int) [3][2]*big.Int {
	if g2.IsZero(p) {
		return p
	}

	a := g2.F.Square(p[0])
	b := g2.F.Square(p[1])
	c := g2.F.Square(b)

	t0 := g2.F.Add(p[0], b)
	t1 := g2.F.Square(t0)
	t2 := g2.F.Sub(t1, a)
	t3 := g2.F.Sub(t2, c)

	d := g2.F.Double(t3)
	e := g2.F.Add(g2.F.Add(a, a), a)
	f := g2.F.Square(e)

	t4 := g2.F.Double(d)
	x3 := g2.F.Sub(f, t4)

	t5 := g2.F.Sub(d, x3)
	twoC := g2.F.Add(c, c)
	fourC := g2.F.Add(twoC, twoC)
	t6 := g2.F.Add(fourC, fourC)
	t7 := g2.F.Mul(e, t5)
	y3 := g2.F.Sub(t7, t6)

	t8 := g2.F.Mul(p[1], p[2])
	z3 := g2.F.Double(t8)

	return [3][2]*big.Int{x3, y3, z3}
}
func (g2 G2) Add(p1, p2 [3][2]*big.Int) [3][2]*big.Int {
	if g2.IsZero(p1) {
		return p2
	}
	if g2.IsZero(p2) {
		return p1
	}

	x1 := p1[0]
	y1 := p1[1]
	z1 := p1[2]
	x2 := p2[0]
	y2 := p2[1]
	z2 := p2[2]

	z1z1 := g2.F.Square(z1)
	z2z2 := g2.F.Square(z2)

	u1 := g2.F.Mul(x1, z2z2)
	u2 := g2.F.Mul(x2, z1z1)

	t0 := g2.F.Mul(z2, z2z2)
	s1 := g2.F.Mul(y1, t0)

	t1 := g2.F.Mul(z1, z1z1)
	s2 := g2.F.Mul(y2, t1)

	h := g2.F.Sub(u2, u1)
	t2 := g2.F.Add(h, h)
	i := g2.F.Square(t2)
	j := g2.F.Mul(h, i)
	t3 := g2.F.Sub(s2, s1)
	r := g2.F.Add(t3, t3)
	v := g2.F.Mul(u1, i)
	t4 := g2.F.Square(r)
	t5 := g2.F.Add(v, v)
	t6 := g2.F.Sub(t4, j)
	x3 := g2.F.Sub(t6, t5)
	t7 := g2.F.Sub(v, x3)
	t8 := g2.F.Mul(s1, j)
	t9 := g2.F.Add(t8, t8)
	t10 := g2.F.Mul(r, t7)

	y3 := g2.F.Sub(t10, t9)

	t11 := g2.F.Add(z1, z2)
	t12 := g2.F.Square(t11)
	t13 := g2.F.Sub(t12, z1z1)
	t14 := g2.F.Sub(t13, z2z2)
	z3 := g2.F.Mul(t14, h)

	return [3][2]*big.Int{x3, y3, z3}
}
func (fq2 Fq2) IsZero(a [2]*big.Int) bool {
	return fq2.F.IsZero(a[0]) && fq2.F.IsZero(a[1])
}













// Fq is the Z field over modulus Q
type Fq struct {
	Q *big.Int // Q
}
var eof = rune(0)
type Scanner struct {
	r *bufio.Reader
}
type AteG1Precomp struct {
	Px *big.Int
	Py *big.Int
}
var Utils = prepareUtils()
// PolynomialField is the Polynomial over a Finite Field where the polynomial operations are performed
type PolynomialField struct {
	F Fq
}
var circuits map[string]*Circuit
type Setup struct {
	Toxic struct {
		TX                    []big.Int
		T                     *big.Int // trusted setup secret
		Ka                    *big.Int // prover
		Kb                    *big.Int // prover
		Kc                    *big.Int // prover
		alpha                 *big.Int
		Li_B_Ui_X_A_Vi_X_Wi_X [3]*big.Int
		alpha_into_G1         [3]*big.Int

		betta_into_G1 [3]*big.Int

		Li_into_G1_gamme [3]*big.Int

		LI_into_G1_delta [3]*big.Int
		Ui_into_x_value  *big.Int
		Vi_into_x_value  *big.Int
		Wi_into_x_value  *big.Int
		r                *big.Int
		s                *big.Int

		delta_into_G1              [3]*big.Int
		betta                      *big.Int
		gamma                      *big.Int
		delta                      *big.Int
		x                          *big.Int
		zt                         [3]*big.Int
		verification_side_by_delta [3]*big.Int

		proving_side_by_gamma [3]*big.Int
		RhoA                  *big.Int
		RhoB                  *big.Int
		RhoC                  *big.Int
		LI                    []*big.Int
	}

	// public
	Pk Pk
	Vk Vk
}
type Pk struct { // Proving Key pk:=(pkA, pkB, pkC, pkH)
	G1T [][3]*big.Int // t encrypted in G1 curve, G1T == Pk.H
	A   [][3]*big.Int
	B   [][3]*big.Int

	B_into_G2      [][3][2]*big.Int
	C              [][3]*big.Int
	PK_LI_G1_delta [][3]*big.Int

	PK_LI_G1_gamma        [][3]*big.Int
	Li_B_Ui_X_A_Vi_X_Wi_X [][3]*big.Int
	Kp                    [][3]*big.Int
	Ap                    [][3]*big.Int
	Bp                    [][3]*big.Int
	Cp                    [][3]*big.Int
	Z                     *big.Int
	LI_2L                 *big.Int
}
type Vk struct { //verification key
	Vka           [3][2]*big.Int
	Vkb           [3]*big.Int
	Vkc           [3][2]*big.Int
	IC            [][3]*big.Int
	G1Kbg         [3]*big.Int    // g1 * Kbeta * Kgamma
	G2Kbg         [3][2]*big.Int // g2 * Kbeta * Kgamma
	G2Kg          [3][2]*big.Int // g2 * Kgamma
	Vkz           [3][2]*big.Int
	alpha_into_G2 [3][2]*big.Int
	betta_into_G2 [3][2]*big.Int
	gamma_into_G2 [3][2]*big.Int
	delta_into_G2 [3][2]*big.Int
}
const (
	ILLEGAL Token = iota
	WS
	EOF
	IDENT // val
	VAR   // var
	CONST // const value
	EQ       // =
	PLUS     // +
	MINUS    // -
	MULTIPLY // *
	DIVIDE   // /
	EXP      // ^

	OUT
	flattening_code1
)
type Circuit struct {
	NVars         int
	NPublic       int
	NSignals      int
	PrivateInputs []string
	PublicInputs  []string
	Signals       []string
	Witness       []*big.Int
	Constraints   []Constraint
	R1CS          struct {
		A [][]*big.Int
		B [][]*big.Int
		C [][]*big.Int
	}
}
type Constraint struct {
	// v1 op v2 = out
	Op      string
	V1      string
	V2      string
	Out     string
	Literal string

	PrivateInputs []string // in func declaration case
	PublicInputs  []string // in func declaration case
}
type Proof struct {
	A_total                            *big.Int
	B_total                            *big.Int
	C_total                            *big.Int
	Hx_Tx                              *big.Int
	alpha_betta                        *big.Int
	CLI0T01                            *big.Int
	C_hxtx_delta_AS_ADD_BS_SUB_RSdelta *big.Int

	PiA1 [3]*big.Int

	PiB1_G2 [3][2]*big.Int

	PIC1          [3]*big.Int
	PIA_ADD_Betta [3]*big.Int

	PIA_ADD_ALPHA [3]*big.Int

	PiA  [3]*big.Int
	PiAp [3]*big.Int
}
type BigInt struct {
	*big.Int
}
type ProofResponse struct {
	A_total                            string `json:"A_total"`
	B_total                            string `json:"B_total"`
	C_total                            string `json:"C_total"`
	Hx_Tx                              string `json:"Hx_Tx"`
	Alpha_betta                        string `json:"alpha_betta"`
	CLI0T01                            string `json:"CLI0T01"`
	C_hxtx_delta_AS_ADD_BS_SUB_RSdelta string `json:"C_hxtx_delta_AS_ADD_BS_SUB_RSdelta"`

	PiA1 [3]string `json:"PiA1"`

	PiB1_G2 [3][2]string `json:"PiB1_G2"`

	PIC1          [3]string `json:"PIC1"`
	PIA_ADD_Betta [3]string `json:"PIA_ADD_Betta"`

	PIA_ADD_ALPHA [3]string `json:"PIA_ADD_ALPHA"`

	PiA  [3]string `json:"PiA"`
	PiAp [3]string `json:"PiAp"`
}
type Token int
// Parser data structure holds the Scanner and the Parsing functions
type Parser struct {
	s   *Scanner
	buf struct {
		tok Token  // last read token
		lit string // last read literal
		n   int    // buffer size (max=1)
	}
}
type utils struct {
	Bn  Bn256
	FqR Fq
	PF  PolynomialField
}
type Bn256 struct {
	Q             *big.Int
	R             *big.Int
	Gg1           [2]*big.Int
	Gg2           [2][2]*big.Int
	NonResidueFq2 *big.Int
	NonResidueFq6 [2]*big.Int
	Fq1           Fq
	Fq2           Fq2
	Fq6           Fq6
	Fq12          Fq12
	G1            G1
	G2            G2
	LoopCount     *big.Int
	LoopCountNeg  bool

	TwoInv             *big.Int
	CoefB              *big.Int
	TwistCoefB         [2]*big.Int
	Twist              [2]*big.Int
	FrobeniusCoeffsC11 *big.Int
	TwistMulByQX       [2]*big.Int
	TwistMulByQY       [2]*big.Int
	FinalExp           *big.Int
}
// Fq6 is Field 6
type Fq6 struct {
	F          Fq2
	NonResidue [2]*big.Int
}
// Fq12 is Field 12
type Fq12 struct {
	F          Fq6
	Fq2        Fq2
	NonResidue [2]*big.Int
}
type G1 struct {
	F Fq
	G [3]*big.Int
}
type G2 struct {
	F Fq2
	G [3][2]*big.Int
}
// Fq2 is Field 2
type Fq2 struct {
	F          Fq
	NonResidue *big.Int
}
type EllCoeffs struct {
	Ell0  [2]*big.Int
	EllVW [2]*big.Int
	EllVV [2]*big.Int
}
type AteG2Precomp struct {
	Qx     [2]*big.Int
	Qy     [2]*big.Int
	Coeffs []EllCoeffs
}


