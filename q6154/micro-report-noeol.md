ANSWER Q6154 9704ad7d

# r18-P-E31DATA — exact N25 E3.1 finite computation

Source: `xiangyazi24/mazur-p2m@40a40768c6369fa8a0cfdd5d538839c44438e933`. All arithmetic is exact. The embedded stdlib-only checker independently recomputes every claimed coefficient and identity.

## 1. Modular units and relation

Definitions:
```text
B2(t)=t^2-t+1/6
E_g=q^(25*B2(g/25)/2)*prod_{n>=1}(1-q^(25(n-1)+g))*(1-q^(25n-g))
P0=E1*E7; P1=E2*E11; P2=E3*E4; P3=E6*E8; P4=E9*E12
U_i=P_i/P_{i+1}; U=U0; V=U0/U1=P0*P2/P1^2
```

The exact expansions begin (coefficients are indexed from q^0):
```text
U[0..40]=[0, 1, -1, 1, -1, 1, -1, 1, -2, 2, -2, 2, -1, 1, -1, 2, -2, 2, -2, 0, 0, 0, -1, 2, -1, 0, 2, -3, 4, -3, 1, -2, 3, -6, 8, -8, 6, -3, 3, -3, 7]
V[0..40]=[0, 0, 1, -1, 2, -3, 3, -4, 4, -5, 5, -6, 7, -5, 6, -4, 4, -4, 4, -6, 3, -5, 2, -2, 4, -2, 6, -1, 0, 6, -11, 10, -16, 10, -18, 21, -24, 32, -25, 28, -14]
```

The complete exact arrays `U[0..5000]` and `V[0..5000]` are emitted by the embedded checker with `--dump qexp.json`. A byte-identical auxiliary archive is pinned at `https://raw.githubusercontent.com/xiangyazi24/AnalyticCombinatorics/6ec28d99a2fd5915c2622d979220131a8e845582/q6154/qexp.b85` (Git blob `71476bb782548700ddb7a46217f61ac62f63f481`; base85 of zlib-compressed JSON).

```text
sha256 CSV(U)=b4547b68c5090115b688b56353c96855a587d3a1b821b890ed868630438d6802
sha256 CSV(V)=6e22a69676ee0d36652978f8e3802a60e8fbde51ab5ea448b77f1ff66cc130cb
```

The primitive relation is:
```text
R(X,Y)=Y^4-X^3*Y^3+(X-X^3-2*X^4)*Y^2
       -(X^3+X^4+2*X^5)*Y+X^7
```

It has `deg_X=7`, `deg_Y=4`, content 1, and is irreducible because its reduction modulo 2 is irreducible. The 40 monomial series `U^i V^j` (`0<=i<=7`, `0<=j<=4`) have rank 38 through q^37 and rank 39 through q^38, so exactly 39 coefficients determine R up to scale. Exact substitution gives `R(U,V)=0` through q^5000. With `G=Delta^3`, `F0=GU`, `F1=GU1`, the cleared weight-396 expression is `G^7 F1^4 R(F0/G,F0/F1)=G^11 U1^4 R(U,V)`; its common q-order is `33-4=29`, hence it vanishes through q^5029.

Divisors and bidegrees:
```text
        U0  U1  U2  U3  U4
p0       1  -1   2   1  -3
p1      -1   2   1  -3   1
p2       2   1  -3   1  -1
p3       1  -3   1  -1   2
p4      -3   1  -1   2   1
```
Thus `deg(U)=4`; `ord(V)=(2,-3,1,4,-4)` and `deg(V)=7`, explaining bidegree `(7,4)`.

## 2. Universal Tate series and canonical model

Use Tate modulus `Q_T=q^25` and torsion parameter `u_T=q` (`u_T^25=Q_T`).
```text
X_T=sum_{n in Z} Q_T^n*u_T/(1-Q_T^n*u_T)^2-2*s1(Q_T)
Y_T=sum_{n in Z}(Q_T^n*u_T)^2/(1-Q_T^n*u_T)^3+s1(Q_T)
a4=-5*s3(Q_T); a6=-(5*s3(Q_T)+7*s5(Q_T))/12
Y_T^2+X_T*Y_T=X_T^3+a4*X_T+a6
s=(3*X_T^2+a4-Y_T)/(2*Y_T+X_T)
A1=1+2*s; A2=3*X_T-s-s^2; A3=X_T+2*Y_T
b=-A2^3/A3^2; c=1-A1*A2/A3
```

```text
b[0..20]=[0, -1, 5, -18, 53, -136, 315, -673, 1346, -2547, 4597, -7964, 13311, -21554, 33931, -52083, 78148, -114869, 165717, -235030, 328169]
c[0..20]=[0, -1, 4, -11, 24, -45, 76, -119, 176, -249, 340, -451, 584, -741, 924, -1135, 1376, -1649, 1956, -2299, 2680]
```

Tate to Sutherland:
```text
Nx=-b^2+b*c+c^3
K=-2*b^2+b*c^2+3*b*c-c^2
B=-b^3+3*b^2*c-b*c^3-3*b*c^2+c^5+c^4+c^3
x_S=Nx/K; y_S=K*(b-c)/B
```

The compiled Sutherland-to-canonical polynomials, in full, are:
```python
def sutherland_to_canonical(x: LS, y: LS) -> list[LS]:
    Xcore = (x**5*y**2 - 2*x**4*y**3 + x**3*y**4 - x**5*y +
        x**4*y**2 + x**3*y**3 - x**2*y**4 + x**4*y -
        2*x**3*y**2 + x**2*y**3 - x**2*y**2 + x*y**3 +
        2*x**2*y - 2*x*y**2 - 2*x**2 + 3*x*y - y**2 -
        2*x + 2*y - 1)
    Xc = -(y - 1)**2 * Xcore
    Yc = -(x**5*y**4 - 2*x**4*y**5 + x**3*y**6 + x**6*y**2 -
        8*x**5*y**3 + 13*x**4*y**4 - 6*x**3*y**5 +
        6*x**5*y**2 - 10*x**4*y**3 + 2*x**3*y**4 +
        2*x**2*y**5 - 2*x**5*y + 4*x**4*y**2 -
        5*x**3*y**3 + 4*x**2*y**4 - x*y**5 - 2*x**4*y +
        12*x**3*y**2 - 10*x**2*y**3 - 6*x**3*y +
        3*x**2*y**2 + 3*x*y**3 + x**3 + x**2*y -
        2*x*y**2 + y**3 - 3*y**2 + 3*y - 1)
    Zc = (x**5*y**4 - 2*x**4*y**5 + x**3*y**6 -
        5*x**5*y**3 + 10*x**4*y**4 - 5*x**3*y**5 +
        x**6*y + 3*x**5*y**2 - 8*x**4*y**3 +
        3*x**3*y**4 + x**2*y**5 - 2*x**5*y +
        4*x**4*y**2 - 4*x**3*y**3 + 2*x**2*y**4 +
        5*x**3*y**2 - 3*x**2*y**3 - 2*x*y**4 - x**4 -
        2*x**3*y + 3*x*y**3 + x**3 - x**2*y + y**3 +
        x**2 - x*y - 3*y**2 + 3*y - 1)
    Wcore = (x**5*y**3 - 2*x**4*y**4 + x**3*y**5 -
        2*x**5*y**2 + 3*x**4*y**3 - x**2*y**5 + x**5*y -
        3*x**3*y**3 + 2*x**2*y**4 - 2*x**3*y**2 +
        2*x**2*y**3 + 3*x**3*y - x**2*y**2 -
        2*x*y**3 - x**3 - x**2*y + 2*x*y**2 + y**2 -
        2*y + 1)
    Wc = (x - y + 1) * Wcore
    return [Xc, Yc, Zc, Wc]
```

After removing common order -2 and normalizing z(0)=1:
```text
Q(x,y,z,w)=-x*z-x*w+y^2+y*z+z*w
C(x,y,z,w)=x^2*w+x*y*z-x*y*w-x*z*w+y*z*w+z^2*w-z*w^2
```

Exact canonical expansions begin:
```text
x[0..30]=[0, 1, 1, 6, 3, 13, 0, 11, -15, -7, -35, -15, -22, 27, 34, 74, 54, 20, -43, -116, -140, -83, 12, 190, 250, 244, 28, -246, -540, -528, -267]
y[0..30]=[0, 1, 1, 5, 2, 8, -2, 4, -12, -5, -20, 3, -3, 34, 17, 30, -6, -27, -60, -55, -30, 64, 110, 144, 72, -64, -223, -304, -267, 41, 377]
z[0..30]=[1, 1, 5, 3, 9, 3, 6, -4, -7, -16, -9, -8, 15, 20, 31, 26, -5, -37, -63, -70, -7, 45, 121, 149, 87, -48, -209, -335, -250, -16, 289]
w[0..30]=[0, 0, -1, -1, -5, -2, -7, 3, 1, 14, 12, 17, -4, -11, -47, -34, -30, 20, 69, 104, 83, 22, -136, -215, -250, -113, 169, 443, 582, 440, -120]
```
The checker verifies the Tate equation and `Q=C=0` through q^100. The constant projective vector is `[0:0:1:0]`.

## 3. Birational maps

Put `A=y+z-w`. Canonical to plane:
```text
U=x/A
V=x^2/(z*A)
```

Put `D=U^2+U+V`. Plane to canonical:
```text
Xc=U*V*(U^2+U+V)
Yc=U*(U^2*V-U^2+V)
Zc=U^2*(U^2+U+V)
Wc=U^4+U^3*V-V^2
[x:y:z:w]=[Xc:Yc:Zc:Wc]
```

Exact ideal certificates:
```text
Q(Xc,Yc,Zc,Wc)=U*R(U,V)
C(Xc,Yc,Zc,Wc)=-U^2*V*(U^2+U+V)*R(U,V)
Yc+Zc-Wc=V*(U^2+U+V)
Xc=U*(Yc+Zc-Wc)
Xc^2=V*Zc*(Yc+Zc-Wc)
```

For the reverse composition define:
```text
A=y+z-w; B=x*z+z*A+x*A
PX=x*B
PY=z*(x^2-z*A+A^2)
PZ=z*B
PW=x*(z^2+x*z-A^2)
PY-y*B=PW-w*B=-x*Q-C; PX-x*B=PZ-z*B=0
```
Thus both compositions hold on dense opens; the checker also verifies them on q-series through q^70.

## 4. Cusp dictionary

```text
canonical       K1   (ord U,ord V)
[0:0:0:1]      p2      ( 2, 1)
[0:-1:1:0]     p3      ( 1, 4)
[1:1:0:1]      p4      (-3,-4)
[0:0:1:0]      p0      ( 1, 2)   q-infinity
[1:0:0:0]      p1      (-1,-3)
```

## 5. Reduction at 2

Every numeric denominator in R and both maps is 1, hence has v2=0. The primitive polynomial denominators `A` and `z*A` have 2-adic content zero. Reduction gives:
```text
R_2(U,V)=V^4+U^3*V^3+(U+U^3)*V^2+(U^3+U^4)*V+U^7
```
It is irreducible in F2[U,V]. The integral composition identities above survive verbatim modulo 2, so the reductions are mutually inverse birational maps. The odd separability witness is `ord_p0(U)=1`; also `dR_2/dV=U^3*(V^2+U+1)` is nonzero.

## Stdlib-only checker

The following executable code block contains the complete readable checker source losslessly compressed with XZ/LZMA2. Save it as `checker.py`; running it recomputes all five parts. `python3 checker.py --dump qexp.json` also writes all 10,002 coefficients.

```python
import base64,lzma
S="""{Wp48S^xk9=GL@E0stWa8~^|S5YJf5;9FQ4{#^hOh(bq-BQwKy4>SE$m+hy=@aif<Hp(x6uSRc*v2(<=-PIwnI`zDwa;;f-*r5OA
G=zJ?1kb@noSwx+_-=MkJPSsPHibG4SDE<1r*#1kqMW|x`@tcUVKA<(<O9_Mmx_#5isZ~6gO<UX0*<5T6|lWx+M;y)u#cd2=;fyJ
_Eg2PpcDu&J3*$DOVyXq8><(HIX!~Ap~Jdr(Sxv7PuSNHeEXj)^2PV!!73mc{w({PG67I$+jcS-(1w(_xsD=><r9V`#P*iP*w8dV
=!=fhgR0;jMHJE$kBKm%TEHG~{$Y1%Om2%Rk2r37&W|79wA2T;B?}KtwH3v6Ct}X=714Hag2`&Nh^}(JR4}g3juRq|WI<cIzt9-d
QDo_$G(haO2IO@idRjv)Tr!YqOZe%t9g#R^L5h02i-lQrf(U|D!$5(S`*@(lF0VcnZ!2m)PF-_J>*tViW;>!IvO(a6ttj5kq!fbR
=4|VLB>0GeH)?n+4Zx~``}p?US1$iFBkqET`eMxk>o*a<$x0(tEIng1tfa9=!}%Q0wJ-lGU}bmnR=J!B=+BVnh510Jr0E*$G$!n2
ati+s;0-apT7+*@aE44S;aQ-4^h;`cQ0Lg3*}1FZrFQt4^K|)+kx+^JP1mXQ7;Vd!=4DI|2ELXg0K|A|Uu#$|3hviYTUih~>S~h|
BJ;WWLX-s<&%rfIrt`r%M;}t^ZxC>KPaR$CJY{urUJ3L<i|6RTRYqK0yMIRXHlZ=0Xm7txm7VXxCoxW%hap6>1>vPwd0riwx7J)d
Qjjw$0Fg0U<(wM8^xRL2eAi`q+%*D^zq;d=g&Y(jqE+$%hcZUcJ>?>qXvRR69HMB|%C}BY?mYym;iX~*wWp(Arc^H`DDGGLe)tjF
vJeK(d-R$#c`{oCi6>zV)mdW>?r$Vtl^vUe*XW1FUtki`F_;O`0nb(1#v%>yI>D?E6jxM?rs%4XDMyhs(eP1H&S>r-ZA(=G_eknW
LrsL)5(dS^EKe+7LOV$*lRmxZ)IwqHI}~!$rP*F&*9n*a_)(%@)ilGI9FtGZtCkH(aK8Rmk6I#Jrk-bfR<$)2xi)7`G6_jFyN|Zp
>~qw>jK7Y~td2SVeHu@9#rZ0G)ZF8$Jh1)aba#jNPA?audo1+qiZ7COtae!*BXUa+7NHk4Yt6~%+q^^bVAgbiJO1ni*lrrmfM2?a
qeek}i&dNE=q}2X4<6Eu3O0EDF$bcdtq|@<LZTeqK@BW)N^R)1kiv$x@3qChZAbGIrTfp9Kfh}X(-=D%tj^H+b(1PJESYZ|$?aIf
P_~wQcJUWjO-B2m)J)%~4`Q}M#Zo>yGO_dFlM<18TZTWHM<j$ABU462`J5t0x;b48X5%N2&oa#~2;$w<+qU1#-CavZtV*SV_>zS>
!`anfVg*Wz*9L&NaSI)_u7++Q?s*4USOz1!DqnD~m<Bsjb>jm-8SU+36j?qsGr1DnQ<|^Nng+C4-D{);I(Z^5RRyF!>i5gnc^UTS
Z>Ocd;V$Y}dx56)xlXg>f!0axfUiLdOPV%m!;7`M3S<s+GkwV7s*32A`Lqu6KaV@236;%NG8~GUw4F|!FP57rLp1MzoFFs`ZrYpo
z>}3kS=$w|$5p#a$Wa4u(rG>fq7o5zKX@1D&3T&A6H4i@shT}t1#Q+5{-&*=hiC7bsoI$_Tn1ozsO@ZMi6_Hv3J%dnGN+<@0<<QO
2L?7K2@Tv>?iZQIS_o3Im??s;YET!Sg&oh$?4D<Z+jZK|#?5*;Z9<^&!}EjfLBOq$+`Vt|shtpc6#S>s8hK^R9=Y>Q(BLcoG)k2r
7r75leir0bx}tz{#-A5<Q0YkJGV2jMZwhh6$WGLKXD$~C39AZT>G@QW11%Jtm4^gTEg=2mu=t@vsq`Riauss@<QVlzgot!X{4SRz
4~BTh@E=f_Bb3nSQ&O<RWf7~XRmrG*(N&E!!%gE1U13$1u?LtUPlxJl?H8<xEDe8#0IP4zqRH0aKRj|kyq?K1l;jfz_aqA(E59`h
t}CX$NfYfvNr(b%2L-Lv%oJW<;nWumz|JM6E?_S03=~f+c{!)QMu|MipSFgL`b;RA;dSh6&h1Q{UbTW7!j6Y)u@r{enRe2Pc%wtp
=F#!I>0>QU_Pe*mS*$d#^!K`1K48?%w5EHIUe}t#zMOUu1ulJ^f}tO;YeH3pv!0aluuZ!<Birw%z?<Y*O<p6@e2*CJ3#9@CMO5pb
n~Xurs)fq{uq8Z-)r`i74?pEQw_6JpL6iLu$7xh5qW$vjNK3HG?X)UGp`rxp-0EzoAyaZCcW43T2#AhF!-2uqP0$|P*Qk-^0&@c}
=5=JxTGz$^Jq|YLP94^{h0Qyq{G3aypp9keT&2HW{(%gWw#>}7%ix&ueT-e%8RbzyUCj*+8hmEG_e@!Kg)~%d$}uX`cnmf-KsP=n
^56-R5s$RwC!Mk%$1eDac_;HI9{YF~Jl(`(Qq_&?k`up;x)y@}tqk<?*D4gC2cjqT3I+c>SEos|_ydL+o6v~KRw+=WO3~-O>Lv=a
m1c2$%)JuSB1YdtI)y$N_7{aihz9Q&5;<B)T%R^)wm`~G9a=Y#ZLtjzeh5at854g6Q5BmwY2qWZ<>}v_1%M#*Wy&qx`E+$uS_79C
&0Frdz*Q?qc#L#VB}9C%u+{Ia%tTvDqL{L%oCY<h$uV)$0o}@|EWd5bK*%XTx3yOyw6;=vgY$kd$R50NIc<2^1rTU0=yHwIM@>dw
04-#jE{{=Mif(Yk!rpwe&bQ)ZxU(5k3yIjje=tz>2EK5I2ZT^{3F;G`g=pk(Guuk2mMR?C1MuW1L2Ig6Wl02?%~5()R3ia(vq)m1
cBeg^QM%2#Iegh1ba6?JjCy+`zQdN5kToDHyh+-*p?ndTO2Vyx;YoH#Ns?0kqO7IK8T3&^harog$bwlJx$t8&vI;{<$`hptd<1s#
y%G14aOdU{9Y(leKLo1wYa^z-RwVbj_z66?DA3_<6h)%*D<h4J7d!~k`bN@pzoTEvh)54gK{H3abrMOK|NY9XwStr`Ccrx=e3S3+
UgVgC%Z>>|N8>`<$_Oei7Nrx~%Cwrx_-OXa4sAQiLHqpb)1lgF=P|6)JQ{@HknAA=up@8jFSue-*U^YOb+uvT7Wg(QD?@Zb<7P%d
xTYeVe$#?E_n73_d4tZ!TS;h2>ttjXt6H-f&ROy8I=?gtOu6+#G9Rq+)z^Q%!H)c)3wdrb*C-vF1U9nVf%2=z9c6f`u%^i$thKN#
-?I-QirlPk9b6Sh#?$@fb%cta%$?e+x@9LX784hb6cJ%#fm`d*z;1hY1*7_NRY;aJ#KB40Dze562&2O1OF++!lz8Ud#zfsa&Y#ju
gd3JXtKs7!olTj_h}(dcTY+sehW?$jNn39fDI&^}{6)N%!}ZL3hj0dO=7AGa-YpqKt7(y0=hf(NG1$oetCorP^SOxfJCmU<nc3Qk
Riy06!bT|C7G7Kd6?Erv1O-iLl}wI#v`y9vpM$i;QXQIcw%3(06)TaT);79MbghfsmteALLw3)T8Umo?U1+`LPWjHY-~raaK1F)B
MRwP|(8=g^OiSq6Q7Kla$lK9F6$^r%BlB&TwmZl>@XiEBFN<ofv68t>|E9>e&VGF$OEydl-_|$R9W5^}OO9tFkt<bHNoHUH)c>BU
qJ{GHRF9}-m5z4KNpX&UMV_LEck^?5>*hATS^9GlRXtYZv5)D$2HvzIp~^GN*!t5PvJ;C(wBRjUcs$zJZ5Y#NGWoACp<p$g8Rn9O
;A5}H+{438|LBVuo0a+@JOVO`X@J5B8IztqL{@xf@Zy~)K@-v9X@BhylW(9Q0N2?$O%WaOhp0z%t${*KnDY9ZMctnJez}CMy1}&a
8Li&|Ny~v{z7+?b-ZE5W{hp_~Lr?{kTf~iazl8h!19RrT=G$}rkeVSr!%bCu{YOraw*@PfqGsEvI37LDL9kVS@ZB}NF2cw+Tg;5n
xnV~7@?A~3k3XtB$eRU_a(99uJU|zp5?P%G7DZoL!P#21d8=++J9ov0`ImK_b)YYrC0x!qL@4{wS2S-cX)H<RpTjt%w;ky^y)sc7
y+XZ&5d&*Z6_3CUBuhe3_$B&C9&4d?Dt+`Fm9UeIg};k&d=ttc9xeU6qU>o>KTw9PWEyULhBawlw2{AsHMV8OWZqmy5)xW@)-6gP
;4;lQbTXW^sH&|*q-*=n(dIP6y?||o4+GpBldQmY3WQPO*|~hs)@Hcj)yP*WEF|R78&Q;R#BtpTb;&vFl${7ySp|=THKD()y)B(}
FS-lxpp{q<dgC}p-jca}zen--2RQi8Lri=<Re09U&22OLOT}2Ac7`OotK+{5t^8_&GOs;;uaoj6o&~tCX9!28F#e<QG{>}jIlh2W
CxD(nRhG15uJB_(_`n!*UxLGy7>00x|IvlTgV$dFg!=nFF4bM%zhzu%yW<GH<Ts3c3F&a)=6ZX$jka}<UWcPD5gy=-c|avf@K+*l
QpJxRR?{4DtX1nvg7DDzx${v8u+fpDM8dH%wKQZ?2ku<^K7%0Evc4Dd^OvrYs$;lM;84e83;*d|?qQmFTdkuCIqPKEFkul7*#env
RH2QXqUEQN<g&%qlFvKZ>@U~`!iOE=rySVq6Qwj0<E3fywu}0#@Q5<$t^@#r19>P%Q}EzN8w+6oL;G~)po9GeD@!f}@9uJPgJ>Qu
NzV^kKYaRv48Ej|fJ`|bcX)SWJez?nbSKJF5sr{KtLNlaHC*Yw6m%zdrdK*xdw2IY;*B`lXvUNSNt8BzR6^xASkK49G>+sL);X#n
o+FYE(Ccp_a)uBTFiG(2TH@X;ZC^dCFHmM%@I+X?8y`n7W?6B|V19<gSMCFW2s_@0E+4*n)0Y9YPhqCOWCZ>AQ~g05UsqWfptKQf
naJgKA*7X1?(J~~f$RBa*>8LwfJawELMl<nZ@^{3My?__rVUo)x@2l1++GhnL$?p#;cnNq!E1Ua@_pChz{Ul)Nb3(Snc7T9>#R&{
SBs+dK{<qEm(xavSJ^-<RU+hIgg1xM>?1zc^qN`nyn;K=*@WD#Q{i?u*OeUE(!bMzg911BsO7JS7$@w8(EzfEHMihJo&>|P0{x)o
l56)IbWVOHGcxf}idiz*feg*6WT1Rg8B$IXOl5M?BajMwtM4nK8A`^4Bb9nnjUf(-`ikPt&O3NG@-?-}nNTkSr?r=h2d=^)`%e9U
Z*B|Dqq9nlqX4(EPxgfp1;Ay!Ve?Dh9Kgz>r<EldnFa~oIF+nmAgIEXVLw6WvWmTs9Jo;lAVQVl(d28$3OuN+=<Dm(R0Mj-cx^x2
ON#ly6jTWu$Wg=3&H=O?>PC1!Lbwu%{;Q+M)t9(#5%ox9;^)#6(;c5ql|Knj(D-aeI<no*DLrb0|LkbTZJ>P4qH{$-1?ZpAF+FnA
fI%J9t2gKN9*XLFm3QgUOoi2XZY@q#A}N@{5*}j=;ZVC9;x#%G-1pckvT7;e)uj$hR+b^onrxeEzj6~MiHS%t4(k`f5F{#M6l-|u
uZF~M&{nuHK(jnBk38%Yy!S@_7&$~hxKyTZtsuHZA(7?Oe&U8Lz3eE8OMBWo9~o8lgDyWs%E9cLC|oUjB{Z0Vd9~2A>{f0l1wZ|!
?-N%0E$t7oPaI3}y=W%EWY*^rbcBsSp3+r#C0%9l8C$c1RlkQ<{|f7vf-3qx%{<OPa}vZWx=SI6pSye`=VYTMIva+j3-T-Ee{5(N
L6a{}(l|!0Z<JJcY9++s>6W&=vo3Pl2dP<rAj1tnFM)6x4da?70<%GHbnch-!M-&au@9nVU;EZzS)_jiK_CAJBu1=<5RTN-zhH0*
LAO&$NWXNT76tSrn_^i`uO|kkN%|Y*W+`O6Ye^toRLeu*3&7a6S0-$e5YuqX4ZUhI*93T%fmJM+EmkIEz}Tv$gR*!j6?||qG({zk
P^YnGC7o1A*lql5<kBab0hn_VA?tyxAZE$Lq3D+p8#rPqkt5lAbd+JtHg`BtHU1MqnLQj?AGkP&`c1xQKkFR;-HKXB!>n#wJ3*jx
c}99tHLEVM0M~9<;fyuT2H#}oFwn->8lQRv-uD=3<`YIW6A2Pu3;Ey`Gj*Cewn|UY)KMxg#MsZoV4zV=xTBcEGM_8BDX}fXiQ(b@
3OE9eRF}YtuB?aCy5$gqnEu!G14JVizGv@?*j+w`J!@*LPe6m-h=JS-0LHXVDse5fmawMLW_EJF)hmu8t5WmCmh{8zo2o*b^&}t|
nXH#?UY89hAKQ@eVlHV+6fVkO)R%5tuKk4k8b@Z;Ix?f9{xl&Rg)litoC(_q&nUzl)v+F`-zgh=_EgobmWi@;{w8<*ui`7=sflyJ
!-1}XTv0WBY5&Q-AcbMk@MN?m_kHas65L;YUOG*+9v}ALGL4*B?7q6oRxOZGl^_dA9Q!B#<aoX!NRQ};8`{&yg85~^mo-x*-{TBs
<wDI!`O(Sle=nr?^O~6ke|6>QcY0+(R&jlzyCB~STKb!F&}t!LybQFAlbB!yLB6#TQL$DeU%$DbnoJ){Pam7K)jCPVewM*>8Vh*b
zkr`ZQN+`I^4l&gW|E*zq+C`_ab$YXnV4>P{XX>>>@z>v#L+7iUHE3RW@Z>Dcm@I>w#{PYRxnH0DglYya3EC!&M*Z9bO58uUa%Fp
qC-W$1OZeu(MjG<2zzl8TT)f54BcpqOx%dPz*{IvNK?`CfNsIzF&s>yhH_Gr&m+En*qN3LMeQ@5AUJl76KCWS>u0BL@Ioi?>m%fQ
0Q~T;v%y8_Q_Ds;eHVQa+?V=xBsX`v`VPEr-7B?W2C*|?&k~b|tJlqKtkw@?iw?|7CTqTyfl)og?Gg6>fq^sH8R~erUetv%v3ZY~
hSa)pEmgWfRIHR2SzF?aPiYWsy_!!AH!V*xtIvYy%%C|vYm8kT)U5KDSTB@`jniu#pNX07&T~f>jBU|X$&?<0(($oS?X)%b>LW!4
;r$r}MVG_in^3<EuINgGV$;%_VQtouiN!hxN4yMYjOyYZ9KLjQhp|}OQCMCK1sj5WOVk+Xc5;nG?8mkc`~R*RjcP(Or5{mXJGK!;
571D|LyEnE01@s<IN7<oigI`<&40Wwk^o?Zl@c6EVHDv@bNV9fb(LQ$;Q#ajYu|XPfQxmh99Wq;OpbhU!#(v{Y?X3Yg0TCyih}`8
*Ke%Py`df2Nmz?@>BF}1i2>#sTnZ^<(q0C?L#k*7NEG#`;vGkGd(2ADP%U8U0R}p*g)gIQ`q%*_u(xnmy=d+evjhU?dN$1;ZJp+D
3zqqc#)e1p&|1Qqfg<WS&2xW_a@-sVrn4y6)Bb)d#y+F1Iyrhbxw8V#bO;+iYkQk3<WpUMxSfGsmhIoa&!ve%G?!JQFY^m|l)Du`
d|vBV__$A3mK63y5!GEZR;s+h7VCrSnQ_>qH1dS4(CPIggwH2avj_>{Ef$zf;44w<iy7DFW9QHT{M|y?jccpr8W(W}zlB(5ROXn0
gHLp#>e0b#7ge+o-DxJTpAs<>f3W=bb4RGSqm_En<>YfMYNga)1(*w&eNfjQ+?9j?vR92xUstvqD#yfs0_UQHnZ!$CBkU$|Xl#Ar
;t1p|xv%Vfat7QF+d`=BR6+wu_KQVI$dfvT&K>kZRb`#o)(n|LNC4cR=QxK8!YYSwMS@L^)*IL}dR+OB=@O4MH#R|6JU9AZ_tR!P
gNKp2JBSyPEk9sv`grOIo+s!IZB;ch)%5Z{yg{Qsx3>)lEv1T69fNJTL%NaiAHkoLkB#t_9*mavNvga|bRQS59wu;dM*EOpe*evG
%&$ON`l6Pdp>gOpZSDUrC24%P{k%BdbllJPiwn$Nrm8I_RLN(AHXM--YNdRpQx+W&*51TC{1j{t+GId^APgw$C8Ke>HE^xsBKj8>
<3@FPehTshy`IzTNgvQeUe19`E#Y3gVSm?LKZD$Xv(R{`I#n&*QsM%O<Jo*o7=0?~Fh#sSf!%p8s@x%GTlk#g2(<++TVLrgdko%I
uWr6pQWF1IlXQa96AM3Pey^AHriSf_bKa+&C=yFvGYpxX=kchiuB!u_+VC_&jQ&aI*+l|*G=aA-N>IGq>|q;*J+P+4FhLbJ`h75}
@L%f%;}J7<#hBu9$&?^#Za#qM!yM^a4B_Yz?<H9~oWJWly>J(Wa@Z1=t5fy2n9^<dqVv@KCR+23+=-&gr`1}oYsX}+ZdF3ycr!Q)
Qr6G0{w@{-9Qu{boK>g6TH0)r#>_t5!kussCSQATG1h%rT%I2+=HQM-3LJ1y9h)g%CXrh!>KJ)}UK0i|K1@WKQRaHoSp-ZhYjXVQ
s70c=-Idt5Cl)mRCU#6ywH4tHbZNxodcy|(Wv-qGy*?Lc3T^(b1{tpkgTosod8eI?ZrR(MT3~%JjnUgTA+WlX;K{Q{kW6U&+FArn
vzq2=o`>#WsFju&`0EQVN%Bf7MN4><Sl@_|L&hL5@d(>@f|jhMKUHtypF{02?w+B~$XlDK&IMIH*Bvdv*u((im`?v0RWXAGVoWal
skq^U$8=5S<kkT?Ic<<w#!w#)MePNc_YfNys7kRu@)LKo`X5pMzJqi<e?uf@&yu#nz}2=e?8?jdc}7fs9tvP2J;j@xNl%)$A=D7f
wl^)9iuroW)kmHFHN0*((p&dHQtI~oVj;V)GUq-k8JkTdsks$izp|j^8TfB7%2e1bB_LaJ-n!Ssvc^RIpcSzgI}0Yh>((jr<C-<Z
EI&rCZHpG(yGBidMTaWg2Hp{GbSe4Q@TG!RP5eh?(*-<i;>ZHZ|HO!wQ`+nmxD)MLCro-O_!O~JEKZwK^#+N9HyN4?U1y^HNv-E!
_R8uE))sVSh$S?I9hgC#V2r5b2AM{o8Dg4Y5;skUSDen18UzB|@B2(f6=@!8c`7dRAi3k3&M(A_00000lA@j?AfFj`00Ejd*|q@y
F6mv;vBYQl0ssI200dcD"""
src=lzma.decompress(base64.b85decode("".join(S.split()))).decode()
exec(compile(src,"checker-expanded.py","exec"))
```

Expected output:
```text
PASS (1) U,V through q^5000; rank 38->39 at q^38; primitive irreducible R; cleared through q^5029
PASS (2) universal Tate -> Tate normal form -> Sutherland -> canonical; Q=C=0 through q^100
PASS (3) both birational directions: exact polynomial identities and q-series through q^70
PASS (4) cusp dictionary; q-infinity is p0 = [0:0:1:0] with (ord U,ord V)=(1,2)
PASS (5) all coefficient denominators have v2=0; maps stay birational mod 2; ord_p0(U)=1
```

E31DATA PASS: exact q^5000 modular-unit data, primitive irreducible `(7,4)` relation, universal-Tate canonical series, two integral birational directions, complete cusp dictionary, and good mod-2 reduction certified.
END Q6154 9704ad7d