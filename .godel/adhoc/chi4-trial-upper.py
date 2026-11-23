# Sage 10.9 Python. Fixed rational sine trials, rigorous ball integrals for the chi4 Weil form.
if not __debug__:
 raise RuntimeError("run without Python optimization")
from sage.all import QQ, ComplexBallField, RealBallField
C=ComplexBallField(128); R=RealBallField(128); pi=C.pi(); eps=QQ(1)/2**30

def ray(D,coef,primes):
 D=QQ(D); n=list(range(1,2*len(coef),2)); v=[QQ(u)/10**9 for u in coef]; norm=sum(x*x for x in v); c=[v[i]**2/norm for i in range(len(n))]; s=[c[i]/n[i] for i in range(len(n))];
 for i,m in enumerate(n):
  for j in range(i):
   k=n[j]; coef=2*v[i]*v[j]/norm; s[i]+=coef*(-QQ(1)/(m-k)+QQ(1)/(m+k)); s[j]+=coef*(QQ(1)/(m-k)+QQ(1)/(m+k))
 f=[pi*m/D for m in n]; sc=[C(x)/pi for x in s]; cs=list(map(C,c))
 def A(t):
  t=C(t); return sum(s0*(fj*t).sin() for fj,s0 in zip(f,sc))+(1-t/D)*sum(c0*(fj*t).cos() for fj,c0 in zip(f,cs))
 def g(t,analytic):return 2*(-3*t/2).exp()*(1-A(t))/(1-(-2*t).exp())
 # regularize [0,eps]: normalized 1-A(t) <= t^2 ||h'||² / 2; 2 exp(-3t/2)/(1-exp(-2t)) <=2/t there.
 en=sum(c0*fj**2 for c0,fj in zip(cs,f)); small=(C(eps**2)*en/2).abs();
 arch=C(QQ(3)/4).psi()+(4/pi).log()+C.integral(g,eps,D,abs_tol=2**-65,rel_tol=2**-65,depth_limit=90)
 # integral of 2e^(-3t/2)/(1-e^(-2t)) on [D,infty]; remainder after j=15 <= geometric bound
 for j in range(16):
  a=QQ(3)/2+2*j;arch+=2*C(-a*D).exp()/a
 a=QQ(3)/2+32; tail=2*C(-a*D).exp()/a/(1-C(-2*D).exp());
 z=arch
 for p,base,chi in primes:z-=2*chi*C(base).log()/C(p).sqrt()*A(C(p).log())
 rad=small+tail.abs(); result=z.real().add_error(rad); print('D=',D,'normalized Rayleigh quotient=',result,flush=True);return result
atoms=[(3,3,-1),(5,5,1),(7,7,-1)];a=ray(2,[1000000000,-186110045,-48485074,-5218948,-2540012,-503751,-622741,-233042],atoms); assert a>0 and a<QQ(8184)/10**10
b=ray(QQ(9)/4,[1000000000,-278522309,-40499780,4956501,1026591,650431,31674,58855],atoms+[(9,3,1)]);assert b>0 and b<QQ(3797)/10**12

c=ray(QQ(11)/5,[1000000000,-260640723,-43488119,2448857,332316,425612,-61877,7756,-38417,-42093,-24085,-11499,-9964,-9872,-3283,-11393],atoms+[(9,3,1)]);assert c>0 and c<QQ(58)/10**10
