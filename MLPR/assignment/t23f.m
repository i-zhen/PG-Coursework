function logP = t23f(w, x, y)
y = (y==1)*2 - 1;
loglambda = w(end);
eps = w(end-1);
ww = w(1: end - 2);
sigmas = 1./(1 + exp(-y.*(x*ww))); % Nx1
Lp = sum(log((1-eps)*sigmas+(eps/2)));
lambda = exp(loglambda);
logP = Lp - lambda*(ww')*ww + length(w)/2*loglambda ;
