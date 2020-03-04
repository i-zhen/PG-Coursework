function [Lp, dLp_dw] = t22f1n(w, x, y)
y = (y==1)*2 - 1;
a = w(end);
ww = w(1: end - 1);
eps = 1./(1+exp(-a));
sigmas = 1./(1 + exp(-y.*(x*ww))); % Nx1
Lp = -sum(log((1-eps)*sigmas+(eps/2)));

a = -(((1-eps)*sigmas.*(1-sigmas)./((1-eps)*sigmas+eps/2).*y)' * x)';
b = -sum((0.5-sigmas)*eps*(1-eps)./((1-eps)*sigmas+(eps/2)));
dLp_dw = [a', b]';
