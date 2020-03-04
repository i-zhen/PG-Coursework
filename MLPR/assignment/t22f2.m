function [Lp, dLp_dw] = t22f2(eps, ww, xx, yy)
yy = (yy==1)*2 - 1;
%derivative of epsilon
sigmas = 1./(1 + exp(-yy.*(xx*ww))); % Nx1
Lp = sum(log((1-eps)*sigmas+(eps/2)));

if nargout > 1
    dLp_dw = sum((0.5-sigmas)./((1-eps)*sigmas+(eps/2)));
end