function [Lp, dLp_dw] = t22f1(ww, eps, xx, yy)
yy = (yy==1)*2 - 1;
% derivative of w
sigmas = 1./(1 + exp(-yy.*(xx*ww))); % Nx1
Lp = sum(log((1-eps)*sigmas+(eps/2)));

if nargout > 1
    dLp_dw = (((1-eps)*sigmas.*(1-sigmas)./((1-eps)*sigmas+eps/2).*yy)' * xx)';
end