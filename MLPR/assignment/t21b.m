function [Lp, dLp_dw] = t21b(ww, xx, yy)
yy = (yy==1)*2 - 1;

sigmas = 1./(1 + exp(-yy.*(xx*ww))); % Nx1
Lp = -sum(log(sigmas));

if nargout > 1
    dLp_dw = -(((1-sigmas).*yy)' * xx)';
end