load('imgregdata.mat');
%code for creating RBF and making predictions
%nbf is the number of basis functions
%dim is the dimensionality of input space
net = rbf(2, 10, 1, 'gaussian');

options = foptions;
options(1) = 1;
options(14) = 5;

rbff= rbftrain(net, options, xtr_nf(:,[end end - 34]), ytr_nf);
ypred_tr = rbffwd(rbff, xtr_nf(:,[end end - 34]));
ypred_te = rbffwd(rbff, xte_nf(:,[end end - 34]));

RMSE_ytr = sqrt(mean((ypred_tr - ytr_nf).^2));
RMSE_yte = sqrt(mean((ypred_te - yte_nf).^2));