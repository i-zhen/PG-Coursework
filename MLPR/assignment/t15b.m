rng(2019, 'twister');
nhid = 10;
net = mlp(size(xtr_nf, 2), nhid, 1, 'linear');

options = zeros(1, 18);
options(1) = 1;
options(9) = 1;
options(14) = 200;

tic
[net, options] = netopt(net, options, xtr_nf(1: 5000, :), ytr_nf(1:5000,:),'scg');
toc

ypred_tr = mlpfwd(net, xtr_nf(1:5000,:));
rmse_NNsuball_tr = sqrt(mean(((ytr_nf(1:5000) - ypred_tr).^2)));

ypred = mlpfwd(net, xte_nf);
rmse_NNsuball_te = sqrt(mean(((yte_nf - ypred).^2)));