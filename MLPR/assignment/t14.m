X = [xtr_nf (ones(1, length(xtr_nf)))'];

w = inv(X' * X) * X' * ytr_nf;
%w = regress(ytr_nf,X); %I used this function to check my answer

ytr_regress = X * w;
RMSE_ytr = sqrt(mean((ytr_regress - ytr_nf).^2));
yte_regress = [xte_nf ones(length(xte_nf), 1)] * w;
RMSE_yte = sqrt(mean((yte_regress - yte_nf).^2));