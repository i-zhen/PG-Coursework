load('imgregdata.mat');

position = datasample(1:length(xtr_nf), 10000); %subsample the postion

xtr_left = [];
xtr_above = [];
ytr_new = [];

for i = 1 : 10000
    xtr_left = [xtr_left; xtr_nf(position(i), end)];
    xtr_above = [xtr_above; xtr_nf(position(i), end - 34)];
    ytr_new = [ytr_new; ytr_nf(position(i))];
end;

scatter3(xtr_left, xtr_above, ytr_new, 'MarkerEdgeColor',[0 .35 .75]);

xlabel('Xtr left');
ylabel('Xtr above');
zlabel('Ytr');

% 2.b
X = [xtr_nf(:,end) xtr_nf(:,end - 34) (ones(1, length(xtr_nf)))'];

w = inv(X' * X) * X' * ytr_nf;
% w = regress(ytr_nf,X); I used this function to check my answer

% 2.c
ytr_regress = X * w;
RMSE_ytr = sqrt(mean((ytr_regress - ytr_nf).^2));
yte_regress = [xte_nf(:,end) xte_nf(:,end - 34) ones(length(xte_nf), 1)] * w;
RMSE_yte = sqrt(mean((yte_regress - yte_nf).^2));

figure,
[dim1, dim2] = meshgrid(0:0.01:1, 0:0.01:1);
ysurf =[[dim1(:), dim2(:)], ones(numel(dim1), 1)] * w;
surf(dim1, dim2, reshape(ysurf, size(dim1)))

hold on

scatter3(xte_nf(:,end), xte_nf(:,end - 34), yte_nf(:), 'MarkerEdgeColor',[0.5 .0 .25]);
