load('imgregdata.mat');
%code for creating RBF and making predictions
%nbf is the number of basis functions
%dim is the dimensionality of input space

nbf = [5,10,15,20,25,30];
format long; % set display precision
options = foptions;
options(1) = 1;
options(14) = 5;
TrainX = xtr_nf(:,[end end - 34]);
%TestX = xte_nf(:,[end end - 34]);

for j= 1:10
for i = 1:6
    dim = 2;
    net = rbf(dim, nbf(i), 1, 'gaussian');
    %10-fold cross validation
    rbff=@(XTRAIN,ytrain,XTEST)(rbffwd(rbftrain(net, options, XTRAIN, ytrain), XTEST));
    RMSE(i) = sqrt(crossval('mse',TrainX, ytr_nf, 'Predfun',rbff));
end

hold on;
plot(nbf, RMSE,'r','LineWidth',2,'Marker','o','MarkerSize',10);
end
