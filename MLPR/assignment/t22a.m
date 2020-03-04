load('text_data.mat');
b_tr = rand(101, 1) * 10;
x_te = [x_test ones(length(x_test), 1)];
x_tr = [x_train ones(length(x_train), 1)];
checkgrad('t22f1', b_tr, 1e-3, rand(1, 1),  x_tr, y_train);
checkgrad('t22f2', rand(1, 1), 1e-3, b_tr,  x_tr, y_train);