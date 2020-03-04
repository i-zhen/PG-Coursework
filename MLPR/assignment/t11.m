%load('imgregdata.mat');

xtr_1a = xtr / 63.0; % scaling the training data
ytr_1a = ytr / 63.0;

xte_1a = xte / 63.0; % scaling the test data
yte_1a = yte / 63.0;

std_tr = std(xtr_1a,0,2); % standard derivation

histogram(std_tr, 64); %(1.a)

err = 0 / 64.0;
targetPixel = mean(xtr_1a, 2); %(1.b)

flatPatch = find(std_tr <= err); 
nonflatPatch = find(std_tr > err);
nononeFlatPatch = [xtr_1a(nonflatPatch(10000), :) zeros(1, 18)]; % find a non-flat image patch locates in 2000
nononeFlatPatch = reshape(nononeFlatPatch, [35, 30])';

oneFlatPatch = [xtr_1a(flatPatch(50), :) zeros(1, 18)]; % find a non-flat image patch locates in 100
oneFlatPatch = reshape(oneFlatPatch, [35, 30])';

colormap gray;

subplot(1,2,1), imagesc(oneFlatPatch, [0,1]);
subplot(1,2,2), imagesc(nononeFlatPatch, [0,1]);