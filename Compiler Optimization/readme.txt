READ ME

IMPORTANCE: The average number which showed in report_result.txt is not the mean of runtimes, it is the mean of rate of speedup.

1.The folders of baseline and result are the results of tests.
raw_result is named raw_result.txt in them and there is also a report result.
(I also copied a raw result in the current path)
Each benchmark has its own result, you can find it in the folders if you want.

2.The flags which I used for this coursework are in op_input.txt and para_input.txt.
op_input.txt includes the flags which almost do not need set a parameter.
para_input.txt is the sample of the parameters.

3.The main program is main.py
Warning: If you want to run the program. You should set your own SMTP account at first or change the program to do not send the email.

IMPORTANCE: The average number which showed in report_result.txt is not the mean of runtimes, it is the mean of reciprocal of rate of speedup.(really important, mentioned twice)

4.Format of report_result.txt:

The format of report_result.txt in the folder result is:

First line: best reciprocal of rate of speedup over all benchmarks
(If it is less than 1, it means that we beat the baseline)

Second line: best flag of all programs

Third line: mean of reciprocal of rate of speedup

From fourth line on, we have all the individual set of flags for each benchmark

In the end of file is the final probability of selection of all single flags.
