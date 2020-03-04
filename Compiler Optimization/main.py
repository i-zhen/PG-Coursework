#!/usr/bin/python
# Version 0.61
# @Author : Yi Zhen
# @UUN : s1563190
# For doing this coursework I have talked about with Xiaowei Liu and Yichi Zhang
# 0.3  : add method of generating flags
# 0.35 : send email to me
# 0.4  : add random method - mutation
# 0.5  : alpha edition - punishment
# 0.51 : configure the parameters
# 0.52 : fix bug
# 0.53 : add report function
# 0.6  : tune the parameter
# 0.8  : Coefficient of Variance
# 1.0  : submit

"""
How to use(*nix only):
* Run following command in your terminal:
  #screen
  #longjob -r28day -c `./main.py`
  #ctrl-a d
* For killing the process:
  use 'top' to check the pid and use 'kill pid' to kill it
"""

import base64
import os
import time
import smtplib
from email.mime.text import MIMEText
from email.mime.multipart import MIMEMultipart
import random
import math


class NumPy:
    """
    because there is no numpy in DICE
    """
    _baseline = {'401.bzip2': 3.59716551, '429.mcf': 2.32190442, '433.milc': 14.97559814,
                 '445.gobmk': 15.44666657, '456.hmmer': 2.31822162, '458.sjeng': 3.43194869,
                 '462.libquantum': 1.20006716, '464.h264ref': 10.55838513, '470.lbm': 2.46367242,
                 'h263dec': 0.12021108, 'h263enc': 1.97227190, 'mpeg2dec': 0.22722061,
                 'mpeg2enc': 8.06954505}
    _speedup = 13.0

    def __init__(self, data):
        self.__data = data
        self.__threshold = 0.2
        return

    def average(self):
        sum = 0.0
        for i in range(0, len(self.__data)):
            sum += self.__data[i]
        return sum / len(self.__data)

    def var(self):
        avg = self.average()
        sum = 0.0
        for i in range(0, len(self.__data)):
            sum += (avg - self.__data[i]) ** 2.0
        return sum / len(self.__data)

    def set_threshold(self, value):
        self.__threshold = value
        return

    def analysis_stable(self):
        if math.sqrt(self.var()) / self.average() <= self.__threshold:
            return True
        else:
            return False

    def speedup(self):
        val = []
        for i in self.__data:
            val.append(self.__data[i] / self._baseline[i])
        return reduce(lambda x, y: x + y, val) / self._speedup


class GccFlags:
    _flags = []
    current = []
    _current2 = []
    result = {'401.bzip2': [9999, '', []], '429.mcf': [9999, '', []], '433.milc': [9999, '', []],
              '445.gobmk': [9999, '', []], '456.hmmer': [9999, '', []], '458.sjeng': [9999, '', []],
              '462.libquantum': [9999, '', []], '464.h264ref': [9999, '', []], '470.lbm': [9999, '', []],
              'h263dec': [9999, '', []], 'h263enc': [9999, '', []], 'mpeg2dec': [9999, '', []],
              'mpeg2enc': [9999, '', []]}
    final_result = dict()
    _points = [25.0, 18.0, 15.0, 12.0, 10.0, 8.0, 6.0, 4.0, 2.0, 1.0]
    _count = 0
    _lower_bound = 0.5
    _upper_bound = 0.9

    def __init__(self, initflag, paraflag):
        self._flags = initflag
        self._para = paraflag
        self._pos = []
        self.baseflag = []
        for i in range(0, len(initflag) + len(paraflag)):
            self._pos.append(0.75)
        return

    def setcurrent(self, num, flag):
        self._count += 1
        self._current2.append([num, self.baseflag])
        self.current.append([num, flag])
        return

    def update(self, name, avg, alltimes, flag):
        if avg < self.result[name][0]:
            self.result[name][0] = avg
            self.result[name][1] = flag
            self.result[name][2] = alltimes
        # save the flags and runtime
        if name not in self.final_result:
            self.final_result[name] = []
        self.final_result[name].append([flag, alltimes])
        return

    def mutation(self, end, step):
        """
        If you are a fan of Grands Prix of Formula 1. You must know the rule of Scoring.
        1st place:  25
        2nd place:  18
        3rd place:  15
        4th place:  12
        5th place:  10
        6th place:  8
        7th place:  6
        8th place:  4
        9th place:  2
        10th place: 1
        :return:
        """
        decrate = len(self._flags) * 0.25 / 20.0
        point = dict()
        inc = 0
        total = 0

        out = dict()
        for i in range(end - step, end):
            out[self._current2[i][0]] = self._current2[i][1]

        for key in sorted(out.keys()):
            for k in out[key]:
                if k[1] != 'O'and k[1] != '-'\
                              and k[0] == '-':
                    if not (k in point):
                        point[k] = self._points[inc]
                    else:
                        point[k] += self._points[inc]
                    total += self._points[inc]
            inc += 1

        for i in range(0, len(self._flags)):
            if self._flags[i] in point:
                dec = point[self._flags[i]] / total * decrate * random.random()
                if self._pos[i] - dec >= self._lower_bound:
                    self._pos[i] -= dec
                else:
                    self._pos[i] = self._lower_bound

        return self._pos

    def punishment(self, compileflags):
        """
        If current set of flags make the compiling error, punish them. Increase the _pos
        :return:
        """
        incrate = len(self._flags) * 0.15 / 20.0
        for i in range(0, len(self._flags)):
            if self._flags[i] in compileflags:
                inc = 1.0 / len(compileflags) * incrate * random.random()
                if self._pos[i] + inc <= self._upper_bound:
                    self._pos[i] += inc
                else:
                    self._pos[i] = self._upper_bound
        return self._pos

    def parampos(self):
        return int(math.floor(random.random() * 3))

    def getparams(self):
        paraflag = []
        for i in range(0, len(self._para)):
            if self.getrandom(i + len(self._flags)):
                paraflag.append('--param ' + self._para[i][self.parampos()])
        return paraflag

    def getrandom(self, pos):
        return random.random() >= self._pos[pos]

    def getflags(self):
        step = 1
        while True:
            if self._count != 0 and self._count % step == 0:  # every 10 times update random seq once
                self.mutation(self._count, step)
            self.baseflag = ["-O3"]
            for i in range(0, len(self._flags)):
                if self.getrandom(i):
                    self.baseflag.append(self._flags[i])
            paraml = self.getparams()
            if len(paraml) > 0:
                self.baseflag.extend(paraml)
            yield " CFLAGS=\"%s\"" % ' '.join(self.baseflag)

    def baseflags(self):
        """
        kernel function, do compute the flags
        :return: the list of flags
        """
        baseflags = ["-O3", "-O2", "-O1", "-O0"]
        for b in baseflags:
            yield " CFLAGS=\"%s\"" % b


class CppRun:

    def __init__(self):
        # global variables
        self.__step_rate = 0.1
        self.__test_num_each = 10
        return

    def set_test_num(self, value):
        self.__test_num_each = value
        return

    def compiler(self, dir, flag):
        """
        change current path into src
        make it
        change the path to original dir
        :param dir: current directory
        :param flag: make the files with flag
        :param f: output target
        :return: nothing
        """
        os.chdir(os.getcwd() + "/" + dir + "/src")
        ret = os.system("make" + flag)
        os.chdir(os.path.pardir)  # ..
        os.chdir(os.path.pardir)  # ..
        return ret

    def analyzer(self, exectime, f):
        """
        :param exectime: a list of executing time of a single set of flags
        :param f: output file
        :return: average running time
        """
        np = NumPy(exectime)
        print >> f, ("Average running time: \t%.8fs\nVariance of time: \t%.8f" % (np.average(), np.var()))
        np.set_threshold(0.2)
        print >> f, ("Running stable? %s\n" % np.analysis_stable())
        return np.average(), exectime

    def executer(self, dir):
        """
        executing multiple times and judge that if it runs table or not
        :param dir: current directory
        :return: a list of executing time of a single set of flags
        """
        exectime = []
        ret = 0
        os.chdir(os.getcwd() + "/" + dir)
        for i in range(0, self.__test_num_each):
            # waiting for machine to get cooling for preventing unstable situation
            starttime = time.time()
            ret = os.system("./run.sh >> " + dir + "_sound.txt")
            endtime   = time.time()
            exectime.append(endtime - starttime)
        os.chdir(os.path.pardir)  # ..
        return exectime, ret

    def sendemail(self, case, info):
        """
        :param case: 0 for progress, 1 or 2 for error information, 3 for result files
        :param info: major information
        :return: nothing
        """
        if case == 0:
            msg = MIMEText("Finished percentage of %d%% of all. \n\n--From student.compute" % info)
        elif case == 1:
            msg = MIMEText("Compiling error on flags : %s \n\n--From student.compute" % info)
        elif case == 2:
            msg = MIMEText("Ruuning error %s \n\n--From student.compute" % info)
        elif case == 3:
            msg = MIMEMultipart()
            for i in info:
                att = MIMEText(open('./' + i, 'rb').read(), 'base64', 'utf-8')
                att["Content-Type"] = 'application/octet-stream'
                att["Content-Disposition"] = 'attachment; filename="%s"' % i
                msg.attach(att)

        if 0 <= case <= 3:
            msg['Subject'] = 'COPT progress/result'
            msg['From'] = "iamzhenyi@icloud.com"
            msg['To'] = "s1563190@sms.ed.ac.uk"

            passwd = base64.decodestring('')  # password here, should be encoded by base64 first
            mail = smtplib.SMTP('smtp.mail.me.com', 587)
            mail.ehlo()
            mail.starttls()
            mail.login("iamzhenyi@icloud.com", passwd)

            mail.sendmail("iamzhenyi@icloud.com", ["s1563190@sms.ed.ac.uk"], msg.as_string())
            mail.quit()
        return

    def report(self, flagobj):
        fout = open("report_result.txt", "w")
        out = dict()
        # single set of flags across all programs and average time
        for i in flagobj.current:
            out[i[0]] = i[1]
        sort = sorted(out.keys())
        print >> fout, sort[0], out[sort[0]]
        print >> fout, "Average: ", reduce(lambda x, y: x + y, out.keys()) / 200.0
        print >> fout
        # best found flags for individual program
        for key in flagobj.result:
            print >> fout, key, flagobj.result[key][0], flagobj.result[key][1]
        print >> fout
        for j in flagobj._pos:
            print >> fout, j,
        fout.close()
        # raw data report
        fout2 = open("raw_result.txt", "w")
        for i in flagobj.final_result:
            print >> fout2, i, ':'
            for j in range(0, len(flagobj.final_result[i])):
                print >> fout2, flagobj.final_result[i][j][0],
                for k in range(0, len(flagobj.final_result[i][j][1])):
                    print >> fout2, int(flagobj.final_result[i][j][1][k] * 100),
                print >> fout2
        fout2.close()
        return

    def main(self):
        """
        control everything
        :return: nothing
        paraf = open("para_input.txt", "r")
        paraflag = []
        for i in paraf.read().split('\n'):
            if len(i) > 0:
                paraflag.append(i)
        paraf.close()
        """
        initf = open("op_input.txt", "r")
        initflag = []
        for i in initf.read().split('\n'):
            if len(i) > 0:
                initflag.append(i)
        initf.close()

        paraf = open("para_input.txt", "r")
        paraflag = []
        temp = []
        pos = 0
        for i in paraf.read().split('\n'):
            if len(i) > 0:
                temp.append(i)
                pos += 1
            if pos % 5 == 0 and len(temp) > 0:
                paraflag.append(temp)
                temp = []
        paraf.close()

        currentpath = os.getcwd()
        getflag = GccFlags(initflag, paraflag)
        succ = 0
        comp = 0
        count = 0
        final_results = set()
        speed = dict()
        tentime = dict()

        for i in os.listdir(currentpath):
            if os.path.isdir(os.getcwd() + "/" + i + "/src"):
                f = open(i + "_result.txt", "w")
                f.close()
                final_results.add(i)
                speed[i] = 0
                tentime[i] = []
        """
        inc = 0
        incc =0
        for j in initflag:
            incc += 1.0
            count = 0
            jj = " CFLAGS=\" %s\"" % j
            for i in final_results:
                count += 1
                if self.compiler(i, jj) != 0:
                    self.sendemail(1, jj + " @ " + i + '$' + str(inc) + '/' + str(incc))
                    getflag.punishment(j)
                    break
            if count == 13:
                inc += 1.0
            if inc == 10.0:
                break
        self.sendemail(0, inc/incc)
        """

        for j in getflag.baseflags():
            inc = 0
            for i in final_results:
                comp += 1    # total test
                if self.compiler(i, j) != 0:
                    self.sendemail(1, j + " @@ " + i + '$' + str(count) + '/' + str(comp))
                    getflag.punishment(j)
                    break
                count += 1   # success test total
                inc += 1     # success test
            if inc == len(final_results):
                inc = 0
                for i in final_results:
                    extime, rret = self.executer(i)
                    if rret == 0:
                        f = open(i + "_result.txt", "a")
                        print >> f, (("#%d Current Flags: " + j) % (succ + 1))
                        avg, tenruntimes = self.analyzer(extime, f)
                        inc += 1
                        speed[i] = avg
                        tentime[i] = tenruntimes
                        f.close()
                    else:
                        self.sendemail(2, i)
                        break
            if inc == len(final_results):
                succ += 1
                getflag.setcurrent(NumPy(speed).speedup(), j)  # compute speedup
                for i in speed:
                    getflag.update(i, speed[i], tentime[i], j)
            if succ / 200.0 >= self.__step_rate:
                self.__step_rate += 0.1
                self.sendemail(0, succ / 2)
            if succ == 200:
                break

        # result
        self.report(getflag)
        final_results.add('report')
        final_results.add('raw')
        self.sendemail(3, map(lambda x: "%s_result.txt" % x, final_results))
        return

    def initoption(self):
        f = open("options.txt", 'r')
        flags = set()
        line = f.readline()
        while line:
            temp = line.lstrip(' ')
            temp = temp.strip(' ')
            temp = temp.strip('\n')
            temp = temp.strip(' ')
            temp = temp.split(' ')
            for j in temp:
                if len(j) > 2 and j[0] == '-' \
                              and j[1] == 'f' \
                              and j.find(')') < 0\
                              and j.find('O') < 0\
                              and j[1] != '-'\
                              and j.find('=') < 0\
                              and j.find('-fno'):
                    j = j.strip('.')
                    j = j.strip(',')
                    flags.add(j)
            line = f.readline()
        f.close()

        f = open("op.txt", "w")
        for i in flags:
            print >> f, i
        f.close()
        return

if __name__ == "__main__":
    testflags = CppRun()
    testflags.set_test_num(10)
    testflags.main()
    #testflags.initoption()
