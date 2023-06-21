import time
import multiprocessing
# 執行你的程式


def go():
    import resource
    # 設置 CPU 時間限制為 10 秒
    resource.setrlimit(resource.RLIMIT_CPU, (1, 1))
    
    s0 = time.process_time()
    s = 0
    for i in range(60000000):
        s += i
    
    print('cpu time', time.process_time() - s0)
    # time.sleep(3)
    

def your_program():
    process = multiprocessing.Process(target=go)
    process.start()
    process.join()
    


# 執行你的程式
try:
    your_program()
    # go()
    print('finish')
except Exception:
    print("Program timed out")
