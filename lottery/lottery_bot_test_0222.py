#!/usr/bin/env python
# coding: utf-8


import os
import re
import time
import datetime
import requests
import httplib2
import itertools
import elementpath
import numpy as np
import pandas as pd
from lxml import etree
from datetime import date
from bs4 import BeautifulSoup
from apiclient import discovery
from flask import Flask, request, abort
from linebot import LineBotApi, WebhookHandler
from oauth2client.client import GoogleCredentials
from linebot.exceptions import InvalidSignatureError
from oauth2client.service_account import ServiceAccountCredentials
from linebot.models import MessageEvent, TextMessage, TextSendMessage, ImageSendMessage, StickerSendMessage, LocationSendMessage, QuickReply, QuickReplyButton, MessageAction
app = Flask(__name__)


line_bot_api = LineBotApi('')
handler = WebhookHandler('')    



###功能2 功能3 所需函式
rules_sub = []
class Rule():
    def __init__(self, antecedent, concequent, confidence, support):
        self.antecedent = antecedent
        self.concequent = concequent
        self.confidence = confidence
        self.support = support


class Apriori():
    def __init__(self, min_sup=0.04, min_conf=0.04):
        self.min_sup = min_sup
        self.min_conf = min_conf
        self.freq_itemsets = None       # List of freqeuent itemsets
        self.transactions = None       # List of transactions
        global rules_sub
        rules_sub = []       
    def _calculate_support(self, itemset):
        count = 0
        for transaction in self.transactions:
            if self._transaction_contains_items(transaction, itemset):
                count += 1
        support = count / len(self.transactions)
        return support


    def _get_frequent_itemsets(self, candidates):
        frequent = []
        # Find frequent items
        for itemset in candidates:
            support = self._calculate_support(itemset)
            if support >= self.min_sup:
                frequent.append(itemset)
        return frequent


    def _has_infrequent_itemsets(self, candidate):
        k = len(candidate)
        # Find all combinations of size k-1 in candidate
        # E.g [1,2,3] => [[1,2],[1,3],[2,3]]
        subsets = list(itertools.combinations(candidate, k - 1))
        for t in subsets:
        # t - is tuple. If size == 1 get the element
            subset = list(t) if len(t) > 1 else t[0]
            if not subset in self.freq_itemsets[-1]:
                return True
        return False


    def _generate_candidates(self, freq_itemset):
        candidates = []
        for itemset1 in freq_itemset:
            for itemset2 in freq_itemset:
                # Valid if every element but the last are the same
                # and the last element in itemset1 is smaller than the last
                # in itemset2
                valid = False
                single_item = isinstance(itemset1, int) 
                if single_item and itemset1 < itemset2:
                    valid = True
                elif not single_item and np.array_equal(itemset1[:-1], itemset2[:-1]) and itemset1[-1] < itemset2[-1]:
                    valid = True

                if valid:
                    # JOIN: Add the last element in itemset2 to itemset1 to
                    # create a new candidate
                    if single_item:
                        candidate = [itemset1, itemset2]
                    else:
                        candidate = itemset1 + [itemset2[-1]]
                    # PRUNE: Check if any subset of candidate have been determined
                    # to be infrequent
                    infrequent = self._has_infrequent_itemsets(candidate)
                    if not infrequent:
                        candidates.append(candidate)
        return candidates


    def _transaction_contains_items(self, transaction, items):
        # If items is in fact only one item
        if isinstance(items, int):
            return items in transaction
        # Iterate through list of items and make sure that
        # all items are in the transaction
        for item in items:
            if not item in transaction:
                return False
        return True

    def find_frequent_itemsets(self, transactions):
        self.transactions = transactions
        # Get all unique items in the transactions
        unique_items = set(item for transaction in self.transactions for item in transaction)
        # Get the frequent items
        self.freq_itemsets = [self._get_frequent_itemsets(unique_items)]
        while(True):
            # Generate new candidates from last added frequent itemsets
            candidates = self._generate_candidates(self.freq_itemsets[-1])
            # Get the frequent itemsets among those candidates
            frequent_itemsets = self._get_frequent_itemsets(candidates)

            # If there are no frequent itemsets we're done
            if not frequent_itemsets:
                break

            # Add them to the total list of frequent itemsets and start over
            self.freq_itemsets.append(frequent_itemsets)

        # Flatten the array and return every frequent itemset
        return self.freq_itemsets

    def _frequent_itemset_contain_user(self, frequent_itemset, user):
        # If user is in fact only one number
        if isinstance(user, str):
            return user in frequent_itemset
        # Iterate through list of user and make sure that
        # all no are in the frequent_itemset
        for no in user:
            if not no in frequent_itemset:
                return False
        return True
    
    def generate_rules(self, user, transactions):
        self.transactions = transactions
        frequent_itemsets = self.find_frequent_itemsets(transactions)
        # Only consider itemsets of size >= 2 items
        frequent_itemsets = frequent_itemsets[1:]
        rules = []
        K = len(user)
        ## 檢查user輸入的號碼是否比長度最長的frequent_itemset短
        if K <= (len(frequent_itemsets)+1):
            index = -1
            while True:
                ## 從長度最長的frequent_itemsets開始觀察user是否包含在裡面 然後計算信賴度 並將符合的frequent_itemsets提取出來
                for frequent_itemset in frequent_itemsets[index]:
                    if self._frequent_itemset_contain_user(frequent_itemset, user):
                        support = self._calculate_support(frequent_itemset)
                        antecedent_support = self._calculate_support(user)
                        confidence = float("{0:.2f}".format(support / antecedent_support))
                        if confidence >= self.min_conf:
                            # The concequent is the frequent_itemset except for user
                            concequent = [itemset for itemset in frequent_itemset if not itemset in user]
                            rule = Rule(
                                antecedent=user,
                                concequent=concequent,
                                confidence=confidence,
                                support=support)
                            rules.append(rule)
                index -= 1
                ## 如果到了長度跟user一樣長 將user切成subsets
                if ((len(frequent_itemsets)+1)-(abs(index)-1)) <= K:
                    self._rules_from_itemset(user, transactions)
                    break
        else:
            self._rules_from_itemset(user, transactions)
        return rules
    
    def _rules_from_itemset(self, initial_frequent_itemsets,transactions):
        global rules_sub
        initial_frequent_itemsets = initial_frequent_itemsets
        frequent_itemsets = self.find_frequent_itemsets(transactions)
        # Only consider itemsets of size >= 2 items
        frequent_itemsets = frequent_itemsets[1:]
        k = len(initial_frequent_itemsets)
        # Flatten all possible subsets
        subsets = []
        for i in range(1,k):
            subsets += list(itertools.combinations(initial_frequent_itemsets, k - i))
        for antecedent in subsets:
            L = len(antecedent)
            antecedent = list(antecedent)
            index = -1
            while True:
                try :
                ## 從長度最長的frequent_itemsets開始觀察user是否包含在裡面 然後計算信賴度 並將符合的frequent_itemsets提取出來
                    for frequent_itemset in frequent_itemsets[index]:
                        if self._frequent_itemset_contain_user(frequent_itemset,antecedent):
                            support = self._calculate_support(frequent_itemset)
                            antecedent_support = self._calculate_support(antecedent)
                            confidence = float("{0:.2f}".format(support / antecedent_support))
                            if confidence >= self.min_conf:
                            # The concequent is the frequent_itemset except for user
                                concequent = [itemset for itemset in frequent_itemset if not itemset in antecedent]
                                rule = Rule(
                                    antecedent=antecedent,
                                    concequent=concequent,
                                    confidence=confidence,
                                    support=support)
                                rules_sub.append(rule)
                    index -= 1
                    if ((len(frequent_itemsets)+1)-(abs(index)-1)) <= L:
                        break
                except:
                    break
    def get_lucky_numbers(self,user,transactions):
        transactions = transactions
        user = user
        # 叫出 rules, rules_sub
        rules = self.generate_rules(user, transactions)
        global rules_sub
        rules_sub = rules_sub
        #整理rules
        antecedent_len = []
        antecedent = []
        concequent = []
        confidence = []
        support = []
        for i in rules:
            antecedent_len.append(len(i.antecedent))
            antecedent.append(i.antecedent)
            concequent.append(i.concequent)
            confidence.append(i.confidence)
            support.append(i.support)
        rules_table = pd.DataFrame({'antecedent_len':antecedent_len,'antecedent':antecedent,'concequent':concequent,'confidence':confidence,'support':support})
        #整理rules_sub
        antecedent_len = []
        antecedent = []
        concequent = []
        confidence = []
        support = []
        for i in rules_sub:
            antecedent_len.append(len(i.antecedent))
            antecedent.append(i.antecedent)
            concequent.append(i.concequent)
            confidence.append(i.confidence)
            support.append(i.support)
        rules_sub_table = pd.DataFrame({'antecedent_len':antecedent_len,'antecedent':antecedent,'concequent':concequent,'confidence':confidence,'support':support})
        #合併table
        rules_table = pd.concat([rules_table,rules_sub_table],axis=0)
        rules_table = rules_table.sort_values(['antecedent_len','confidence'],ascending=[False,False])
        rules_table.reset_index(inplace=True)
        lucky_nums = user
        def check(candidates,lucky_nums):
            for item in candidates:
                if item in lucky_nums:
                    return False
            return True
        for j,i in enumerate(rules_table['concequent']):
            if len(lucky_nums) == 6:
                break
            elif (len(lucky_nums)+len(i)) <= 6:
                if check(i,lucky_nums):
                    lucky_nums += i
            else :
                continue
        if len(lucky_nums) == 6:
            return lucky_nums
        else :
            return "抱歉找不到"
    def get_one_lucky_number(self,user,transactions):
        transactions = transactions
        user = user
        # 叫出 rules, rules_sub
        rules = self.generate_rules(user, transactions)
        global rules_sub
        rules_sub = rules_sub
        #整理rules
        concequent_len = []
        antecedent = []
        concequent = []
        confidence = []
        support = []
        for i in rules:
            concequent_len.append(len(i.concequent))
            antecedent.append(i.antecedent)
            concequent.append(i.concequent)
            confidence.append(i.confidence)
            support.append(i.support)
        rules_table = pd.DataFrame({'concequent_len':concequent_len,'antecedent':antecedent,'concequent':concequent,'confidence':confidence,'support':support})
        #整理rules_sub
        concequent_len = []
        antecedent = []
        concequent = []
        confidence = []
        support = []
        for i in rules_sub:
            concequent_len.append(len(i.concequent))
            antecedent.append(i.antecedent)
            concequent.append(i.concequent)
            confidence.append(i.confidence)
            support.append(i.support)
        rules_sub_table = pd.DataFrame({'concequent_len':concequent_len,'antecedent':antecedent,'concequent':concequent,'confidence':confidence,'support':support})
        #合併table
        rules_table = pd.concat([rules_table,rules_sub_table],axis=0)
        #排序
        rules_table.drop(rules_table[rules_table['concequent_len'] == 0].index,inplace=True)
        rules_table = rules_table.sort_values(['concequent_len','confidence'],ascending=[True,False])
        rules_table.reset_index(inplace=True)
        lucky_nums = user
        try:
            if len(rules_table.index) == 0:
                return "抱歉找不到"
            else:
                if rules_table['concequent_len'][0] == 1:
                    lucky_nums += rules_table['concequent'][0]
                    return list(itertools.combinations(lucky_nums, 6))
        except:
            return "抱歉找不到"
    def get_rules_table(self,user,transactions):
        transactions = transactions
        user = user
        # 叫出 rules, rules_sub
        rules = self.generate_rules(user, transactions)
        global rules_sub
        rules_sub = rules_sub
        #整理rules
        concequent_len = []
        antecedent = []
        concequent = []
        confidence = []
        support = []
        for i in rules:
            concequent_len.append(len(i.concequent))
            antecedent.append(i.antecedent)
            concequent.append(i.concequent)
            confidence.append(i.confidence)
            support.append(i.support)
        rules_table = pd.DataFrame({'concequent_len':concequent_len,'antecedent':antecedent,'concequent':concequent,'confidence':confidence,'support':support})
        #整理rules_sub
        concequent_len = []
        antecedent = []
        concequent = []
        confidence = []
        support = []
        for i in rules_sub:
            concequent_len.append(len(i.concequent))
            antecedent.append(i.antecedent)
            concequent.append(i.concequent)
            confidence.append(i.confidence)
            support.append(i.support)
        rules_sub_table = pd.DataFrame({'concequent_len':concequent_len,'antecedent':antecedent,'concequent':concequent,'confidence':confidence,'support':support})
        #合併table
        rules_table = pd.concat([rules_table,rules_sub_table],axis=0)
        rules_table = rules_table.sort_values(['concequent_len','confidence'],ascending=[True,False])
        rules_table.reset_index(inplace=True)
        return rules_table
##自選機率
def user_prob(user,data):
    #算頻率
    count = dict()
    for i in data:
        for j in i:
            if count.get(j,'F') != 'F':
                count[j] += 1
            else:
                count[j] = 1
    return [round((count.get(i)/len(data)),3) for i in user]
##全部快選 
def lazy_option(data):
    #算頻率
    count = dict()
    for i in data:
        for j in i:
            if count.get(j,'F') != 'F':
                count[j] += 1
            else:
                count[j] = 1
    #照大小排序並返回機率前6大的balls
    selected_balls = [sorted(count.items(),key=lambda x:x[1])[i][0] for i in range(len(count.items())-6,len(count.items()))]
    selected_balls_probability = [round((count.get(i)/len(data)),3) for i in selected_balls]
    return (selected_balls,selected_balls_probability)
                
##檢查input是不是全部都是整數與加號 順便把數字都轉成float 然後刪除重複值排序
def check_para(text):
    pattern = re.compile(r"[0-9]+|\@")
    matches = pattern.findall(text)
    if matches == [] :
        return False
    else:
        for i in matches:
            try:
                float(i)
            except:
                if i != '@':
                    return False
        int_num = []
        plus_num = []
        for i in matches:
            try:
                float(i)%1
                if float(i)%1 == 0.0:
                    int_num.append(float(i))
                else:
                    return False
            except :
                plus_num.append(i)
        return sorted(list(set(int_num))) + plus_num
##檢查是不是+號:
def check_plus(text):
    if text == '@':
        return True
    else:
        return False
##檢查是不是1-49的正整數:
def check_ball(text):
    try: 
        if text>=1 and text<=49:
            if text%1 == 0.0:
                return True
            else:
                return False
        else:
            return False
    except:
        return False
##檢查號碼有沒有太多
def check_toomuch(text):
    plus_check = []
    balls_check = []
    for i in text:
        plus_check.append(check_plus(i))
    for i in text:
        balls_check.append(check_ball(i))
    if sum(plus_check)>1 or sum(balls_check)>6:
        return True
    else:
        return False

##取得與更新資料
url ='https://www.taiwanlottery.com.tw/Lotto/Lotto649/history.aspx'
#連結googledrive for .json;若在本機端推送heroku,則#註記下列兩行,不用跑以免錯誤!!
#from google.colab import auth
#auth.authenticate_user()
def get_data():
    #API及目標GoogleSheet設定
    scopes = ["https://spreadsheets.google.com/feeds","https://www.googleapis.com/auth/drive", "https://www.googleapis.com/auth/drive.file", "https://www.googleapis.com/auth/spreadsheets"]

    credentials = ServiceAccountCredentials.from_json_keyfile_name(
          "credentials.json", scopes) #本機端導入VSCODE,並把左側"___"內容改成檔名:"credentials.json"
    spreadsheet_id = '1FWvEPppM2UrD8Id4r9txyK8KRmsNgPz3WDGZvcDrSc4'
    service = discovery.build('sheets', 'v4', credentials=credentials)
    range_name = "database" #目標Sheet的名稱

    #讀取database內容,只取值
    value_render_option = 'FORMATTED_VALUE'
    database_request = service.spreadsheets().values().get(spreadsheetId=spreadsheet_id, range=range_name, valueRenderOption=value_render_option)
    database_response = database_request.execute()
    database_data = database_response.get('values')

    #將取值後結果轉DataFrame
    database_df = pd.DataFrame(database_data[1:], columns=database_data[0])
    database_df

    #爬新資料-抓取資料-期別、日期、開獎號碼

    #自訂標頭
    my_headers = {'user-agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/88.0.4324.146 Safari/537.36'}

    #將自訂標投加入post請求中
    r = requests.post(url,headers = my_headers)
    # print(r.text)
    res = r.content.decode()
    html = etree.HTML(res)

    #找到期別(draw_term)、開獎日(draw_date),使用etree.HTML()載入html,並使用xpath選擇器來取得想要的資料
    draw_term_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_L649_DrawTerm_0")]/text()')

    #開獎日(draw_date)
    draw_date_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_L649_DDate_0")]/text()')

    #開獎號碼(draw_number)
    draw_no1_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_SNo1_0")]/text()')
    draw_no2_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_SNo2_0")]/text()')
    draw_no3_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_SNo3_0")]/text()')
    draw_no4_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_SNo4_0")]/text()')
    draw_no5_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_SNo5_0")]/text()')
    draw_no6_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_SNo6_0")]/text()')
    draw_no7_new = html.xpath('//*[contains(@id,"Lotto649Control_history_dlQuery_No7_0")]/text()') 

    dailynew_df = pd.DataFrame({'draw_term':draw_term_new,
        'draw_date':draw_date_new,
        'no1':draw_no1_new,
        'no2':draw_no2_new,
        'no3':draw_no3_new,
        'no4':draw_no4_new,
        'no5':draw_no5_new,
        'no6':draw_no6_new,
        'no7':draw_no7_new                 
        }) #用Dict解

    lastest_row = len(database_df['draw_term'])-1 #第一個row從0開始,所以要-1

    #比對資料,利用database最後一筆資料去做判斷
    if (dailynew_df.values != database_df.iloc[lastest_row,].values).all(): #!=不相等 
        #用append把新資料加回資料庫
        values = dailynew_df.to_numpy().tolist() #先把DataFrame轉回list
        value_input_option = 'USER_ENTERED' #How the input data should be interpreted. 
        insert_data_option = 'INSERT_ROWS' #How the input data should be inserted. 
        value_range_body = {'values': values}
        request = service.spreadsheets().values().append(spreadsheetId=spreadsheet_id, 
            range=range_name, 
            valueInputOption=value_input_option, 
            insertDataOption=insert_data_option, 
            body=value_range_body
            )
        response = request.execute()
    
        #將取值後的最新資料庫導入DataFrame
        database_request = service.spreadsheets().values().get(spreadsheetId=spreadsheet_id, range=range_name, valueRenderOption=value_render_option)
        database_response = database_request.execute()
        database_data = database_response.get('values')
        database_df = pd.DataFrame(database_data[1:], columns=database_data[0])
        # print('change')
        #整理成可以給後續函數吃的資料
        result = []
        for i in range(len(database_df.index)):
            result.append(sorted(database_df.iloc[i,2:9]))
        result2 = []
        for j in range(len(result)):
            result2.append([int(x) for x in result[j]])
        return  result2
    
    else:
        #如果新資料與舊資料相同,直接return舊有資料庫
        # print('no change')
        #整理成可以給後續函數吃的資料
        result = []
        for i in range(len(database_df.index)):
            result.append(sorted(database_df.iloc[i,2:9]))
        result2 = []
        for j in range(len(result)):
            result2.append([int(x) for x in result[j]])
        return  result2


###玩法介紹
play_method = """
台灣彩券中獎王使用說明以及免責聲明書。\n\n
【手動選號】:\n
您可以手動輸入6個數字。(1~49)\n\n
【電腦選號】:\n
功能1【0】全部電腦選號\n
功能2【請輸入6碼以內的數字(1~49)】不足6碼其餘由系統計算提供。\n
功能3【請輸入隨機6碼@】由系統選一碼湊成7碼來做7組排列組合。\n\n
【財神D家】:\n
查詢選擇的地區及縣市搜尋歷屆大樂透中過頭獎的店家。\n\n
【星座運勢】:\n
由國師唐立淇每日星座運勢資訊網提供您今日的運勢天氣意象圖。\n\n
【連結官網】:\n
更多資訊與玩法請上台灣彩券官網查詢。
"""

###功能4所需函式
region_dict = ['基隆市','台北市','新北市','桃園市','新竹市','新竹縣','苗栗縣','台中市','彰化縣','南投縣','雲林縣','嘉義市','嘉義縣','台南市','高雄市','屏東縣','台東縣','花蓮縣','宜蘭縣','澎湖縣','金門縣','連江縣']
def get_address(text):
    #lottory report csv
    lottory_csv = 'http://www.taiwanlottery.com.tw/lotto/reportdownload/Jackpot_stores.csv'
    lottery_raw_data = pd.read_csv(lottory_csv,encoding='cp950',index_col=0)
    # filter catergory of 大樂透
    filtered_lottory = lottery_raw_data.loc['大樂透']
    sorted_by_address = filtered_lottory.sort_values(by=['售出頭獎商店地址'],ascending=False)
    sorted_by_address['縣市'] = sorted_by_address.apply(lambda row: row['售出頭獎商店地址'][:3], axis=1)
    find_result = sorted_by_address.loc[sorted_by_address['縣市'] == text]
    ##如果只有表頭的空Dataframe
    return find_result


###功能五所需函式
star_dict = {'牡羊座':'Aries','金牛座':'Taurus','雙子座':'Gemini','巨蟹座':'Cancer','獅子座':'Leo','處女座':'Virgo','天秤座':'Libra','天蠍座':'Scorpio','射手座':'Sagittarius','摩羯座':'Capricorn','水瓶座':'Aquarius','雙魚座':'Pisces'}
def get_stars(text):
    star = star_dict.get(text)
    url = f'https://www.daily-zodiac.com/mobile/zodiac/{star}'
    r = requests.get(url)
    sp = BeautifulSoup(r.text, 'lxml')
    datas = sp.find('div', class_='middle')
    title = datas.find('div', class_='name').text[1:4]
    weather = datas.find('div', class_='text').text[27:31]
    weather = weather.rstrip()
    return title + ': ' + weather

        
@app.route("/callback", methods=['POST'])
def callback():
    signature = request.headers['X-Line-Signature']
    body = request.get_data(as_text=True)
    try:
        handler.handle(body,signature)
    except InvalidSignatureError:
        abort(400)
    return 'OK'

@handler.add(MessageEvent, message=TextMessage)
def handle_message(event):
    user_id = event.source.user_id
    mtext = event.message.text
    if mtext == '@手動選號':
        try:
            message = TextSendMessage(
              text = '請輸入您喜歡的6碼自選號碼\n【輸入範例】: \n1 2 3 4 5 6'
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!')) 
    elif mtext == '@電腦選號':
        try:
            message = TextSendMessage(
              text = '【玩法1】:\n請輸入您喜歡的大樂透號碼，必須介於1~49的整數，最少輸入1碼，至多5碼，由系統選擇其餘的號碼湊成6碼\n\n輸入範例: 1 6 8\n\n【玩法2】:\n請輸入您喜歡的大樂透號碼，必須介於1~49的整數，輸入6碼，並加上@號，由系統再選擇1碼回傳套餐組合\n\n輸入範例: 1 6 8 23 45 49 @\n \n【玩法3】:\n輸入0,由系統選擇6碼'
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!')) 
    elif mtext == '@使用說明':
        try:
            message = [
                TextSendMessage(
                    text = play_method
                ),
                ImageSendMessage(
                    original_content_url = 'https://i.imgur.com/PCT8jSL.jpg',
                    preview_image_url = 'https://i.imgur.com/PCT8jSL.jpg'
                )
            
            ]
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext == '@星座運勢':
        try:
            d = str(datetime.date.today())
            text = d + '\n'
            for i in list(star_dict.keys()):
                text += get_stars(i)
                text += '\n'
            message = TextSendMessage(
              text = text 
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='獲取星座運勢發生錯誤!'))
    elif mtext =='@財神D家':
        try:
            message = TextSendMessage(
                text='請選擇所在區域',
                quick_reply=QuickReply(
                    items=[
                        QuickReplyButton(
                            action=MessageAction(label="北部", text="北區財神爺")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="中部", text="中區財神爺")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="南部", text="南區財神爺")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="東部", text="東區財神爺")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="離島", text="離島財神爺")
                        )                        
                        ]
                )
            )
            line_bot_api.reply_message(event.reply_token, message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    ##全部快選:
    elif mtext == '0':
        try:
            _blank = Apriori()
            data = get_data()
            if lazy_option(data) == "抱歉找不到":
                message = TextSendMessage(
                    text =  '全部快選發生錯誤!'
                )
            else:
                message = TextSendMessage(
                    text =  f'機器人接收使用者輸入: {mtext}\n平均每個號碼出現機率為 0.14\n全部快選: {lazy_option(data)[0]}\n全部快選各號碼機率: {lazy_option(data)[1]}' 
                )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='全部快選發生錯誤!'))
    elif mtext == '北區財神爺':
        try:
            message = TextSendMessage(
                text='選擇北部欲查詢縣市',
                quick_reply=QuickReply(
                    items=[
                        QuickReplyButton(
                            action=MessageAction(label="基隆市", text="基隆市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="台北市", text="台北市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="新北市", text="新北市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="桃園市", text="桃園市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="新竹市", text="新竹市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="新竹縣", text="新竹縣")
                        )
                        ]
                )
            )
            line_bot_api.reply_message(event.reply_token, message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext =='中區財神爺':
        try:
            message = TextSendMessage(
                text='選擇中部欲查詢縣市',
                quick_reply=QuickReply(
                    items=[
                        QuickReplyButton(
                            action=MessageAction(label="苗栗縣", text="苗栗縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="台中市", text="台中市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="彰化縣", text="彰化縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="南投縣", text="南投縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="雲林縣", text="雲林縣")
                        ),                      
                        ]
                )
            )
            line_bot_api.reply_message(event.reply_token, message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext == '南區財神爺':
        try:
            message = TextSendMessage(
                text='選擇南部欲查詢縣市',
                quick_reply=QuickReply(
                    items=[
                        QuickReplyButton(
                            action=MessageAction(label="雲林縣", text="雲林縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="嘉義市", text="嘉義市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="嘉義縣", text="嘉義縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="台南市", text="台南市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="高雄市", text="高雄市")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="屏東縣", text="屏東縣")
                        )                   
                        ]
                )
            )
            line_bot_api.reply_message(event.reply_token, message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext == '東區財神爺':
        try:
            message = TextSendMessage(
                text='選擇東部欲查詢縣市',
                quick_reply=QuickReply(
                    items=[
                        QuickReplyButton(
                            action=MessageAction(label="台東縣", text="台東縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="花蓮縣", text="花蓮縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="宜蘭縣", text="宜蘭縣")
                        )                 
                        ]
                )
            )
            line_bot_api.reply_message(event.reply_token, message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext == '離島財神爺':
        try:
            message = TextSendMessage(
                text='選擇離島欲查詢縣市',
                quick_reply=QuickReply(
                    items=[
                        QuickReplyButton(
                            action=MessageAction(label="澎湖縣", text="澎湖縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="金門縣", text="金門縣")
                        ),
                        QuickReplyButton(
                            action=MessageAction(label="連江縣", text="連江縣")
                        )                 
                        ]
                )
            )
            line_bot_api.reply_message(event.reply_token, message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext in list(star_dict.keys()):
        try:
            d = str(datetime.date.today())
            message = TextSendMessage(
                text = d + '\n' + get_stars(mtext)
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='獲取星座資料發生錯誤!'))   
    elif mtext in region_dict:    
        try:
            result = get_address(mtext)
            if result.empty:
                message1 = TextSendMessage(text = '很抱歉，您挑選的區域查無頭獎店家。')
                line_bot_api.reply_message(event.reply_token,message1)
            else:
                message = TextSendMessage(text = f'所有中獎店家資訊:\n'+str(result.to_records(index=False)))
                line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='獲取頭獎店家資訊發生錯誤!')) 
    else :
        if check_para(mtext):
            para = check_para(mtext)
            ##自選機率:
            if len(para) == 6 and [check_ball(para[i]) for i in range(len(para))] == [True]*len(para):
                try:
                    _blank = Apriori()
                    data = get_data()[:100]
                    user = [int(i) for i in para]
                    message = TextSendMessage(
                        text =  f'機器人接收使用者輸入: {user}\n平均每個號碼出現機率為 0.14\n自選各號碼歷史出現機率: {user_prob(user,data)}' 
                    )
                    line_bot_api.reply_message(event.reply_token,message)
                except:
                    line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))    
            ##部分快選
            elif len(para) > 0 and len(para) < 6 and [check_ball(para[i]) for i in range(len(para))] == [True]*len(para):
                try:                    
                    message1 = TextSendMessage(
                        text =  '請稍候，計算中'
                    )
                    line_bot_api.reply_message(event.reply_token,message1)
                    data = get_data()[:50]
                    test = Apriori()
                    user_balls = [int(i) for i in para]
                    if  test.get_lucky_numbers(user_balls,data) != "抱歉找不到":
                        message2 = TextSendMessage(
                            text =  f'機器人接收使用者輸入: {[int(i) for i in para]}\n部分快選:{str(test.get_lucky_numbers(user_balls,data))}'
                        )
                        line_bot_api.push_message(user_id,message2)
                    else:
                        message2 = TextSendMessage(
                            text =  '請更換一組號碼' 
                        )                        
                        line_bot_api.reply_message(event.reply_token,message2)
                except:
                    line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))         
            ##電腦組合:
            elif len(para) == 7 and check_plus(para[6]) == True and [check_ball(para[i]) for i in range(6)] == [True]*6: 
                try:
                    message1 = TextSendMessage(text ='請稍候，計算中')
                    line_bot_api.reply_message(event.reply_token,message1)
                    data = get_data()[:50]
                    user_balls = [int(i) for i in para[0:6]]
                    test = Apriori()
                    result = test.get_one_lucky_number(user_balls,data)
                    if test.get_one_lucky_number(user_balls,data) != "抱歉找不到":
                        message2 = TextSendMessage(text =  f'機器人接收使用者輸入: {[int(i) for i in para[0:6]]}\n電腦組合:\n{result}')
                        line_bot_api.push_message(user_id, message2)
                    else:
                        message2 = TextSendMessage(text =  '請更換一組號碼')
                        line_bot_api.reply_message(event.reply_token,message2)
                except:
                    line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
            else:
                ##輸入太多號碼
                if check_toomuch(para):
                    try:
                        message = TextSendMessage(
                        text = '您輸入太多號碼了'
                        )
                        line_bot_api.reply_message(event.reply_token,message)
                    except:
                        line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!')) 
                ##其他        
                else:
                    try:
                        message = TextSendMessage(
                        text = '請參考電腦選號玩法'
                        )
                        line_bot_api.reply_message(event.reply_token,message)
                    except:
                        line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!')) 
        else:
            try:
                message = TextSendMessage(
                    text = '請參考正確的使用者輸入'
                )
                line_bot_api.reply_message(event.reply_token,message)
            except:
                line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))   
            

        
            
if __name__ == '__main__':
    app.run()
