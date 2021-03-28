#!/usr/bin/env python
# coding: utf-8

# In[1]:


from flask import Flask
app = Flask(__name__)
from flask import Flask, request, abort
from linebot import LineBotApi, WebhookHandler
from linebot.exceptions import InvalidSignatureError
from linebot.models import MessageEvent, TextMessage, TextSendMessage, ImageSendMessage, StickerSendMessage, LocationSendMessage, QuickReply, QuickReplyButton, MessageAction
import requests
import elementpath
try:
    import xml.etree.cElemenTree as ET
except:
    from xml.etree import ElementTree as ET

line_bot_api = LineBotApi('')
handler = WebhookHandler('')    
    
def mononum(n):
    content = requests.get('http://invoice.etax.nat.gov.tw/invoice.xml')
    tree = ET.fromstring(content.text)
    items = list(tree.iter(tag='item'))
    title = items[n][0].text
    ptext = items[n][2].text
    ptext = ptext.replace('<p>','').replace('</p>','\n')
    return title + '月\n' + ptext[:-1]

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
    mtext = event.message.text     
    if mtext == '@本期中獎號碼':
        try:
            message = TextSendMessage(
                text = mononum(0)
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!'))
    elif mtext == '@前期中獎號碼':
        try:
            message = TextSendMessage(
                text = mononum(1) + '\n\n'+ mononum(2)
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='發生錯誤!')) 
    elif (len(mtext) == 3) & (mtext.isdigit()):
        try:
            ###取得xml
            content = requests.get('http://invoice.etax.nat.gov.tw/invoice.xml')
            #解析xml
            tree = ET.fromstring(content.text)
            #取得item標籤內容
            items = list(tree.iter(tag='item'))
            #取得中獎號碼 儲存到變數ptext
            ptext = items[0][2].text
            ptext = ptext.replace('<p>','').replace('</p>','')
            temlist = ptext.split('：')
            prizelist = []
            prizelist.append(temlist[1][5:8]) #特別獎後三碼
            prizelist.append(temlist[2][5:8]) #特獎後三碼
            for i in range(3): #增開6獎
                prizelist.append(temlist[3][9*i+5:9*i+8])
            sixlist = temlist[4].split('、')
            for i in range(len(sixlist)):
                    prizelist.append(sixlist[i])
            if mtext in prizelist:
                message_ = '符合其獎項後三碼,請自行核對前五碼!\n\n'
                message_ += mononum(0)
            else:
                message_ = '很可惜未中獎!!請輸入下一張發票最後三碼'
            message = TextSendMessage(
                text = message_
            )
            line_bot_api.reply_message(event.reply_token,message)
        except:
            line_bot_api.reply_message(event.reply_token,TextSendMessage(text='讀取發票發生錯誤'))            
    else:
        line_bot_api.reply_message(event.reply_token,TextSendMessage(text='請輸入發票最後末三碼進行對獎'))            

        
if __name__ == '__main__':
    app.run()