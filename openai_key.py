import os
import openai

# Please put your API keys here, the format is: ("sk-xxx", "org-xxx")
GPT_35_POOL = [
    # ("sk-xxx", "org-xxx"),
]

GPT_4_POOL = [
]

print("Testing api keys in GPT_35_POOL:")
new_pool = []
for key, org in GPT_35_POOL:
    try:
        response = openai.ChatCompletion.create(
            model="gpt-3.5-turbo-16k",
            messages=[{"role": "system", "content": "Hi"}],
            temperature=0,
            api_key=key,
            max_tokens=2,
            organization=org,
        )
        print(key, response.get("choices")[0]["message"]["content"])
        new_pool.append([key, org])
    except Exception as e:
        print(key, e)
        if "You exceeded your current quota" in str(e):
            continue
        if "Your account is not active" in str(e):
            continue
        if "account associated with this API key has been deactivated" in str(e):
            continue
        new_pool.append([key, org])

GPT_35_POOL = new_pool
print("Remaining GPT_35_POOL:")
for key in GPT_35_POOL:
    print(key)


print("Testing api keys in GPT_4_POOL:")
new_pool = []
for key, org in GPT_4_POOL:
    try:
        response = openai.ChatCompletion.create(
            model="gpt-4",
            messages=[{"role": "system", "content": "Hi!"}],
            temperature=0,
            api_key=key,
            organization=org
        )
        new_pool.append([key, org])
    except Exception as e:
        print(key, e)
        if "You exceeded your current quota" in str(e):
            continue
        if "Your account is not active" in str(e):
            continue
        if "account associated with this API key has been deactivated" in str(e):
            continue
        new_pool.append([key, org])

GPT_4_POOL = new_pool
print("Remaining GPT_4_POOL:")
for key in GPT_4_POOL:
    print(key)

GPT_ADA_POOL = GPT_35_POOL + GPT_4_POOL

assert len(GPT_ADA_POOL) > 0, "No valid API key found!"

os.environ["OPENAI_API_KEY"] = GPT_ADA_POOL[0][0]
os.environ["OPENAI_API_KEY_GPT"] = GPT_ADA_POOL[0][0]
os.environ["OPENAI_API_KEY_ADA"] = GPT_ADA_POOL[0][0]

