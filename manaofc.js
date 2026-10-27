const { version } = require("./package.json");
const axios = require('axios');
const crypto = require('crypto');
const cheerio = require('cheerio');
const yts = require('yt-search');
const express = require('express');
const fs = require('fs-extra');
const path = require('path');
const { promisify } = require('util');
const os = require('os');
const { exec } = require('child_process');
const execAsync = promisify(exec);
const moment = require('moment-timezone');
const { PAIR_NUMBER } = require('./pair');
const fetch = (...args) =>
  import("manaofc-node-fetch").then(({ default: fetch }) => fetch(...args));

const {
  default: makeWASocket,
  getAggregateVotesInPollMessage,
  useMultiFileAuthState,
  DisconnectReason,
  getDevice,
  fetchLatestBaileysVersion,
  jidNormalizedUser,
  getContentType,
  Browsers,
  makeInMemoryStore,
  makeCacheableSignalKeyStore,
  downloadContentFromMessage,
  generateWAMessageFromContent,
  prepareWAMessageMedia,
  generateForwardMessageContent,
  proto,
  pino,
} = require("manaofc-baileys");

const { Sticker, StickerTypes } = require('wa-sticker-formatter');

async function downloadQuotedMedia(manaofc, mek) {
  const ctx = mek.message?.extendedTextMessage?.contextInfo;
  let msg = ctx?.quotedMessage || mek.message;
  msg = msg?.ephemeralMessage?.message || msg?.viewOnceMessage?.message ||
        msg?.viewOnceMessageV2?.message || msg;

  const type = getContentType(msg);
  if (!['imageMessage', 'videoMessage', 'stickerMessage'].includes(type)) return null;

  const node = msg[type];
  const stream = await downloadContentFromMessage(node, type.replace('Message', ''));
  const chunks = [];
  for await (const chunk of stream) chunks.push(chunk);
  return { type, media: node, buffer: Buffer.concat(chunks) };
}

function getPackAuthor(q, cfg = {}) {
  let pack = cfg.BOT_NAME || 'manaofc';
  let author = cfg.OWNER_NAME || 'manaofc';
  if (q && q.includes('|')) {
    const [p, a] = q.split('|');
    pack = p.trim() || pack;
    author = (a || '').trim() || author;
  } else if (q && q.trim()) {
    pack = q.trim();
  }
  return { pack, author };
}

const getGroupAdmins = (participants) => {
    var admins = []
    for (let i of participants) {
        i.admin !== null ? admins.push(i.id) : ''
    }
    return admins
}

const runtime = (seconds) => {
seconds = Number(seconds)
var d = Math.floor(seconds / (3600 * 24))
var h = Math.floor(seconds % (3600 * 24) / 3600)
var m = Math.floor(seconds % 3600 / 60)
var s = Math.floor(seconds % 60)
var dDisplay = d > 0 ? d + (d == 1 ? ' day, ' : ' days, ') : ''
var hDisplay = h > 0 ? h + (h == 1 ? ' hour, ' : ' hours, ') : ''
var mDisplay = m > 0 ? m + (m == 1 ? ' minute, ' : ' minutes, ') : ''
var sDisplay = s > 0 ? s + (s == 1 ? ' second' : ' seconds') : ''
return dDisplay + hDisplay + mDisplay + sDisplay;
}

const delay = (ms) => new Promise(resolve => setTimeout(resolve, ms));

function getRandom(ext) {
    return `${Math.floor(Math.random() * 10000)}${ext || ''}`;
}

function getSriLankaTimestamp() {
    return moment().tz('Asia/Colombo').format('YYYY-MM-DD HH:mm:ss');
}
// ========== LOCAL STORAGE (No GitHub / Octokit) ==========
// Sessions & configs are saved directly to ./session/ on this server.
// NOTE: On ephemeral hosts (Heroku/Koyeb/Replit free tiers) the disk is
// wiped on redeploy/restart — pairing will be lost unless you use a
// persistent disk or a VPS.
const SESSION_BASE_PATH = './session';
fs.ensureDirSync(SESSION_BASE_PATH);

// Memory optimization: Use weak references for manaofcs
const activeSockets = new Map();
const manaofcCreationTime = new Map();
// Numbers being intentionally disconnected — prevents auto-restart from firing
const intentionalDisconnects = new Set();
// Anti-delete message store (keep last 500 messages per manaofc)
const messageStore = new Map();
const MAX_STORED_MESSAGES = 500;

// ========== ANTIDELETE HELPERS ==========
function storeMessage(key, message) {
    const jid = key.remoteJid;
    if (!messageStore.has(jid)) {
        messageStore.set(jid, new Map());
    }
    const chatStore = messageStore.get(jid);
    chatStore.set(key.id, {
        message: message,
        timestamp: Date.now(),
        key: key
    });

    if (chatStore.size > MAX_STORED_MESSAGES) {
        const oldestKey = chatStore.keys().next().value;
        chatStore.delete(oldestKey);
    }
}

function getStoredMessage(key) {
    const jid = key.remoteJid;
    const chatStore = messageStore.get(jid);
    if (chatStore && chatStore.has(key.id)) {
        return chatStore.get(key.id);
    }
    return null;
}

function deleteStoredMessage(key) {
    const jid = key.remoteJid;
    const chatStore = messageStore.get(jid);
    if (chatStore) {
        chatStore.delete(key.id);
    }
}

// ========== LID -> REAL NUMBER RESOLVER ==========
// Users with WhatsApp phone-number privacy arrive as LID JIDs
// (e.g. 48701405925425@lid) instead of 9476xxxxxxx@s.whatsapp.net.
// This resolves the real phone number, falling back gracefully.
async function resolveRealNumber(manaofc, jid, messageKey, chatJid) {
    try {
        // 1) PN fields carried on the message key itself (newer WhatsApp/Baileys)
        const alt = (messageKey && (messageKey.senderPn || messageKey.participantAlt || messageKey.remoteJidAlt)) || null;
        if (alt && !alt.endsWith('@lid')) {
            return '+' + alt.split('@')[0].split(':')[0];
        }

        if (!jid) return 'Unknown';
        const cleanJid = jidNormalizedUser(jid);
        const user = cleanJid.split('@')[0].split(':')[0];
        const isLid = cleanJid.endsWith('@lid');

        if (isLid) {
            // 2) Baileys LID mapping store (learned automatically from chats)
            try {
                const pn = await manaofc.signalRepository.lidMapping.getPNForLID(cleanJid);
                if (pn) return '+' + jidNormalizedUser(pn).split('@')[0].split(':')[0];
            } catch (e) { /* mapping not known yet */ }

            // 3) Group metadata fallback (groups keep PN alongside LID)
            if (chatJid && chatJid.endsWith('@g.us')) {
                try {
                    const metadata = await manaofc.groupMetadata(chatJid);
                    const match = (metadata.participants || []).find(p =>
                        (p.id && jidNormalizedUser(p.id) === cleanJid) ||
                        (p.lid && jidNormalizedUser(p.lid) === cleanJid)
                    );
                    const pnJid = match && (match.phoneNumber || match.pn);
                    if (pnJid) return '+' + pnJid.split('@')[0].split(':')[0];
                } catch (e) { /* ignore */ }
            }
        }

        // For non-LID JIDs, add '+' prefix to phone numbers (10+ digits)
        if (/^\d{10,}$/.test(user)) {
            return '+' + user;
        }

        return user;
    } catch (e) {
        const fallback = (jid || 'Unknown').split('@')[0].split(':')[0];
        if (/^\d{10,}$/.test(fallback)) {
            return '+' + fallback;
        }
        return fallback;
    }
}

// ========== ANTICALL HELPERS ==========
async function handleAntiCall(manaofc, json) {
    if (config.ANTICALL !== 'true') return;

    try {
        const callerId = json[0][2][0][1].from;
        const callId = json[0][2][0][1].id;
        const callStatus = json[0][2][0][2][0][1];

        if (callStatus === 'offer') {
            await manaofc.rejectCall(callId, callerId);

            const anticallMsg = config.ANTICALL_MSG;
            await manaofc.sendMessage(callerId, { 
                text: "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n📵 *Anti-Call Activated*\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" + anticallMsg + "\n\n⏰ " + getSriLankaTimestamp()
            });

            const botUserJid = jidNormalizedUser(manaofc.user.id);
            const callerNumber = await resolveRealNumber(manaofc, callerId);
            if (botUserJid) {
                await manaofc.sendMessage(botUserJid, {
                    text: "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n🚨 *Call Blocked!*\n📞 *Caller Number:* " + callerNumber + "\n⏰ Time: " + getSriLankaTimestamp() + "\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n_Call was automatically rejected._"
                });
            }

            console.log("Anti-call: Blocked call from " + callerId);
        }
    } catch (error) {
        console.error('Anti-call handler error:', error);
    }
}

// Memory optimization: Clean up unused variables and optimize loops
async function cleanDuplicateFiles(number) {
    try {
        const sanitizedNumber = number.replace(/[^0-9]/g, '');
        if (!fs.existsSync(SESSION_BASE_PATH)) return;

        const sessionFiles = fs.readdirSync(SESSION_BASE_PATH).filter(file =>
            file.startsWith("creds_" + sanitizedNumber + "_") && file.endsWith('.json')
        ).sort((a, b) => {
            const timeA = parseInt(a.match(/creds_\d+_(\d+)\.json/)?.[1] || 0);
            const timeB = parseInt(b.match(/creds_\d+_(\d+)\.json/)?.[1] || 0);
            return timeB - timeA;
        });

        if (sessionFiles.length > 1) {
            for (let i = 1; i < sessionFiles.length; i++) {
                fs.removeSync(path.join(SESSION_BASE_PATH, sessionFiles[i]));
                console.log("Deleted duplicate session file: " + sessionFiles[i]);
            }
        }
    } catch (error) {
        console.error("Failed to clean duplicate files for " + number + ":", error);
    }
}

// Memory optimization: Throttle status handlers
function setupStatusHandlers(manaofc) {
    let lastStatusInteraction = 0;
    const STATUS_INTERACTION_COOLDOWN = 10000;

    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const message = messages[0];

        if (
            !message?.key ||
            message.key.remoteJid !== 'status@broadcast' ||
            !message.key.participant
        ) {
            return;
        }

        const now = Date.now();

        if (now - lastStatusInteraction < STATUS_INTERACTION_COOLDOWN) {
            return;
        }

        try {
            const from = message.key.remoteJid;
            const presence = config.PRESENCE;

            // Handle Presence Updates
            if (presence) {
                if (presence === "composing") {
                    await manaofc.sendPresenceUpdate("composing", from);
                } else if (presence === "recording") {
                    await manaofc.sendPresenceUpdate("recording", from);
                } else if (presence === "unavailable") {
                    await manaofc.sendPresenceUpdate("unavailable", from);
                } else {
                    await manaofc.sendPresenceUpdate("available", from);
                }

                console.log(`Set ${presence} presence for ${from}`);
            }

            // Auto View Status
            if (config.AUTO_VIEW_STATUS === 'true') {
                let retries = parseInt(config.MAX_RETRIES) || 3;

                while (retries > 0) {
                    try {
                        await manaofc.readMessages([message.key]);
                        console.log(
                            `Viewed status from ${message.key.participant}`
                        );
                        break;
                    } catch (error) {
                        retries--;
                        console.warn(
                            `Failed to read status, retries left: ${retries}`,
                            error
                        );

                        if (retries === 0) throw error;

                        await delay(
                            1000 *
                                ((parseInt(config.MAX_RETRIES) || 3) -
                                    retries)
                        );
                    }
                }
            }

            // Auto Like Status
            if (config.AUTO_LIKE_STATUS === 'true') {
                const emojis = Array.isArray(config.AUTO_LIKE_EMOJI)
                    ? config.AUTO_LIKE_EMOJI
                    : config.AUTO_LIKE_EMOJI;

                const randomEmoji =
                    emojis[Math.floor(Math.random() * emojis.length)];

                let retries = parseInt(config.MAX_RETRIES) || 3;

                while (retries > 0) {
                    try {
                        await manaofc.sendMessage(
                            from,
                            {
                                react: {
                                    text: randomEmoji,
                                    key: message.key,
                                },
                            },
                            {
                                statusJidList: [message.key.participant],
                            }
                        );

                        lastStatusInteraction = now;

                        console.log(
                            `Reacted to status with ${randomEmoji}`
                        );

                        break;
                    } catch (error) {
                        retries--;

                        console.warn(
                            `Failed to react to status, retries left: ${retries}`,
                            error
                        );

                        if (retries === 0) throw error;

                        await delay(
                            1000 *
                                ((parseInt(config.MAX_RETRIES) || 3) -
                                    retries)
                        );
                    }
                }
            }
        } catch (error) {
            console.error("Status handler error:", error);
        }
    });
}
// ========== ANTIDELETE HANDLER ==========
function setupAntiDeleteHandler(manaofc) {
    // Always register — config.ANTIDELETE checked at runtime (no restart)
    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        for (const message of messages) {
            if (!message.key || !message.message) continue;
            if (message.key.remoteJid === 'status@broadcast') continue;

            try {
                storeMessage(message.key, message);
            } catch (error) {
                console.error('Anti-delete store error:', error);
            }
        }
    });

    manaofc.ev.on('messages.update', async (updates) => {
        for (const update of updates) {
            try {
                const { key, update: updateData } = update;

                if (updateData && updateData.message === null) {
                    if (config.ANTIDELETE !== 'true') continue;
                    const storedMsg = getStoredMessage(key);

                    if (storedMsg) {
                        const storedKey = storedMsg.key || key;
                        const senderJid = storedKey.participant || storedKey.remoteJid || key.participant || key.remoteJid;
                        const deletedBy = key.fromMe ? 'You' : await resolveRealNumber(manaofc, senderJid, storedKey, key.remoteJid);
                        const chatJid = key.remoteJid;
                        const isGroup = chatJid.endsWith('@g.us');

                        const botUserJid = jidNormalizedUser(manaofc.user.id);
                        const deletedByNumber = key.fromMe ? 'You' : await resolveRealNumber(manaofc, senderJid, storedKey, key.remoteJid);
                        if (botUserJid) {

                            let notifyText = "> _*Powered By Manaofc*_ ⚡\n\n";
                            notifyText += "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n";
                            notifyText += "🗑️ *Anti-Delete Alert!*\n\n";
                            notifyText += "👤 *Deleted By Number:* " + deletedByNumber + "\n";
                            notifyText += "💬 *Chat:* " + (isGroup ? 'Group' : 'Private') + "\n";
                            notifyText += "⏰ *Time:* " + getSriLankaTimestamp() + "\n";
                            notifyText += "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n";
                            notifyText += "📩 *Deleted Message:*\n";

                            const msg = storedMsg.message;
                            const msgType = getContentType(msg.message);

                            if (msgType === 'conversation') {
                                notifyText += "```" + msg.message.conversation + "```";
                            } else if (msgType === 'extendedTextMessage') {
                                notifyText += "```" + msg.message.extendedTextMessage.text + "```";
                            } else if (msgType === 'imageMessage') {
                                notifyText += "[Image] " + (msg.message.imageMessage.caption || '');
                            } else if (msgType === 'videoMessage') {
                                notifyText += "[Video] " + (msg.message.videoMessage.caption || '');
                            } else if (msgType === 'audioMessage') {
                                notifyText += "[Audio/Voice Message]";
                            } else if (msgType === 'documentMessage') {
                                notifyText += "[Document] " + (msg.message.documentMessage.fileName || '');
                            } else if (msgType === 'stickerMessage') {
                                notifyText += "[Sticker]";
                            } else {
                                notifyText += "[" + msgType + "]";
                            }

                            notifyText += "\n\n> _Message recovered by Anti-Delete_";

                            await manaofc.sendMessage(botUserJid, { text: notifyText });

                            try {
                                if (msgType === 'imageMessage' && msg.message.imageMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.imageMessage, 'image');
                                    let chunks = [];
                                    for await (const chunk of buffer) {
                                        chunks.push(chunk);
                                    }
                                    const imageBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        image: imageBuffer,
                                        caption: "> _*Powered By Manaofc*_ ⚡\n\n🗑️ *Deleted Image*\nFrom Number: " + deletedBy + "\nTime: " + getSriLankaTimestamp()
                                    });
                                } else if (msgType === 'videoMessage' && msg.message.videoMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.videoMessage, 'video');
                                    let chunks = [];
                                    for await (const chunk of buffer) {
                                        chunks.push(chunk);
                                    }
                                    const videoBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        video: videoBuffer,
                                        caption: "> _*Powered By Manaofc*_ ⚡\n\n🗑️ *Deleted Video*\nFrom Number: " + deletedBy + "\nTime: " + getSriLankaTimestamp()
                                    });
                                } else if (msgType === 'audioMessage' && msg.message.audioMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.audioMessage, 'audio');
                                    let chunks = [];
                                    for await (const chunk of buffer) {
                                        chunks.push(chunk);
                                    }
                                    const audioBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        audio: audioBuffer,
                                        mimetype: 'audio/mp4',
                                        ptt: msg.message.audioMessage.ptt || false
                                    });
                                } else if (msgType === 'stickerMessage' && msg.message.stickerMessage.url) {
                                    const buffer = await downloadContentFromMessage(msg.message.stickerMessage, 'sticker');
                                    let chunks = [];
                                    for await (const chunk of buffer) {
                                        chunks.push(chunk);
                                    }
                                    const stickerBuffer = Buffer.concat(chunks);
                                    await manaofc.sendMessage(botUserJid, {
                                        sticker: stickerBuffer
                                    });
                                }
                            } catch (mediaError) {
                                console.error('Failed to resend deleted media:', mediaError);
                            }
                        }

                        deleteStoredMessage(key);
                    }
                }
            } catch (error) {
                console.error('Anti-delete handler error:', error);
            }
        }
    });
}

// ========== ANTICALL HANDLER ==========
function setupAntiCallHandler(manaofc) {
    // Always register — config.ANTICALL checked at runtime
    manaofc.ws.on('CB:call', async (json) => {
        await handleAntiCall(manaofc, json);
    });

    manaofc.ev.on('call', async (calls) => {
        if (config.ANTICALL !== 'true') return;
        for (const call of calls) {
            try {
                if (call.status === 'offer') {
                    await manaofc.rejectCall(call.id, call.from);

                    const anticallMsg = config.ANTICALL_MSG;
                    await manaofc.sendMessage(call.from, { 
                        text: "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n📵 *Anti-Call Activated*\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" + anticallMsg + "\n\n⏰ " + getSriLankaTimestamp()
                    });

                    const botUserJid = jidNormalizedUser(manaofc.user.id);
                    const callerNumber2 = await resolveRealNumber(manaofc, call.from);
                    if (botUserJid) {
                        await manaofc.sendMessage(botUserJid, {
                            text: "> _*Powered By Manaofc*_ ⚡\n\n🚨 *Call Blocked!*\n\n📞 *Caller Number:* " + callerNumber2 + "\n⏰ Time: " + getSriLankaTimestamp() + "\n\n_Call was automatically rejected._"
                        });
                    }

                    console.log("Anti-call: Blocked call from " + call.from);
                }
            } catch (error) {
                console.error('Anti-call handler error:', error);
            }
        }
    });
}

// ========== AUTO STATUS SAVER ==========
function setupAutoStatusSaver(manaofc) {
    // Always register — checked at runtime
    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const message = messages[0];
        if (!message?.key || message.key.remoteJid !== 'status@broadcast' || !message.key.participant) return;
        if (config.AUTO_STATUS_SAVER !== 'true') return;

        try {
            const botUserJid = jidNormalizedUser(manaofc.user.id);
            if (!botUserJid) return;

            const msgType = getContentType(message.message);
            const sender = await resolveRealNumber(manaofc, message.key.participant, message.key, message.key.remoteJid);
            const caption = "> _*Powered By Manaofc*_ ⚡\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n💾 *Auto Status Saved*\n👤 *From:* " + sender + "\n📂 *Type:* " + (msgType?.replace('Message', '') || 'Unknown') + "\n⏰ *Time:* " + getSriLankaTimestamp() + "\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*";

            if (msgType === 'imageMessage') {
                const buffer = await downloadContentFromMessage(message.message.imageMessage, 'image');
                let chunks = [];
                for await (const chunk of buffer) chunks.push(chunk);
                await manaofc.sendMessage(botUserJid, {
                    image: Buffer.concat(chunks),
                    caption: caption
                });
            } else if (msgType === 'videoMessage') {
                const buffer = await downloadContentFromMessage(message.message.videoMessage, 'video');
                let chunks = [];
                for await (const chunk of buffer) chunks.push(chunk);
                await manaofc.sendMessage(botUserJid, {
                    video: Buffer.concat(chunks),
                    caption: caption,
                    mimetype: 'video/mp4'
                });
            } else if (msgType === 'audioMessage') {
                const buffer = await downloadContentFromMessage(message.message.audioMessage, 'audio');
                let chunks = [];
                for await (const chunk of buffer) chunks.push(chunk);
                await manaofc.sendMessage(botUserJid, {
                    audio: Buffer.concat(chunks),
                    mimetype: 'audio/mp4',
                    ptt: message.message.audioMessage.ptt || false
                });
            } else if (msgType === 'extendedTextMessage' || msgType === 'conversation') {
                const text = msgType === 'conversation' 
                    ? message.message.conversation 
                    : message.message.extendedTextMessage.text;
                await manaofc.sendMessage(botUserJid, {
                    text: caption + "\n\n📝 *Text:*\n```" + text + "```"
                });
            }
        } catch (error) {
            console.error('Auto status saver error:', error);
        }
    });
}

// ========== DATABASE HELPERS ==========
const settingsFile = path.join(__dirname, 'settings.json');
const nonBtnFile = path.join(__dirname, 'nonbtn.json');

// Single global config — mutate in place so .set applies instantly (no restart)
const config = {
    AUTO_VIEW_STATUS: 'false',
    AUTO_LIKE_STATUS: 'false',
    PRESENCE: 'composing',
    AUTO_LIKE_EMOJI: ['💥', '👍', '😍', '💗', '🎈', '🎉', '🥳', '😎', '🚀', '🔥'],
    AUTO_STATUS_SAVER: 'false',
    PREFIX: '.',
    MAX_RETRIES: 3,
    IMAGE_PATH: 'https://files.catbox.moe/i33owf.png',
    OWNER_NUMBER: '94759934522',
    WORK_TYPE: 'onlyme',
    BOT_MODE: 'private',
    ANTIDELETE: 'true',
    ANTICALL: 'false',
    BOT_NAME: 'MANAOFC LITE',
    FOOTER: '> *𝐏𝐨𝐰𝐞𝐫𝐝 𝐁𝐲 𝐌𝐚𝐧𝐚𝐨𝐟𝐜 ☻*',
    ANTICALL_MSG: '📵 Calls are not allowed! Please send a message instead.',
    NON_BUTTON: false,
    ANTI_LINK: 'false',
    MOROCCO_BLOCK: 'off',
    ANTI_BOT: 'false'
};

// Snapshot for reset (updfb)
const _configDefaults = JSON.parse(JSON.stringify(config));

// ================= JSON FUNCTIONS =================

function createJSON(file, data) {
    try {
        if (!fs.existsSync(file)) {
            fs.writeFileSync(
                file,
                JSON.stringify(data, null, 2),
                "utf8"
            );
        }
    } catch (error) {
        console.error("JSON create error:", error);
    }
}

function readJSONFile(file, defaultData) {
    try {
        createJSON(file, defaultData);

        const data = fs.readFileSync(file, "utf8");

        if (!data.trim()) {
            return defaultData;
        }

        return JSON.parse(data);
    } catch (error) {
        console.error("JSON read error:", error);
        return defaultData;
    }
}

function writeJSONFile(file, data) {
    try {
        fs.writeFileSync(
            file,
            JSON.stringify(data, null, 2),
            "utf8"
        );

        return true;
    } catch (error) {
        console.error("JSON write error:", error);
        return false;
    }
}

// Create database files
createJSON(settingsFile, _configDefaults);
createJSON(nonBtnFile, []);

// ================= CMD STORE FUNCTIONS =================

async function updateCMDStore(MsgID, CmdID) {
    try {
        const olds = readJSONFile(nonBtnFile, []);

        olds.push({
            [MsgID]: CmdID
        });

        return writeJSONFile(nonBtnFile, olds);
    } catch (error) {
        console.error("updateCMDStore error:", error);
        return false;
    }
}

async function isbtnID(MsgID) {
    try {
        const olds = readJSONFile(nonBtnFile, []);

        return olds.some(
            (item) =>
                Object.prototype.hasOwnProperty.call(item, MsgID)
        );
    } catch (error) {
        console.error("isbtnID error:", error);
        return false;
    }
}

async function getCMDStore(MsgID) {
    try {
        const olds = readJSONFile(nonBtnFile, []);

        for (const item of olds) {
            if (
                Object.prototype.hasOwnProperty.call(item, MsgID)
            ) {
                return item[MsgID];
            }
        }

        return null;
    } catch (error) {
        console.error("getCMDStore error:", error);
        return null;
    }
}

function getCmdForCmdId(CMD_ID_MAP, cmdId) {
    if (!CMD_ID_MAP) return null;
    const result = CMD_ID_MAP.find(
        (entry) => entry.cmdId === cmdId
    );

    return result ? result.cmd : null;
}

// ================= DATABASE ECT =================

async function connectdb() {
    try {
        createJSON(settingsFile, _configDefaults);
        createJSON(nonBtnFile, []);

        console.log("Local database connected 💜");
        return true;
    } catch (error) {
        console.error("Database ection error:", error);
        return false;
    }
}

// ================= UPDATE SETTING =================

async function input(setting, data) {
    try {
        const settings = readJSONFile(
            settingsFile,
            config
        );

        if (!Object.prototype.hasOwnProperty.call(settings, setting)) {
            console.warn(`Setting "${setting}" is not recognized.`);
            return false;
        }

        settings[setting] = data;

        // Update runtime config
        config[setting] = data;

        // Save locally
        return writeJSONFile(settingsFile, settings);

    } catch (error) {
        console.error("input error:", error);
        return false;
    }
}

// ================= GET SETTING =================

async function get(setting) {
    try {
        const settings = readJSONFile(
            settingsFile,
            config
        );

        if (!Object.prototype.hasOwnProperty.call(settings, setting)) {
            console.warn(`Setting "${setting}" is not recognized.`);
            return null;
        }

        return settings[setting];

    } catch (error) {
        console.error("get error:", error);
        return null;
    }
}

// ================= UPDATE CONFIG =================

async function updateDB() {
    try {
        const settings = readJSONFile(settingsFile, _configDefaults);
        Object.keys(settings).forEach((key) => {
            if (settings[key] !== undefined) config[key] = settings[key];
        });
        if (settings.MAX_RETRIES !== undefined) config.MAX_RETRIES = Number(settings.MAX_RETRIES);
        console.log("Local database updated ✅");
        return true;
    } catch (error) {
        console.error("updb error:", error);
        return false;
    }
}

// ================= RESET DATABASE =================

async function updfb() {
    try {
        Object.keys(_configDefaults).forEach((key) => {
            config[key] = Array.isArray(_configDefaults[key]) ? [..._configDefaults[key]] : _configDefaults[key];
        });
        writeJSONFile(settingsFile, config);
        console.log("Local database reset ✅");
        return true;
    } catch (error) {
        console.error("updfb error:", error);
        return false;
    }
}

// ================= RESET BUTTON DATABASE =================

async function upresbtn() {
    try {
        writeJSONFile(nonBtnFile, []);

        console.log("Button database cleared ✅");

        return true;

    } catch (error) {
        console.error("upresbtn error:", error);
        return false;
    }
}
// Load global config from disk on startup
(async () => {
    await connectdb();
    await updateDB();
})();

//=====================
// ========== COMMAND REGISTRY ==========
const commands = [];

function cmd(info, func) {
  var data = info;
  data.function = func;
  if (!data.dontAddCommandList) data.dontAddCommandList = false;
  if (!info.desc) info.desc = '';
  if (!data.fromMe) data.fromMe = false;
  if (!info.category) data.category = 'misc';
  if (!info.filename) data.filename = "Not Provided";
  commands.push(data);
  return data;
}
//====================================================
// ================= COMMANDS ======================
//====================================================

//=============================================
// ============= MENU COMMANDS ============= 
//=============================================
cmd({
  pattern: "menu",
  react: "📃",
  alias: ["panel","list","commands"],
  desc: "Get bot's command list.",
  category: "menu",
  use: '.menu',
  filename: __filename
},
async(manaofc, mek, m,{from, prefix, pushname, reply}) => {
try{
if(os.hostname().length == 12 ) hostname = 'replit'
else if(os.hostname().length == 36) hostname = 'heroku'
else if(os.hostname().length == 8) hostname = 'koyeb'
else hostname = os.hostname()

const sections = [
  {
    title: "📋 MENU CATEGORIES",
    rows: [
      { title: "⚙️ SETTINGS MENU", description: "Bot settings & configuration", rowId: prefix + "settingsmenu" },
      { title: "📥 DOWNLOAD MENU", description: "Download songs, videos & files", rowId: prefix + "downmenu" },
      { title: "🗣️ OWNER MENU", description: "Owner-only commands", rowId: prefix + "ownermenu" },
      { title: "🔍 SEARCH MENU", description: "Search YouTube, Google & more", rowId: prefix + "searchmenu" },
      { title: "🔄 CONVERT MENU", description: "Convert text, stickers & media", rowId: prefix + "convertmenu" },
      { title: "🔧 TOOLS MENU", description: "Useful tools & utilities", rowId: prefix + "toolsmenu" },
      { title: "🎐 OTHERS MENU", description: "Extra & fun commands", rowId: prefix + "othersmenu" },
      { title: "🎬 MOVIE MENU", description: "Movies & subtitles", rowId: prefix + "moviemenu" },
      { title: "🤖 AI MENU", description: "AI related commands", rowId: prefix + "aimenu" },
      { title: "🎨 LOGO MENU", description: "Create stylish text logos", rowId: prefix + "logomenu" },
      { title: "🏠 MAIN MENU", description: "Main bot commands", rowId: prefix + "mainmenu" },
      { title: "😃 FUN MENU", description: "Games, jokes & fun commands", rowId: prefix + "funmenu" },
    ]
  }
];

const listMessage = {
  image: config.IMAGE_PATH,
  text: `*👋 Hello ${pushname}*

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*│◈ ᴏᴡɴᴇʀ : manaofc*
*│◈ ᴠᴇʀꜱɪᴏɴ : ${version}*
*│◈ ʀᴜɴᴛɪᴍᴇ : ${runtime(process.uptime())}*
*│◈ ʀᴀᴍ ᴜꜱᴀɢᴇ : ${(process.memoryUsage().heapUsed / 1024 / 1024).toFixed(2)}MB / ${Math.round(require('os').totalmem / 1024 / 1024)}MB*
*╰━━━━━━━✧༺♥༻✧━━━━━━━*
`,
  footer: config.FOOTER,
  buttonText: "📋 Open Menu",
  sections
};

return await manaofc.listMessage(from, listMessage, mek)
} catch (e) {
reply('*Error !!*')
console.log(e)
}
})
// ============================================
// SETTINGS MENU
// ============================================
cmd({
    pattern: "settingsmenu",
    react: "⚙️",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*📥 ${config.BOT_NAME} SETTINGS MENU. ⚙️*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'settings'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};

let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// DOWNLOAD MENU
// ============================================
cmd({
    pattern: "downmenu",
    react: "📥",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*📥 ${config.BOT_NAME} DOWNLOAD MENU. 📥*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'download'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};

let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

//=================================
// OWNER MENU 
//===================================

cmd({
  pattern: "ownermenu",
  react: "🗣️",
  dontAddCommandList: true,
  filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🗣️ ${config.BOT_NAME} OWNER MENU. 🗣️*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'owner'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
let buttonMessaged = {
  image: config.IMAGE_PATH,
  caption: menuc,
  footer: config.FOOTER,
  headerType: 4,
  buttons: generatebutton
};
return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
reply('*ERROR !!*')
console.log(e)
}
})

// ============================================
// SEARCH MENU
// ============================================
cmd({
    pattern: "searchmenu",
    react: "🔍",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🔍 ${config.BOT_NAME} SEARCH MENU. 🔍*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'search'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})
// ============================================
// CONVERT MENU
// ============================================
cmd({
    pattern: "convertmenu",
    react: "🔄",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🔄 ${config.BOT_NAME} CONVERT MENU. 🔄*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'convert'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// TOOLS MENU
// ============================================
cmd({
    pattern: "toolsmenu",
    react: "🔧",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🔧 ${config.BOT_NAME} TOOLS MENU. 🔧*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'tools'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// OTHERS MENU
// ============================================
cmd({
    pattern: "othersmenu",
    react: "🎐",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🎐 ${config.BOT_NAME} OTHER MENU. 🎐*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'others'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// MOVIE MENU
// ============================================
cmd({
  pattern: "moviemenu",
  react: "🎬",
  dontAddCommandList: true,
  filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🎬 ${config.BOT_NAME} MOVIE MENU. 🎬*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'movie'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
let buttonMessaged = {
  image: config.IMAGE_PATH,
  caption: menuc,
  footer: config.FOOTER,
  headerType: 4,
  buttons: generatebutton
};
return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
reply('*ERROR !!*')
console.log(e)
}
})

// ============================================
// AI MENU
// ============================================
cmd({
    pattern: "aimenu",
    react: "🤖",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🤖 ${config.BOT_NAME} AI MENU. 🤖*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'ai'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// LOGO MENU
// ============================================
cmd({
    pattern: "logomenu",
    react: "🎨",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🎨 ${config.BOT_NAME} LOGO MENU. 🎨*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'logo'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// MAIN MENU
// ============================================
cmd({
    pattern: "mainmenu",
    react: "🏠",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*🏠 ${config.BOT_NAME} MAIN MENU. 🏠*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'main'){
if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};
let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

// ============================================
// FUN MENU
// ============================================

cmd({
    pattern: "funmenu",
    react: "😃",
    dontAddCommandList: true,
    filename: __filename
},
async(manaofc, mek, m,{from, prefix, command, reply}) => {
try{
let menuc = `*📥 ${config.BOT_NAME} FUN MENU. 😃*\n\n`
for (let i=0;i<commands.length;i++) { 
if(commands[i].category === 'fun'){
  if(!commands[i].dontAddCommandList){
menuc += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*
*╎🔖Command :* ${commands[i].pattern}
*╎🏷️Desc :* ${commands[i].desc}
*╎ 🧧Use:* ${commands[i].use}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n
`
}}};

let generatebutton = [{
    buttonId: `${prefix}ping`,
    buttonText: { displayText: 'GET BOT\'S PING' },
    type: 1
  }]
  let buttonMessaged = {
    image: config.IMAGE_PATH,
    caption: menuc,
    footer: config.FOOTER,
    headerType: 4,
    buttons: generatebutton
  };
  return await manaofc.buttonMessage(from, buttonMessaged, mek);
} catch (e) {
  reply('*ERROR !!*')
  console.log(e)
}
})

//=======================================
//========= SETTINGS COMMAND ==========
//========================================
cmd({
    pattern: "settings",
    react: "⚙️",
    alias: ["setup", "changesettings"],
    desc: "Show bot settings menu",
    category: "settings",
    use: ".settings",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, reply, isOwner}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        const botNumber = manaofc.user.id.split(":")[0].split("@")[0];

        const sections = [
            {
                title: "🔤 PREFIX",
                rows: [
                    { title: "🔹 Prefix ( . )", rowId: prefix + "set prefix ." },
                    { title: "🔹 Prefix ( ! )", rowId: prefix + "set prefix !" },
                    { title: "🔹 Prefix ( # )", rowId: prefix + "set prefix #" },
                    { title: "🔹 Prefix ( / )", rowId: prefix + "set prefix /" },
                    { title: "🔹 Prefix ( * )", rowId: prefix + "set prefix *" },
                    { title: "🔹 Prefix ( $ )", rowId: prefix + "set prefix $" },
                ],
            },
            {
                title: "🔧 WORK TYPE",
                rows: [
                    { title: "👥 Public", rowId: prefix + "set botmode public" },
                    { title: "👤 Only Me (Private)", rowId: prefix + "set botmode private" },
                ],
            },
            {
                title: "🤖 BOT PRESENCE",
                rows: [
                    { title: "💬 Auto Typing", rowId: prefix + "set presence composing" },
                    { title: "🎙️ Auto Recording", rowId: prefix + "set presence recording" },
                    { title: "🔋 Always Online", rowId: prefix + "set presence available" },
                    { title: "🪫 Always Offline", rowId: prefix + "set presence unavailable" },
                ],
            },
            {
                title: "👁️ AUTO VIEW STATUS",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set autoview on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set autoview off" },
                ],
            },
            {
                title: "❤️ AUTO LIKE STATUS",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set autolike on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set autolike off" },
                ],
            },
            {
                title: "💾 AUTO STATUS SAVER",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set autosave on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set autosave off" },
                ],
            },
            {
                title: "📞 AUTO REJECT CALL",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set anticall on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set anticall off" },
                ],
            },
            {
                title: "🗑️ ANTI DELETE",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set antidelete on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set antidelete off" },
                ],
            },
            {
                title: "🔘 NON BUTTON MODE",
                rows: [
                    { title: "✅ Turn ON (Text Mode)", rowId: prefix + "set nonbutton on" },
                    { title: "❎ Turn OFF (Button Mode)", rowId: prefix + "set nonbutton off" },
                ],
            },
            {
                title: "🤖 ANTI BOT",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set antibot on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set antibot off" },
                ],
            },
            {
                title: "🔗  ANTI LINK",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set antilink on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set antilink off" },
                ],
            },
            {
                title: "🇲🇦 MOROCCO BLOCK",
                rows: [
                    { title: "✅ Turn ON", rowId: prefix + "set morocco on" },
                    { title: "❎ Turn OFF", rowId: prefix + "set morocco off" },
                ],
            },
        ];

        const desc = `⚙️ \`${config.BOT_NAME || 'MANAOFC LITE'} SETTINGS\` ⚙️

> ◈ *Owner:* manaofc
> ◈ *Version:* ${version}
> ◈ *Prefix:* ${config.PREFIX || '.'}
> ◈ *Mode:* ${(config.BOT_MODE || 'public').toUpperCase()}`;

        let listset = {
            image: config.IMAGE_PATH,
            text: desc,
            footer: config.FOOTER,
            buttonText: "⚙️ Open Settings",
            sections,
        };
        await manaofc.listMessage(from, listset, mek);

    } catch (e) {
        console.error(e);
        reply(`❌ Error: ${e.message}`);
    }
});

//==============
cmd({
    pattern: "set",
    react: "🔧",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply, isOwner}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        const botNumber = manaofc.user.id.split(":")[0].split("@")[0];

        if (!q) {
            return reply("❌ *Provide a value!*\nExample: `.set prefix !`");
        }

        const args = q.trim().split(/ +/);
        const field = args[0].toLowerCase();
        const value = args.slice(1).join(" ");

        if (!value) {
            return reply("❌ *Provide a value!*\nExample: `.set prefix !`");
        }

        const updates = { ...config };

        switch (field) {
            case 'prefix':
                updates.PREFIX = value;
                break;
            case 'botmode':
            case 'mode':
                if (!['public','private','inbox','group'].includes(value.toLowerCase())) {
                    return reply("❌ *Valid modes:* public, private, inbox, group");
                }
                updates.BOT_MODE = value.toLowerCase();
                break;
            case 'presence':
                if (!['composing','recording','available','unavailable'].includes(value.toLowerCase())) {
                    return reply("❌ *Valid presence:* composing, recording, available, unavailable");
                }
                updates.PRESENCE = value.toLowerCase();
                break;
            case 'autoview':
            case 'auto_view_status':
                updates.AUTO_VIEW_STATUS = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'autolike':
            case 'auto_like_status':
                updates.AUTO_LIKE_STATUS = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'autosave':
            case 'auto_status_saver':
                updates.AUTO_STATUS_SAVER = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'antidelete':
                updates.ANTIDELETE = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'anticall':
                updates.ANTICALL = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'antilink':
                updates.ANTI_LINK = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'nonbutton':
            case 'non_button':
                updates.NON_BUTTON = value.toLowerCase() === 'on' || value === 'true' ? true : false;
                break;
            case 'antibot':
            case 'anti_bot':
                updates.ANTI_BOT = value.toLowerCase() === 'on' || value === 'true' ? 'true' : 'false';
                break;
            case 'morocco':
            case 'morocco_block':
                updates.MOROCCO_BLOCK = value.toLowerCase() === 'on' || value === 'true' ? 'on' : 'off';
                break;
            default:
                return reply("❌ *Unknown field!*\nTry: `.set prefix !`");
        }

        Object.assign(config, updates);
        writeJSONFile(settingsFile, config);
        reply(`✅ *Setting updated!*\n\n*${field}* → ${value}\n\n_Applied instantly — no restart needed._`);

    } catch (e) {
        console.error(e);
        reply(`❌ Error: ${e.message}`);
    }
});

//=========

cmd(
{
    pattern: "getconfig",
    alias: ["config", "botconfig", "currentsettings"],
    desc: "View all current bot settings",
    category: "settings",
    react: "📋",
    use: ".getconfig",
    filename: __filename
},
async (manaofc, mek, m, { from, reply, isOwner }) => {
    try {
        if (!isOwner) {
            return reply("❌ *Only owner can use this command!*");
        }

        const botNumber = manaofc.user.id.split(":")[0].split("@")[0];

        let configText = "";

      configText += `🤖 *${config.BOT_NAME}*\n\n`;
      configText += "📋 *CURRENT BOT CONFIGURATION* 📋\n\n";
      configText += `🔢 *Bot Number:* ${botNumber}\n`;
      configText += `👑 *Owner Number:* ${config.OWNER_NUMBER || "N/A"}\n`;
      configText += `⏰ *Time:* ${getSriLankaTimestamp()}\n\n`;
      configText += "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n";
      configText += `*╎ 🔧 BOT_MODE:* ${(config.BOT_MODE || "public").toUpperCase()}\n`;
      configText += `*╎ 🔧 WORK_TYPE:* ${(config.WORK_TYPE || "public").toUpperCase()}\n`;
      configText += `*╎ 🎭 PRESENCE:* ${
        config.PRESENCE
        ? config.PRESENCE.toUpperCase()
        : "AVAILABLE"
      }\n`;
      configText += `*╎ 👁️ AUTO_VIEW_STATUS:* ${
        config.AUTO_VIEW_STATUS === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ ❤️ AUTO_LIKE_STATUS:* ${
        config.AUTO_LIKE_STATUS === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 📱 AUTO_STATUS_SAVER:* ${
        config.AUTO_STATUS_SAVER === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 📞 ANTICALL:* ${
        config.ANTICALL === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🗑️ ANTIDELETE:* ${
        config.ANTIDELETE === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🤖 ANTI_BOT:* ${
        config.ANTI_BOT === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🇲🇦 MOROCCO_BLOCK:* ${
        config.MOROCCO_BLOCK === "on" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🔗 ANTI_LINK:* ${
        config.ANTI_LINK === "true" ? "✅ ON" : "❌ OFF"
      }\n`;
      configText += `*╎ 🔤 PREFIX:* ${config.PREFIX || "."}\n`;
      configText += `*╎ 🎨 LIKE_EMOJIS:* ${
        Array.isArray(config.AUTO_LIKE_EMOJI)
        ? config.AUTO_LIKE_EMOJI.join(" ")
        : (config.AUTO_LIKE_EMOJI || "❤️")
      }\n`;
      configText += `*╎ 🔘 NON_BUTTON:* ${
        config.NON_BUTTON === true ? "✅ ON (Text Mode)" : "❌ OFF (Button Mode)"
      }\n`;
      configText += `*╎ 🔄 MAX_RETRIES:* ${config.MAX_RETRIES || 3}\n`;
      configText += `*╎ 🖼️ IMAGE_PATH:* ${config.IMAGE_PATH ? "✅ Set" : "❌ Not Set"}\n`;
      configText += `*╎ 💬 ANTICALL_MSG:* ${config.ANTICALL_MSG || "N/A"}\n`;
      configText += `*╎ 📝 FOOTER:* ${config.FOOTER || "N/A"}\n`;
      configText += "*╰━━━━━━━✧༺♥༻✧━━━━━━━*";
      
        await manaofc.sendMessage(
            from,
            {
                image: {
                    url: config.IMAGE_PATH
                },
                caption: configText
            },
            {
                quoted: mek
            }
        );

    } catch (e) {
        console.error("[GETCONFIG ERROR]:", e);
        reply(`❌ Error: ${e.message}`);
    }
});

//===========================================
// ========== DOWNLOAD COMMANDS ==========
//============================================
async function fetchWithRetry(url, opts, retries = 3) {
  for (let i = 0; i < retries; i++) {
    try {
      return await axios.get(url, opts);
    } catch (e) {
      if (i === retries - 1) throw e;
      await new Promise(r => setTimeout(r, 1500));
    }
  }
}

async function searchAnime(query) {
  const url = 'https://animeheaven.me/search.php?s=' + encodeURIComponent(query);
  const { data } = await fetchWithRetry(url, {
    headers: {
      accept: 'text/html',
      'User-Agent': 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36',
      Referer: 'https://animeheaven.me/'
    }
  });
  const $ = cheerio.load(data);
  const list = [];
  $('.similarimg').each((_, el) => {
    const title = $(el).find('.similarname a').text().trim();
    const href = $(el).find('.similarname a').attr('href');
    const img = $(el).find('img.coverimg').attr('src');
    if (title && href) {
      list.push({
        title,
        url: 'https://animeheaven.me/' + href,
        image: img ? 'https://animeheaven.me/' + img : ''
      });
    }
  });
  return list;
}

  cmd({
    pattern: 'animesearch',
    alias: ['animes', 'ahsearch'],
    react: '🎌',
    desc: 'Search anime on animeheaven.me',
    category: 'download',
    use: '.animesearch naruto',
    filename: __filename
  }, async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply('❌ Example: `.animesearch one piece`');
      await reply('🔍 Searching anime...');
      const results = await searchAnime(q);
      if (!results.length) return reply('❌ No results for: ' + q);

      let text = `🎌 *Anime Search: ${q}*\n\n`;
      results.slice(0, 10).forEach((r, i) => {
        text += `*${i + 1}.* ${r.title}\n🔗 ${r.url}\n\n`;
      });
      text += (config.FOOTER);

      if (results[0].image) {
        await manaofc.sendMessage(from, {
          image: { url: results[0].image },
          caption: text
        }, { quoted: mek });
      } else {
        await reply(text);
      }
    } catch (e) {
      console.error('anime search error:', e);
      reply('❌ Anime search failed: ' + (e.message || ''));
    }
  });

//============== IMAGE DOWNLOAD ===========
cmd({
    pattern: "pinterest",
    react: '🖼️',
    alias: ["pinterestdl"],
    desc: "Search for related pics on Pinterest.",
    category: "download",
    use: '.pinterest <query>',
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply}) => {
    try {
        if (!q) return await reply("*Please provide a search query!*");

        const res = await fetch('https://allstars-apis.vercel.app/pinterest?search=' + encodeURIComponent(q));
        const result = await res.json();
        
        const data = result.data;
        
        if (!data || data.length === 0) {
            return await reply("*No images found!*");
        }

        for (let i = 0; i < Math.min(data.length, 7); i++) {
            await manaofc.sendMessage(from, { 
                image: { url: data[i] }, 
                caption: config.FOOTER 
            }, { quoted: mek });
        }
    } catch (e) {
        await reply("*Error fetching images!*");
        console.log(e);
    }
});


/* ================== SONG SEARCH ================== */
cmd(
  {
    pattern: "song",
    react: "🎵",
    alias: ["music", "yt"],
    category: "download",
    desc: "Search & download YouTube songs (audio)",
    use: ".song <Song Name or YouTube URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Please provide a song name or YouTube URL!*");

      const search = await yts(q);
      if (!search.videos || search.videos.length === 0) {
        return reply("⚠️ *No song results found!*");
      }

      const song = search.videos[0];

      const sections = [
        {
          title: "🎵 DOWNLOAD OPTIONS",
          rows: [
            {
              title: "🎙 AUDIO TYPE",
              description: "Download as audio (mp3)",
              rowId: `${prefix}yta ${song.url}`,
            },
            {
              title: "📁 DOCUMENT TYPE",
              description: "Download as document (mp3)",
              rowId: `${prefix}ytd ${song.url}`,
            },
          ],
        },
      ];

      const listMessage = {
        image: song.thumbnail,
        text: `*🎶 ${config.BOT_NAME} SONG DOWNLOAD.📥*
*╭━━━━━━━✧༺♥༻✧━━━━━━━*
│✨ \`Title\` : ${song.title}
│⏰ \`Duration\` : ${song.timestamp}
│👀 \`Views\` : ${song.views}
│📅 \`Uploaded\` : ${song.ago}
│📺 \`Channel\` : ${song.author?.name || "Unknown"}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`,
        footer: config.FOOTER,
        buttonText: "📥 Open Options",
        sections,
      };

      await manaofc.listMessage(from, listMessage, mek);
    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);
/* ================== AUDIO DOWNLOAD ================== */
cmd(
  {
    pattern: "yta",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a YouTube URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        "https://manaofc-api.vercel.app/yt/mp3?url=" + encodeURIComponent(q) + "&apikey=manaofc-uvfk09u1"
      );
      const json = await res.json();

      // Direct parse — { status, data: { title, download_url, ... } }
      const data = json?.data;
      if (!json?.status || !data?.download_url) {
        return reply("❌ *Failed to fetch audio!*\n" + (json?.error || json?.message || ""));
      }

      await manaofc.sendMessage(
        from,
        {
          audio: { url: data.download_url },
          mimetype: "audio/mpeg",
          ptt: false,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });
    } catch (e) {
      console.log(e);
      reply("❌ *Audio download failed!*");
    }
  }
);

/* ================== DOCUMENT DOWNLOAD ================== */
cmd(
  {
    pattern: "ytd",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a YouTube URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        "https://manaofc-api.vercel.app/yt/mp3?url=" + encodeURIComponent(q) + "&apikey=manaofc-uvfk09u1"
      );
      const json = await res.json();

      // Direct parse — { status, data: { title, download_url, ... } }
      const data = json?.data;
      if (!json?.status || !data?.download_url) {
        return reply("❌ *Failed to fetch document link!*\n" + (json?.error || json?.message || ""));
      }

      const title = data.title || "audio";
      await manaofc.sendMessage(
        from,
        {
          document: { url: data.download_url },
          mimetype: "audio/mpeg",
          fileName: title + ".mp3",
          caption: "🎵 *" + title + "*",
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });
    } catch (e) {
      console.log(e);
      reply("❌ *Document download failed!*");
    }
  }
);

/* ================== VIDEO SEARCH ================== */
cmd(
  {
    pattern: "video",
    react: "🎬",
    alias: ["vid", "ytvsearch"],
    category: "download",
    desc: "Search & download YouTube videos",
    use: ".video <Video Name or YouTube URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Please provide a video name or YouTube URL!*");

      const search = await yts(q);
      if (!search.videos || search.videos.length === 0) {
        return reply("⚠️ *No video results found!*");
      }

      const video = search.videos[0];

      const sections = [
        {
          title: "🎬 DOWNLOAD OPTIONS",
          rows: [
            {
              title: "🎥 VIDEO TYPE",
              description: "Download as video (mp4)",
              rowId: `${prefix}ytv ${video.url}`,
            },
            {
              title: "📁 DOCUMENT TYPE",
              description: "Download as document (mp4)",
              rowId: `${prefix}ytvd ${video.url}`,
            },
          ],
        },
      ];

      const listMessage = {
        image: video.thumbnail,
        text: `*🎬 ${config.BOT_NAME} VIDEO DOWNLOAD.📥*
*╭━━━━━━━✧༺♥༻✧━━━━━━━*
│✨ \`Title\` : ${video.title}
│⏰ \`Duration\` : ${video.timestamp}
│👀 \`Views\` : ${video.views}
│📅 \`Uploaded\` : ${video.ago}
│📺 \`Channel\` : ${video.author?.name || "Unknown"}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*`,
        footer: config.FOOTER,
        title: "Select Download Type",
        buttonText: "📥 Open Options",
        sections,
      };

      await manaofc.listMessage(from, listMessage, mek);
    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

/* ================== VIDEO DOWNLOAD (ytv) ================== */
cmd(
  {
    pattern: "ytv",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a YouTube URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        "https://manaofc-api.vercel.app/yt/mp4?url=" + encodeURIComponent(q) + "&apikey=manaofc-uvfk09u1"
      );
      const json = await res.json();

      // Direct parse — { status, data: { title, download_url, quality, ... } }
      const data = json?.data;
      if (!json?.status || !data?.download_url) {
        return reply("❌ *Failed to fetch video!*\n" + (json?.error || json?.message || ""));
      }

      const title = data.title || "video";
      const quality = data.quality || "Video";

      await manaofc.sendMessage(
        from,
        {
          video: { url: data.download_url },
          mimetype: "video/mp4",
          caption: `🎬 *${title}*\n📊 *${quality}*\n\n${config.FOOTER}`,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });
    } catch (e) {
      console.log(e);
      reply("❌ *Video download failed!*");
    }
  }
);

/* ================== VIDEO DOCUMENT DOWNLOAD (ytvd) ================== */
cmd(
  {
    pattern: "ytvd",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a YouTube URL!*");

      await manaofc.sendMessage(from, {
        react: { text: "⬇️", key: mek.key },
      });

      const res = await fetch(
        "https://manaofc-api.vercel.app/yt/mp4?url=" + encodeURIComponent(q) + "&apikey=manaofc-uvfk09u1"
      );
      const json = await res.json();

      // Direct parse — { status, data: { title, download_url, ... } }
      const data = json?.data;
      if (!json?.status || !data?.download_url) {
        return reply("❌ *Failed to fetch document link!*\n" + (json?.error || json?.message || ""));
      }

      const title = data.title || "video";
      await manaofc.sendMessage(
        from,
        {
          document: { url: data.download_url },
          mimetype: "video/mp4",
          fileName: title + ".mp4",
          caption: `🎬 *${title}*\n\n${config.FOOTER}`,
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, {
        react: { text: "✔️", key: mek.key },
      });
    } catch (e) {
      console.log(e);
      reply("❌ *Document download failed!*");
    }
  }
);

/* ================== FACEBOOK VIDEO DOWNLOADER ================== */
cmd(
  {
    pattern: "fb",
    react: "📘",
    alias: ["facebook", "fbdl"],
    category: "download",
    use: ".fb <Facebook Video URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a Facebook URL!*");

      await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

      const res = await fetch(
        `https://manaofc-api.vercel.app/facebook/download?url=${encodeURIComponent(q.trim())}&apikey=manaofc-uvfk09u1`
      );
      const json = await res.json();

      // Direct parse — { status, data: { title, thumbnail, media: [{ quality, url }] } }
      const fb = json?.data;
      if (!json?.status || !fb) {
        return reply("❌ *Failed to fetch video!*\n" + (json?.error || json?.message || ""));
      }

      const media = Array.isArray(fb.media) ? fb.media : [];
      const videoItems = media.filter((m) => (m.type || "video") === "video" || m.url);
      const pick =
        videoItems.find((m) => /hd|1080|720/i.test(String(m.quality || ""))) ||
        videoItems[0] ||
        null;

      const videoUrl = pick?.url || null;
      if (!videoUrl) {
        return reply("❌ *No download links found!*");
      }

      const fbTitle = String(fb.title || "Facebook Video").replace(/\r\n/g, " ").slice(0, 120);
      const quality = pick?.quality || "Video";

      if (fb.thumbnail) {
        await manaofc.sendMessage(from, {
          image: { url: fb.thumbnail },
          caption: `📘 *${fbTitle}*\n📊 ${quality}\n⏳ Sending video...`
        }, { quoted: mek });
      }

      await manaofc.sendMessage(
        from,
        {
          video: { url: videoUrl },
          caption: `📘 *${fbTitle}*\n📊 *${quality}*\n✅ ${config.BOT_NAME}`
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, { react: { text: "✔️", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Facebook video download failed!*");
    }
  }
);


/* ================== TIKTOK COMMAND ================== */
cmd(
  {
    pattern: "tiktok",
    react: "🎵",
    alias: ["tt", "tik"],
    category: "download",
    use: ".tiktok <TikTok URL>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Please provide a TikTok URL!*");

      await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

      const apiUrl = `https://manaofc-api.vercel.app/tiktok/download?url=${encodeURIComponent(q.trim())}&apikey=manaofc-uvfk09u1`;
      const res = await fetch(apiUrl);
      const json = await res.json();

      const tt = json?.data;
      if (!json?.status || !tt) {
        return reply("⚠️ *Failed to fetch TikTok video!*");
      }

      const media = Array.isArray(tt.media) ? tt.media : [];
      const videoItem = media.find((m) => (m.type || "video") === "video") || media[0];

      if (!videoItem?.url) {
        return reply("⚠️ *Video URL not found!*");
      }

      const caption =
        `*🎵 ${config.BOT_NAME} TIKTOK*\n` +
        `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n` +
        `│✨ Title: ${(tt.title || "No title").slice(0, 80)}\n` +
        `│📊 Quality: ${videoItem?.quality || "HD"}\n` +
        `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

      // Thumbnail එක යවනවා (optional)
      if (tt.thumbnail) {
        await manaofc.sendMessage(from, {
          image: { url: tt.thumbnail },
          caption
        }, { quoted: mek });
      }

      // Video එක යවනවා
      await manaofc.sendMessage(
        from,
        {
          video: { url: videoItem.url },
          caption: `🎥 *${(tt.title || "TikTok Video").slice(0, 100)}*\n📊 ${videoItem?.quality || "HD"}\n✅ ${config.BOT_NAME}`
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while fetching TikTok video!*");
    }
  }
);
/* ================== MEDIAFIRE COMMAND ================== */

cmd({
    pattern: "mediafire",
    alias: ["mf", "mfire"],
    react: "📦",
    desc: "Download MediaFire file",
    category: "download",
    use: ".mediafire <url>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Need a MediaFire URL!*");
        await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

        const res = await fetch(
            "https://manaofc-api.vercel.app/mediafire/download?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-uvfk09u1"
        );
        const json = await res.json();

        // Direct parse — { status, data: { fileName, fileSize, downloadUrl, mimeType } }
        const data = json?.data;
        if (!json?.status || !data) {
            return reply("❌ *Failed to get MediaFire link!*\n" + (json?.message || json?.error || ""));
        }

        const link = data.downloadUrl || data.download_url || null;
        const name = data.fileName || data.filename || data.name || "file";
        const size = data.fileSize || data.size || "";
        const mime = data.mimeType || "application/octet-stream";

        if (!link) {
            return reply("❌ *Download URL not found!*");
        }

        await manaofc.sendMessage(from, {
            document: { url: link },
            fileName: name,
            mimetype: mime,
            caption: `📦 *MediaFire*\n📁 ${name}\n📊 ${size}\n\n${config.FOOTER || ""}`
        }, { quoted: mek });

        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.log(e);
        reply("❌ *MediaFire download failed!*");
    }
});

/* ================== GDRIVE COMMAND ================== */

cmd({
    pattern: "gdrive",
    alias: ["drive", "gd"],
    react: "📁",
    desc: "Download Google Drive file",
    category: "download",
    use: ".gdrive <url>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Need a Google Drive URL!*");
        await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

        const res = await fetch(
            "https://manaofc-api.vercel.app/gdrive/download?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-uvfk09u1"
        );
        const json = await res.json();

        // Direct parse — { status, data: { fileName, fileSize, downloadUrl, mimeType } }
        const data = json?.data;
        if (!json?.status || !data) {
            return reply("❌ *Failed to get Drive link!*\n" + (json?.message || json?.error || ""));
        }

        const link = data.downloadUrl || data.download_url || null;
        const name = data.fileName || data.filename || data.name || "gdrive_file";
        const size = data.fileSize || data.size || "";
        const mime = data.mimeType || "application/octet-stream";

        if (!link) {
            return reply("❌ *Download URL not found!*");
        }

        await manaofc.sendMessage(from, {
            document: { url: link },
            fileName: name,
            mimetype: mime,
            caption: `📁 *Google Drive*\n📄 ${name}\n📊 ${size}\n\n${config.FOOTER || ""}`
        }, { quoted: mek });

        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.log(e);
        reply("❌ *GDrive download failed!*");
    }
});


// ============================================
// MEGA DOWNLOAD COMMAND
// ============================================



// ============================================
// AN1 SEARCH COMMAND
// ============================================
cmd(
  {
    pattern: "an1",
    react: "🎮",
    alias: ["mod", "an1search"],
    category: "download",
    use: ".an1 <App Name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return await reply("*Please provide a game/app name!*\n\nExample: `.an1 freefire`");

      await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

      const response = await fetch(
        "https://manaofc-api.vercel.app/an1/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-uvfk09u1z"
      );
      const res = await response.json();

      // Direct parse — matches { status, data: { results: [...] } }
      const results = Array.isArray(res?.data?.results)
        ? res.data.results
        : (Array.isArray(res?.data) ? res.data : []);

      if (!res?.status || !results.length) {
        return await reply("*❌ No results found on AN1!*");
      }

      const sections = [{
        title: "🎮 AN1 Results",
        rows: results.slice(0, 12).map((v, i) => {
          const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
          const short = title.length > 40 ? title.slice(0, 37) + "..." : title;
          const desc = [
            v.developer || "",
            v.rating ? `⭐ ${v.rating}` : ""
          ].filter(Boolean).join(" • ") || "MOD / APK";
          return {
            title: `${i + 1}. ${short}`,
            description: desc.slice(0, 60),
            rowId: prefix + "dan1 " + (v.link || v.url || "")
          };
        })
      }];

      const listMessage = {
        image: "https://files.catbox.moe/wesr4b.png",
        text: `*🔰 ${config.BOT_NAME} AN1 SEARCH*\n\n🔍 Query: *${q}*\n📊 Results: *${results.length}*\n\nSelect an app to download:`,
        footer: config.FOOTER,
        buttonText: "📥 Open Results",
        sections
      };

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.error(e);
      await reply("*ERROR !!* " + e.message);
    }
  }
);

// ============================================
// DAN1 DOWNLOAD COMMAND (AUTO DOCUMENT SEND)
// ============================================
cmd(
  {
    pattern: "dan1",
    react: "📥",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return await reply("*❌ Please provide an AN1 URL!*");

      await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

      const response = await fetch(
        "https://manaofc-api.vercel.app/an1/download?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
      );
      const res = await response.json();

      // Direct parse — matches { status, data: { title, directDownloadUrl, ... } }
      const app = res?.data;
      if (!res?.status || !app || typeof app !== "object") {
        return await reply("*❌ Download info not available!*\n\n*Error:* " + (res?.message || "Unknown error"));
      }

      const downloadUrl = app.directDownloadUrl || app.downloadUrl || app.download_url || null;
      if (!downloadUrl) {
        return await reply("*❌ Direct download link not found!*");
      }

      const title = app.title || "App";
      const version = app.version || "unknown";
      const size = app.size || "N/A";
      const developer = app.developer || "N/A";
      const rating = app.rating || "N/A";
      const icon = app.icon || app.image;

      let caption = "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n";
      caption += `*📦 ${title}*\n\n`;
      caption += `*Version:* ${version}\n`;
      caption += `*Size:* ${size}\n`;
      caption += `*Developer:* ${developer}\n`;
      caption += `*Rating:* ⭐ ${rating}\n`;
      if (app.category) caption += `*Category:* ${app.category}\n`;
      if (app.androidVersion) caption += `*Android:* ${app.androidVersion}\n`;
      caption += "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n";
      caption += "⏳ *Sending APK file...*";

      if (icon) {
        await manaofc.sendMessage(from, {
          image: { url: icon },
          caption
        }, { quoted: mek });
      } else {
        await reply(caption);
      }

      await delay(1000);

      const safeName = String(title).replace(/[^a-zA-Z0-9._-]/g, "_").slice(0, 60);
      const fileName = `${safeName}_v${String(version).replace(/[^a-zA-Z0-9._-]/g, "")}.apk`;

      await manaofc.sendMessage(from, {
        document: { url: downloadUrl },
        mimetype: "application/vnd.android.package-archive",
        fileName,
        caption: `🎮 *${title}*\n✅ ${config.BOT_NAME}\n\n${config.FOOTER || ""}`
      }, { quoted: mek });

      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.error(e);
      await reply("*❌ ERROR !!*\n\n" + e.message);
    }
  }
);

// ============================================
// XNXX SEARCH
// ============================================
cmd({
    pattern: "xnxx",
    desc: "Search XNXX videos",
    use: ".xnxx <query>",
    react: "🔞",
    category: "download",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
        if (!q) return reply("*Please enter a query!*\n\nExample: `.xnxx query`");

        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

        const response = await fetch(
            "https://manaofc-api.vercel.app/xnxx/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const xnsearch = await response.json();

        let list = [];
        if (Array.isArray(xnsearch?.data)) {
            list = xnsearch.data;
        } else if (Array.isArray(xnsearch?.data?.result)) {
            list = xnsearch.data.result;
        } else if (Array.isArray(xnsearch?.data?.results)) {
            list = xnsearch.data.results;
        }

        if (!xnsearch?.status || !list.length) {
            return reply("*❌ No results found!*\n_" + (xnsearch?.message || xnsearch?.error || "Empty response") + "_");
        }

        const sections = [{
            title: "🔞 XNXX Results",
            rows: list.slice(0, 15).map((v, i) => {
                const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
                const short = title.length > 45 ? title.slice(0, 42) + "..." : title;
                return {
                    title: `${i + 1}. ${short}`,
                    description: "XNXX",
                    rowId: `${prefix}xnxxvid ${v.url || v.link || ""}`
                };
            })
        }];

        const listMessage = {
            image: "https://files.catbox.moe/ave9xa.png",
            text: `*🔞 ${config.BOT_NAME} XNXX SEARCH*\n\n🔍 Query: *${q}*\n📊 Results: *${list.length}*\n\nSelect a video:`,
            footer: config.FOOTER,
            buttonText: "📥 Open Results",
            sections
        };

        await manaofc.listMessage(from, listMessage, mek);
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.log(e);
        reply("*❌ Error occurred!*");
    }
});

// ============================================
// XNXX DOWNLOAD
// ============================================
cmd({
    pattern: "xnxxvid",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("*Need a video url!*");

        await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });
        await reply("⏳ *Fetching video...*");

        const response = await fetch(
            "https://manaofc-api.vercel.app/xnxx/download?url=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const xndown = await response.json();
        const data = xndown?.data;

        if (!xndown?.status || !data) {
            return reply("*❌ Failed to fetch video!*\n_" + (xndown?.message || xndown?.error || "Empty response") + "_");
        }

        let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*🔞 XNXX DOWNLOAD*\n`;
        caption += `🎬 *Title:* ${data.title || "N/A"}\n`;
        caption += `⏱ *Duration:* ${data.duration || "N/A"}\n`;
        caption += `👀 *Views:* ${data.views || "N/A"}\n`;
        if (data.likes) caption += `👍 *Likes:* ${data.likes}\n`;
        if (data.rating) caption += `⭐ *Rating:* ${data.rating}\n`;
        caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

        if (data.thumbnail) {
            await manaofc.sendMessage(from, {
                image: { url: data.thumbnail },
                caption
            }, { quoted: mek });
        } else {
            await reply(caption);
        }

        const dl = data.dlink || data.downloadUrl || null;
        if (!dl) return reply("*❌ Download URL not available!*");

        await manaofc.sendMessage(from, {
            video: { url: dl },
            mimetype: "video/mp4",
            caption: `🔞 *${data.title || "XNXX"}*\n✅ ${config.BOT_NAME}`
        }, { quoted: mek });

        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.log(e);
        reply("*❌ Download failed!* (File may be too large)");
    }
});

// ============================================
// XVIDEOS SEARCH
// ============================================
cmd({
    pattern: "xvideo",
    alias: ["xvideos", "xv"],
    desc: "Search and download XVideos",
    use: ".xvideo <query>",
    react: "🔞",
    category: "download",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
        if (!q) return reply("❌ Please enter a search query!\n\nExample: `.xvideo query`");

        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

        const response = await fetch(
            "https://manaofc-api.vercel.app/xvideos/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const xvsearch = await response.json();

        let list = [];
        if (Array.isArray(xvsearch?.data)) {
            list = xvsearch.data;
        } else if (Array.isArray(xvsearch?.data?.result)) {
            list = xvsearch.data.result;
        } else if (Array.isArray(xvsearch?.data?.results)) {
            list = xvsearch.data.results;
        }

        if (!xvsearch?.status || !list.length) {
            return reply("*❌ No results found!*\n_" + (xvsearch?.message || xvsearch?.error || "Empty response") + "_");
        }

        const sections = [{
            title: "🔞 XVideos Results",
            rows: list.slice(0, 15).map((v, i) => {
                const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
                const short = title.length > 42 ? title.slice(0, 39) + "..." : title;
                const dur = v.duration ? ` • ${v.duration}` : "";
                return {
                    title: `${i + 1}. ${short}`,
                    description: `XVideos${dur}`,
                    rowId: `${prefix}xvdo ${v.url || v.link || ""}`
                };
            })
        }];

        const listMessage = {
            image: "https://files.catbox.moe/twrsw8.png",
            text: `*🔞 ${config.BOT_NAME} XVIDEOS SEARCH*\n\n🔍 Query: *${q}*\n📊 Results: *${list.length}*\n\nSelect a video:`,
            footer: config.FOOTER,
            buttonText: "📥 Open Results",
            sections
        };

        await manaofc.listMessage(from, listMessage, mek);
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.error("XVIDEO Search Error:", e);
        reply("*❌ Error occurred while searching!*");
    }
});

// ============================================
// XVIDEOS DOWNLOAD
// ============================================
cmd({
    pattern: "xvdo",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ Need a video URL!\n\nUse `.xvideo <query>` first.");

        await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });
        await reply("⬇️ *Downloading video...*");

        const response = await fetch(
            "https://manaofc-api.vercel.app/xvideos/download?url=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const xvdown = await response.json();
        const data = xvdown?.data;

        if (!xvdown?.status || !data) {
            return reply("*❌ Failed to fetch video details!*");
        }

        let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n`;
        caption += `*🔞 XVIDEOS DOWNLOAD*\n`;
        caption += `🎬 *Title:* ${data.title || "N/A"}\n`;
        caption += `👀 *Views:* ${data.views || "N/A"}\n`;
        caption += `⏱️ *Duration:* ${data.duration || "N/A"}\n`;
        caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

        if (data.thumbnail) {
            await manaofc.sendMessage(from, {
                image: { url: data.thumbnail },
                caption
            }, { quoted: mek });
        } else {
            await reply(caption);
        }

        const downloadUrl = data.dlink || data.downloadUrl || null;

        if (!downloadUrl || String(downloadUrl).includes("xvideos.com/video")) {
            return reply("*❌ Direct download URL not available!*");
        }

        await manaofc.sendMessage(from, {
            video: { url: downloadUrl },
            mimetype: "video/mp4",
            caption: `🔞 *${data.title || "XVideos"}*\n✅ ${config.BOT_NAME}`
        }, { quoted: mek });

        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.error("XVIDEO Download Error:", e);
        reply("*❌ Download failed! Please try again.*");
    }
});

// ============================================
// TANAFLIX SEARCH
// ============================================
cmd({
    pattern: "tanaflix",
    alias: ["tnaflix", "tnfx"],
    desc: "Search and download Tnaflix videos",
    use: ".tanaflix <query>",
    react: "🔞",
    category: "download",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
        if (!q) return reply("❌ Please enter a search query!\n\nExample: `.tanaflix query`");

        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

        const response = await fetch(
            "https://manaofc-api.vercel.app/tnaflix/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const txsearch = await response.json();

        let list = [];
        if (Array.isArray(txsearch?.data)) {
            list = txsearch.data;
        } else if (Array.isArray(txsearch?.data?.result)) {
            list = txsearch.data.result;
        } else if (Array.isArray(txsearch?.data?.results)) {
            list = txsearch.data.results;
        }

        if (!txsearch?.status || !list.length) {
            return reply("*❌ No results found!*\n_" + (txsearch?.message || txsearch?.error || "Empty response") + "_");
        }

        const sections = [{
            title: "🔞 Tanaflix Results",
            rows: list.slice(0, 15).map((v, i) => {
                const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
                const short = title.length > 42 ? title.slice(0, 39) + "..." : title;
                const dur = v.duration ? ` • ${v.duration}` : "";
                return {
                    title: `${i + 1}. ${short}`,
                    description: `Tanaflix${dur}`,
                    rowId: `${prefix}txd ${v.url || v.link || ""}`
                };
            })
        }];

        const listMessage = {
            image: "https://files.catbox.moe/gc7uis.png",
            text: `*🔞 ${config.BOT_NAME} TANAFLIX SEARCH*\n\n🔍 Query: *${q}*\n📊 Results: *${list.length}*\n\nSelect a video:`,
            footer: config.FOOTER,
            buttonText: "📥 Open Results",
            sections
        };

        await manaofc.listMessage(from, listMessage, mek);
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.error("TANAFLIX Search Error:", e);
        reply("*❌ Error occurred while searching!*");
    }
});

// ============================================
// TANAFLIX DOWNLOAD
// ============================================
cmd({
    pattern: "txd",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ Need a video URL!\n\nUse `.tanaflix <query>` first.");

        await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });
        await reply("⬇️ *Downloading video...*");

        const response = await fetch(
            "https://manaofc-api.vercel.app/tnaflix/download?url=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const txd = await response.json();
        const data = txd?.data;

        if (!txd?.status || !data) {
            return reply("*❌ Failed to fetch video details!*");
        }

        let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n`;
        caption += `*🔞 TANAFLIX DOWNLOAD*\n`;
        caption += `🎬 *Title:* ${data.title || "N/A"}\n`;
        caption += `👀 *Views:* ${data.views || "N/A"}\n`;
        caption += `⏱️ *Duration:* ${data.duration || "N/A"}\n`;
        caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

        if (data.thumbnail) {
            await manaofc.sendMessage(from, {
                image: { url: data.thumbnail },
                caption
            }, { quoted: mek });
        } else {
            await reply(caption);
        }

        let downloadUrl = data.dlink || data.downloadUrl || null;

        if (data.formats && Array.isArray(data.formats) && data.formats.length) {
            const sorted = data.formats.sort((a, b) => (b.height || 0) - (a.height || 0));
            downloadUrl = sorted[0].url || downloadUrl;
        }

        if (!downloadUrl) {
            return reply("*❌ Direct download URL not available!*");
        }

        await manaofc.sendMessage(from, {
            video: { url: downloadUrl },
            mimetype: "video/mp4",
            caption: `🔞 *${data.title || "Tanaflix"}*\n✅ ${config.BOT_NAME}`
        }, { quoted: mek });

        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.error("TANAFLIX Download Error:", e);
        reply("*❌ Download failed! Please try again.*");
    }
});

//=====================================
// ========== OWNER COMMANDS ==========
//=====================================
cmd({
    pattern: "vv",
    alias: ["decvv", "👀"],
    react: "🔓",
    desc: "Decrypt / open ViewOnce messages",
    category: "owner",
    use: ".vv (reply to a view-once msg)",
    filename: __filename
}, async (manaofc, mek, m, { from, reply, isOwner }) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        const ctx = mek.message?.extendedTextMessage?.contextInfo;
        const quotedMsg = ctx?.quotedMessage;
        if (!quotedMsg) {
            return reply("❌ *Reply to a ViewOnce message.*\nExample: reply a view-once photo → `.vv`");
        }

        // Unwrap viewOnce wrappers (V1 / V2 / Extension)
        const unwrap = (msg) => {
            if (!msg) return null;
            if (msg.viewOnceMessage?.message) return msg.viewOnceMessage.message;
            if (msg.viewOnceMessageV2?.message) return msg.viewOnceMessageV2.message;
            if (msg.viewOnceMessageV2Extension?.message) return msg.viewOnceMessageV2Extension.message;
            return msg;
        };

        const inner = unwrap(quotedMsg) || quotedMsg;
        const type = getContentType(inner);

        const downloadBuf = async (mediaMsg, mediaType) => {
            const stream = await downloadContentFromMessage(mediaMsg, mediaType);
            const chunks = [];
            for await (const chunk of stream) chunks.push(chunk);
            return Buffer.concat(chunks);
        };

        // Target: in groups send to owner DM privately; else same chat
        const botUserJid = jidNormalizedUser(manaofc.user.id);
        const sendTo = from.endsWith("@g.us") ? botUserJid : from;

        if (type === "imageMessage" || (inner.imageMessage && (inner.imageMessage.viewOnce || quotedMsg.viewOnceMessage || quotedMsg.viewOnceMessageV2))) {
            const img = inner.imageMessage || quotedMsg.imageMessage;
            if (!img) return reply("❌ *Not a ViewOnce image.*");
            const buffer = await downloadBuf(img, "image");
            const caption = img.caption || config.FOOTER || "";
            await manaofc.sendMessage(sendTo, {
                image: buffer,
                caption: `🔓 *ViewOnce unlocked*\n${caption}`
            }, { quoted: mek });
            if (from.endsWith("@g.us")) {
                await reply("✅ *ViewOnce image sent to your DM.*");
            }
            return;
        }

        if (type === "videoMessage" || (inner.videoMessage && (inner.videoMessage.viewOnce || quotedMsg.viewOnceMessage || quotedMsg.viewOnceMessageV2))) {
            const vid = inner.videoMessage || quotedMsg.videoMessage;
            if (!vid) return reply("❌ *Not a ViewOnce video.*");
            const buffer = await downloadBuf(vid, "video");
            const caption = vid.caption || config.FOOTER || "";
            await manaofc.sendMessage(sendTo, {
                video: buffer,
                caption: `🔓 *ViewOnce unlocked*\n${caption}`,
                mimetype: "video/mp4"
            }, { quoted: mek });
            if (from.endsWith("@g.us")) {
                await reply("✅ *ViewOnce video sent to your DM.*");
            }
            return;
        }

        if (type === "audioMessage" || (inner.audioMessage && (inner.audioMessage.viewOnce || quotedMsg.viewOnceMessage || quotedMsg.viewOnceMessageV2))) {
            const aud = inner.audioMessage || quotedMsg.audioMessage;
            if (!aud) return reply("❌ *Not a ViewOnce audio.*");
            const buffer = await downloadBuf(aud, "audio");
            await manaofc.sendMessage(sendTo, {
                audio: buffer,
                mimetype: aud.mimetype || "audio/mp4",
                ptt: aud.ptt || false
            }, { quoted: mek });
            if (from.endsWith("@g.us")) {
                await reply("✅ *ViewOnce audio sent to your DM.*");
            }
            return;
        }

        // Fallback: try any media on quoted
        if (inner.imageMessage) {
            const buffer = await downloadBuf(inner.imageMessage, "image");
            await manaofc.sendMessage(sendTo, {
                image: buffer,
                caption: inner.imageMessage.caption || "🔓 ViewOnce"
            }, { quoted: mek });
            return;
        }
        if (inner.videoMessage) {
            const buffer = await downloadBuf(inner.videoMessage, "video");
            await manaofc.sendMessage(sendTo, {
                video: buffer,
                caption: inner.videoMessage.caption || "🔓 ViewOnce"
            }, { quoted: mek });
            return;
        }

        return reply("❌ *This is not a ViewOnce message (image/video/audio).*");
    } catch (e) {
        console.error("vv error:", e);
        reply("❌ *Failed to open ViewOnce:* " + (e.message || ""));
    }
});

// 3. BROADCAST MESSAGE
cmd({
    pattern: "broadcast",
    react: "📢",
    alias: ["bc", "cast"],
    desc: "Broadcast message to all chats",
    category: "owner",
    use: ".broadcast <message>",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, q}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!q) return reply("❌ *Provide a message to broadcast!*");

        const chats = await manaofc.groupFetchAllParticipating();
        const groups = Object.values(chats);

        let count = 0;
        for (let group of groups) {
            await manaofc.sendMessage(group.id, { text: `*📢 BROADCAST*

${q}` });
            count++;
            await delay(500);
        }

        reply(`✅ *Broadcast sent to ${count} groups!*`);

    } catch (e) {
        console.error(e);
        reply("❌ *Broadcast failed!*");
    }
});

// 4. LEAVE GROUP
cmd({
    pattern: "leave",
    react: "👋",
    desc: "Leave current group",
    category: "owner",
    use: ".leave",
    filename: __filename
},
async (manaofc, mek, m, { from, isGroup, isOwner, reply}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!isGroup) return reply("❌ *This is not a group!*");

        await reply("👋 *Leaving group...*");
        await delay(1000);
        await manaofc.groupLeave(from);

    } catch (e) {
        console.error(e);
        reply("❌ *Error!*");
    }
});

// 5. BLOCK USER
cmd({
    pattern: "block",
    react: "🚫",
    desc: "Block a user",
    category: "owner",
    use: ".block @user or reply",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        let users = mek.mentionedJid ? mek.mentionedJid[0] : (mek.quoted ? mek.quoted.sender : null);
        if (!users) return reply("❌ *Mention or reply to a user!*");

        await manaofc.updateBlockStatus(users, "block");
        reply(`🚫 *Blocked @${users.split('@')[0]}*`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to block user!*");
    }
});

// 6. UNBLOCK USER
cmd({
    pattern: "unblock",
    react: "✅",
    desc: "Unblock a user",
    category: "owner",
    use: ".unblock @user or reply",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");

        let users = mek.mentionedJid ? mek.mentionedJid[0] : (mek.quoted ? mek.quoted.sender : null);
        if (!users) return reply("❌ *Mention or reply to a user!*");

        await manaofc.updateBlockStatus(users, "unblock");
        reply(`✅ *Unblocked @${users.split('@')[0]}*`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to unblock user!*");
    }
});

// 7. SET BOT BIO/ABOUT
cmd({
    pattern: "setbio",
    react: "📝",
    desc: "Set bot status/bio",
    category: "owner",
    use: ".setbio <text>",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, q}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!q) return reply("❌ *Provide a bio text!*");

        await manaofc.updateProfileStatus(q);
        reply(`✅ *Bio updated to:* ${q}`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to update bio!*");
    }
});

// 8. SET BOT NAME
cmd({
    pattern: "setname",
    react: "✏️",
    desc: "Set bot profile name",
    category: "owner",
    use: ".setname <name>",
    filename: __filename
},
async (manaofc, mek, m, { from, isOwner, reply, q}) => {
    try {
        if (!isOwner) return reply("❌ *Only owner can use this!*");
        if (!q) return reply("❌ *Provide a name!*");

        await manaofc.updateProfileName(q);
        reply(`✅ *Profile name updated to:* ${q}`);

    } catch (e) {
        console.error(e);
        reply("❌ *Failed to update name!*");
    }
});


// ===============================================
//==========  SEARCH COMMMAND =================
// ===============================================
const isUrl = (url) => {
    return url.match(
        new RegExp(
            /https?:\/\/(www\.)?[-a-zA-Z0-9@:%.+~#=]{1,256}\.[a-zA-Z0-9()]{1,6}\b([-a-zA-Z0-9()@:%+.~#?&/=]*)/,
            'gi'
        )
    )
}

function ytreg(url) {
    const ytIdRegex = /(?:http(?:s|):\/\/|)(?:(?:www\.|)youtube(?:\-nocookie|)\.com\/(?:watch\?.*(?:|\&)v=|embed|shorts\/|v\/)|youtu\.be\/)([-_0-9A-Za-z]{11})/
    return ytIdRegex.test(url);
}

cmd({
    pattern: "yts",
    alias: ["y"],
    use: '.yts lelena',
    react: "🔎",
    desc: "Search Youtube Songs or Videos.",
    category: "search",
    filename: __filename
},
async(manaofc, mek, m, {from, q, reply}) => {
    try {
        if (!q) return await reply("❌ *Please provide a search query!*\n\n*Example:* `.yts lelena`")
        if(isUrl(q) && !ytreg(q)) return await reply("❌ *Invalid YouTube URL!*")
        
        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });
        
        const arama = await yts(q);
        
        if (!arama || !arama.all || arama.all.length === 0) {
            return await reply("❌ *No results found!*")
        }
        
        let mesaj = `*🔎 ${config.BOT_NAME} YOUTUBE SEARCH*\n\n`;
        
        arama.all.slice(0, 10).forEach((video) => {
            mesaj += `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n`;
            mesaj += `*╎◈ Title :* ${video.title}\n`;
            mesaj += `*╎🔗 Link :* ${video.url}\n`;
            mesaj += `*╎⏱️ Duration :* ${video.timestamp || 'N/A'}\n`;
            mesaj += `*╎👀 Views :* ${video.views || 'N/A'}\n`;
            mesaj += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n`;
        });
        
        mesaj += `${config.FOOTER}`;
        
        await manaofc.sendMessage(from, { text: mesaj }, { quoted: mek });
        
    } catch (e) {
        console.log(e);
        reply('*Error !!*')
    }
});

cmd({
    pattern: "google",
    alias: ["gsearch", "search"],
    react: "🔍",
    desc: "Search Google (DuckDuckGo)",
    category: "search",
    use: ".google <query>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.google Node.js tutorial`");
        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });
        const res = await fetch("https://api.duckduckgo.com/?q=" + encodeURIComponent(q) + "&format=json&no_html=1&skip_disambig=1");
        const data = await res.json();
        let text = `🔍 *Google Search*\n📝 ${q}\n\n`;
        if (data.AbstractText) {
            text += `*Summary:*\n${data.AbstractText}\n\n`;
            if (data.AbstractURL) text += `🔗 ${data.AbstractURL}\n\n`;
        }
        const topics = (data.RelatedTopics || []).filter(t => t.Text && t.FirstURL).slice(0, 6);
        if (topics.length) {
            text += `*Related:*\n`;
            topics.forEach((t, i) => {
                text += `*${i + 1}.* ${t.Text.slice(0, 100)}\n${t.FirstURL}\n\n`;
            });
        }
        if (!data.AbstractText && !topics.length) {
            text += `_No instant answer. Try a more specific query._\n🔗 https://duckduckgo.com/?q=${encodeURIComponent(q)}\n`;
        }
        text += `\n${config.FOOTER}`;
        await reply(text);
    } catch (e) {
        reply("❌ *Search failed!*");
    }
});

cmd({
    pattern: "img",
    alias: ["image", "gimage"],
    react: "🖼️",
    desc: "Search images",
    category: "search",
    use: ".img <query>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.img cute cats`");
        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });
        // Use pollinations as visual search fallback + duckduckgo abstract image
        const res = await fetch("https://api.duckduckgo.com/?q=" + encodeURIComponent(q) + "&format=json&no_html=1");
        const data = await res.json();
        const imgs = [];
        if (data.Image) imgs.push("https://duckduckgo.com" + data.Image);
        (data.RelatedTopics || []).forEach(t => {
            if (t.Icon && t.Icon.URL) imgs.push(t.Icon.URL.startsWith("http") ? t.Icon.URL : "https://duckduckgo.com" + t.Icon.URL);
        });
        if (!imgs.length) {
            // AI image as fallback for visual query
            const url = `https://image.pollinations.ai/prompt/${encodeURIComponent(q)}?width=768&height=768&nologo=true`;
            await manaofc.sendMessage(from, { image: { url }, caption: `🖼️ *${q}*\n_(AI visual)_\n\n${config.FOOTER}` }, { quoted: mek });
            return;
        }
        for (const u of imgs.slice(0, 4)) {
            try {
                await manaofc.sendMessage(from, { image: { url: u }, caption: config.FOOTER }, { quoted: mek });
            } catch (_) {}
        }
    } catch (e) {
        reply("❌ *Image search failed!*");
    }
});

cmd({
    pattern: "lyrics",
    alias: ["lyric", "songlyrics"],
    react: "🎤",
    desc: "Get song lyrics",
    category: "search",
    use: ".lyrics <song name>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.lyrics perfect ed sheeran`");
        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });
        // lyrics.ovh
        const parts = q.trim().split(/ +/);
        let url;
        if (parts.length >= 2) {
            url = `https://api.lyrics.ovh/v1/${encodeURIComponent(parts[0])}/${encodeURIComponent(parts.slice(1).join(" "))}`;
        } else {
            url = `https://api.lyrics.ovh/v1/${encodeURIComponent(q)}/${encodeURIComponent(q)}`;
        }
        let lyrics = null, title = q;
        try {
            const res = await fetch(url);
            const data = await res.json();
            if (data.lyrics) lyrics = data.lyrics;
        } catch (_) {}
        if (!lyrics) {
            // try some-random-api
            try {
                const res2 = await fetch("https://some-random-api.com/lyrics?title=" + encodeURIComponent(q));
                const d2 = await res2.json();
                if (d2.lyrics) {
                    lyrics = d2.lyrics;
                    title = d2.title || q;
                }
            } catch (_) {}
        }
        if (!lyrics) return reply("❌ *Lyrics not found!*");
        const cut = lyrics.length > 3500 ? lyrics.slice(0, 3500) + "\n\n_...truncated_" : lyrics;
        await reply(`🎤 *Lyrics — ${title}*\n\n${cut}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Lyrics fetch failed!*");
    }
});

cmd({
    pattern: "npm",
    alias: ["npmsearch"],
    react: "📦",
    desc: "Search npm packages",
    category: "search",
    use: ".npm baileys",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.npm express`");
        const res = await fetch("https://registry.npmjs.org/-/v1/search?text=" + encodeURIComponent(q) + "&size=5");
        const data = await res.json();
        if (!data.objects?.length) return reply("❌ *No packages found!*");
        let text = `📦 *NPM Search — ${q}*\n\n`;
        data.objects.forEach((o, i) => {
            const p = o.package;
            text += `*${i + 1}. ${p.name}* v${p.version}\n${(p.description || "").slice(0, 80)}\n🔗 ${p.links?.npm || ""}\n\n`;
        });
        text += config.FOOTER;
        await reply(text);
    } catch (e) {
        reply("❌ *NPM search failed!*");
    }
});
// ============================================
// CONVERT COMMANDS
// ============================================


cmd({
    pattern: 'sticker',
    alias: ['s', 'stic'],
    react: '🖼️',
    desc: 'Image/video → sticker (reply to media)',
    category: 'convert',
    use: '.sticker [Pack|Author]',
    filename: __filename
  }, async (manaofc, mek, m, { from, q, reply }) => {
    try {
      const got = await downloadQuotedMedia(manaofc, mek);
      if (!got) return reply('❌ *Reply to an image or short video.*\nExample: `.sticker MyPack|Me`');

      if (got.type === 'videoMessage' && (got.media.seconds || 0) > 20) {
        return reply('❌ Video must be under *20 seconds*.');
      }

      const { pack, author } = getPackAuthor(q, config);
      const sticker = new Sticker(got.buffer, {
        pack,
        author,
        type: StickerTypes.FULL,
        quality: got.type === 'videoMessage' ? 50 : 80
      });
      await manaofc.sendMessage(from, { sticker: await sticker.toBuffer() }, { quoted: mek });
    } catch (e) {
      console.error('sticker error:', e);
      reply('❌ Failed to create sticker.\n' + (e.message || ''));
    }
  });

  cmd({
    pattern: 'steal',
    alias: ['take', 'sname'],
    react: '✏️',
    desc: 'Change sticker pack/author name',
    category: 'convert',
    use: '.steal Pack|Author (reply sticker)',
    filename: __filename
  }, async (manaofc, mek, m, { from, q, reply }) => {
    try {
      const got = await downloadQuotedMedia(manaofc, mek);
      if (!got || got.type !== 'stickerMessage') {
        return reply('❌ *Reply to a sticker.*\nExample: `.steal NewPack|Author`');
      }
      const { pack, author } = getPackAuthor(q, config);
      const sticker = new Sticker(got.buffer, {
        pack, author, type: StickerTypes.FULL, quality: 80
      });
      await manaofc.sendMessage(from, { sticker: await sticker.toBuffer() }, { quoted: mek });
    } catch (e) {
      console.error('steal error:', e);
      reply('❌ Failed to steal sticker.');
    }
  });

  cmd({
    pattern: 'emomix',
    alias: ['emix', 'emojimix'],
    react: '😄',
    desc: 'Mix two emojis into a sticker',
    category: 'convert',
    use: '.emomix 🙂+😂',
    filename: __filename
  }, async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q || !q.includes('+')) return reply('❌ Example: `.emomix 🙂+😂`');
      const [e1, e2] = q.replace(/\s/g, '').split('+');
      if (!e1 || !e2) return reply('❌ Need two emojis: `.emomix 🔥+😎`');
      const url = `https://tenor.googleapis.com/v2/featured?key=AIzaSyAyimkuYQYF_FXVALexPuGQctUWRURdCYQ&contentfilter=high&media_filter=png_transparent&component=proactive&collection=emoji_kitchen_v5&q=${encodeURIComponent(e1)}_${encodeURIComponent(e2)}`;
      const axios = require('axios');
      const { data } = await axios.get(url);
      const img = data?.results?.[0]?.url;
      if (!img) return reply('❌ Could not mix those emojis.');
      const res = await axios.get(img, { responseType: 'arraybuffer' });
      const { pack, author } = getPackAuthor(null, config);
      const sticker = new Sticker(Buffer.from(res.data), {
        pack, author, type: StickerTypes.FULL, quality: 80
      });
      await manaofc.sendMessage(from, { sticker: await sticker.toBuffer() }, { quoted: mek });
    } catch (e) {
      console.error('emomix error:', e);
      reply('❌ Emoji mix failed.');
    }
  });

  cmd({
    pattern: 'searchsticker',
    alias: ['ssticker', 'findsticker'],
    react: '🔍',
    desc: 'Search stickers online',
    category: 'convert',
    use: '.searchsticker cat',
    filename: __filename
  }, async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply('❌ Example: `.searchsticker cat`');
      const axios = require('axios');
      // simple giphy/tenor-style search via public sticker API fallback
      const term = q.split(',')[0].trim();
      const count = Math.min(parseInt(q.split(',')[1]) || 5, 10);
      const { data } = await axios.get(
        `https://api.otakugifs.xyz/gif?reaction=${encodeURIComponent(term)}`
      ).catch(() => ({ data: null }));

      // fallback: use wa sticker packs search is complex; use emoji kitchen style
      if (!data || !data.url) {
        return reply('❌ No stickers found for: ' + term + '\nTry: `.sticker` with an image instead.');
      }
      const res = await axios.get(data.url, { responseType: 'arraybuffer' });
      const { pack, author } = getPackAuthor(null, config);
      const sticker = new Sticker(Buffer.from(res.data), {
        pack, author, type: StickerTypes.FULL, quality: 70
      });
      await manaofc.sendMessage(from, { sticker: await sticker.toBuffer() }, { quoted: mek });
    } catch (e) {
      console.error('searchsticker error:', e);
      reply('❌ Sticker search failed. Use `.sticker` with an image.');
    }
  });

  
cmd({
    pattern: "fancy",
    alias: ["style", "font"],
    react: "✨",
    desc: "Convert text to fancy styles",
    category: "convert",
    use: ".fancy <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.fancy MANAOFC`");
        const styles = [
            (t) => t.split("").map(c => {
                const map = {"a":"ⓐ","b":"ⓑ","c":"ⓒ","d":"ⓓ","e":"ⓔ","f":"ⓕ","g":"ⓖ","h":"ⓗ","i":"ⓘ","j":"ⓙ","k":"ⓚ","l":"ⓛ","m":"ⓜ","n":"ⓝ","o":"ⓞ","p":"ⓟ","q":"ⓠ","r":"ⓡ","s":"ⓢ","t":"ⓣ","u":"ⓤ","v":"ⓥ","w":"ⓦ","x":"ⓧ","y":"ⓨ","z":"ⓩ","A":"Ⓐ","B":"Ⓑ","C":"Ⓒ","D":"Ⓓ","E":"Ⓔ","F":"Ⓕ","G":"Ⓖ","H":"Ⓗ","I":"Ⓘ","J":"Ⓙ","K":"Ⓚ","L":"Ⓛ","M":"Ⓜ","N":"Ⓝ","O":"Ⓞ","P":"Ⓟ","Q":"Ⓠ","R":"Ⓡ","S":"Ⓢ","T":"Ⓣ","U":"Ⓤ","V":"Ⓥ","W":"Ⓦ","X":"Ⓧ","Y":"Ⓨ","Z":"Ⓩ"};
                return map[c] || c;
            }).join(""),
            (t) => t.split("").map(c => {
                const o = c.charCodeAt(0);
                if (o >= 65 && o <= 90) return String.fromCodePoint(0x1D400 + (o - 65));
                if (o >= 97 && o <= 122) return String.fromCodePoint(0x1D41A + (o - 97));
                return c;
            }).join(""),
            (t) => t.split("").map(c => {
                const o = c.charCodeAt(0);
                if (o >= 65 && o <= 90) return String.fromCodePoint(0x1D5D4 + (o - 65));
                if (o >= 97 && o <= 122) return String.fromCodePoint(0x1D5EE + (o - 97));
                return c;
            }).join(""),
            (t) => t.split("").join(" "),
        ];
        const out = styles.map((fn, i) => `*${i + 1}.* ${fn(q)}`).join("\n");
        await reply(`✨ *Fancy Text*\n\n${out}\n\n${config.FOOTER}`);
    } catch (e) {
        console.log(e);
        reply("❌ *Fancy failed!*");
    }
});

cmd({
    pattern: "toimg",
    alias: ["toimage"],
    react: "🖼️",
    desc: "Convert sticker to image (reply to sticker)",
    category: "convert",
    use: ".toimg (reply sticker)",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        const sticker = quoted?.stickerMessage;
        if (!sticker) return reply("❌ *Reply to a sticker!*");
        const buffer = await downloadContentFromMessage(sticker, "sticker");
        let chunks = [];
        for await (const chunk of buffer) chunks.push(chunk);
        await manaofc.sendMessage(from, {
            image: Buffer.concat(chunks),
            caption: `🖼️ *Sticker → Image*\n${config.FOOTER}`
        }, { quoted: mek });
    } catch (e) {
        console.log(e);
        reply("❌ *Conversion failed!*");
    }
});

cmd({
    pattern: "tomp3",
    alias: ["toaudio"],
    react: "🎵",
    desc: "Convert video to audio (reply to video)",
    category: "convert",
    use: ".tomp3 (reply video)",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const quoted = mek.message?.extendedTextMessage?.contextInfo?.quotedMessage;
        const video = quoted?.videoMessage;
        if (!video) return reply("❌ *Reply to a video!*");
        await reply("⏳ *Converting...*");
        const buffer = await downloadContentFromMessage(video, "video");
        let chunks = [];
        for await (const chunk of buffer) chunks.push(chunk);
        // Send as audio document (raw video buffer as audio may not always work without ffmpeg)
        await manaofc.sendMessage(from, {
            audio: Buffer.concat(chunks),
            mimetype: "audio/mp4",
            ptt: false
        }, { quoted: mek });
    } catch (e) {
        console.log(e);
        reply("❌ *Conversion failed! (server may need ffmpeg)*");
    }
});

cmd({
    pattern: 'img2url',
    alias: ['toururl', 'tour'],
    react: '☁️',
    desc: 'Upload replied image to get URL',
    category: 'convert',
    use: '.img2url (reply image)',
    filename: __filename
  }, async (manaofc, mek, m, { from, reply }) => {
    try {
      const ctx = mek.message?.extendedTextMessage?.contextInfo;
      const quoted = ctx?.quotedMessage;
      if (!quoted) return reply('❌ Reply to an image.');
      const type = getContentType(quoted);
      if (type !== 'imageMessage') return reply('❌ Reply to an *image*.');
      const stream = await downloadContentFromMessage(quoted.imageMessage, 'image');
      const chunks = [];
      for await (const c of stream) chunks.push(c);
      const buf = Buffer.concat(chunks);
      const FormData = require('form-data');
      const form = new FormData();
      form.append('fileToUpload', buf, { filename: 'image.jpg', contentType: 'image/jpeg' });
      form.append('reqtype', 'fileupload');
      const res = await axios.post('https://catbox.moe/user/api.php', form, {
        headers: form.getHeaders()
      });
      const url = typeof res.data === 'string' ? res.data.trim() : '';
      if (!url.startsWith('http')) return reply('❌ Upload failed.');
      reply(`☁️ *Image URL*\n\n${url}`);
    } catch (e) {
      console.error(e);
      reply('❌ img2url failed. Is form-data installed?');
    }
  });

cmd({
    pattern: "base64",
    alias: ["b64"],
    react: "🔐",
    desc: "Encode/decode Base64",
    category: "convert",
    use: ".base64 encode|decode <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.base64 encode hello` or `.base64 decode aGVsbG8=`");
        const args = q.trim().split(/ +/);
        const mode = args[0].toLowerCase();
        const text = args.slice(1).join(" ");
        if (!text) return reply("❌ *Provide text!*");
        if (mode === "encode" || mode === "enc") {
            await reply(`🔐 *Base64 Encode*\n\n\`\`\`${Buffer.from(text).toString("base64")}\`\`\`\n\n${config.FOOTER}`);
        } else if (mode === "decode" || mode === "dec") {
            await reply(`🔓 *Base64 Decode*\n\n\`\`\`${Buffer.from(text, "base64").toString("utf8")}\`\`\`\n\n${config.FOOTER}`);
        } else {
            reply("❌ *Use encode or decode!*");
        }
    } catch (e) {
        reply("❌ *Base64 failed!*");
    }
});

cmd({
    pattern: "hash",
    alias: ["md5", "sha256"],
    react: "🔏",
    desc: "Hash text (md5/sha256)",
    category: "convert",
    use: ".hash sha256 hello",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.hash md5 text` or `.hash sha256 text`");
        const args = q.trim().split(/ +/);
        let algo = "sha256";
        let text = q;
        if (["md5", "sha1", "sha256", "sha512"].includes(args[0].toLowerCase())) {
            algo = args[0].toLowerCase();
            text = args.slice(1).join(" ");
        }
        if (!text) return reply("❌ *Provide text!*");
        const h = crypto.createHash(algo).update(text).digest("hex");
        await reply(`🔏 *${algo.toUpperCase()}*\n\n\`\`\`${h}\`\`\`\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Hash failed!*");
    }
});

cmd({
    pattern: "reverse",
    react: "🔄",
    desc: "Reverse text",
    category: "convert",
    use: ".reverse <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Provide text!*");
    await reply(`🔄 *Reversed*\n\n${q.split("").reverse().join("")}\n\n${config.FOOTER}`);
});

cmd({
    pattern: "binary",
    alias: ["bin"],
    react: "0️⃣",
    desc: "Text ↔ Binary",
    category: "convert",
    use: ".binary encode|decode <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.binary encode hi` / `.binary decode 1101000...`");
        const args = q.trim().split(/ +/);
        const mode = args[0].toLowerCase();
        const text = args.slice(1).join(" ");
        if (!text) return reply("❌ *Provide data!*");
        if (mode === "encode" || mode === "enc") {
            const bin = text.split("").map(c => c.charCodeAt(0).toString(2).padStart(8, "0")).join(" ");
            await reply(`0️⃣ *Binary Encode*\n\n\`\`\`${bin}\`\`\`\n\n${config.FOOTER}`);
        } else {
            const str = text.trim().split(/\s+/).map(b => String.fromCharCode(parseInt(b, 2))).join("");
            await reply(`1️⃣ *Binary Decode*\n\n\`\`\`${str}\`\`\`\n\n${config.FOOTER}`);
        }
    } catch (e) {
        reply("❌ *Binary convert failed!*");
    }
});

cmd({
    pattern: "morse",
    react: "📡",
    desc: "Text ↔ Morse code",
    category: "convert",
    use: ".morse encode|decode <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    const map = {A:".-",B:"-...",C:"-.-.",D:"-..",E:".",F:"..-.",G:"--.",H:"....",I:"..",J:".---",K:"-.-",L:".-..",M:"--",N:"-.",O:"---",P:".--.",Q:"--.-",R:".-.",S:"...",T:"-",U:"..-",V:"...-",W:".--",X:"-..-",Y:"-.--",Z:"--..","0":"-----","1":".----","2":"..---","3":"...--","4":"....-","5":".....","6":"-....","7":"--...","8":"---..","9":"----."," ":"/"};
    const rev = Object.fromEntries(Object.entries(map).map(([k,v]) => [v, k]));
    if (!q) return reply("❌ *Usage:* `.morse encode hello` / `.morse decode .... . .-.. .-.. ---`");
    const args = q.trim().split(/ +/);
    const mode = args[0].toLowerCase();
    const text = args.slice(1).join(" ");
    if (!text) return reply("❌ *Provide text!*");
    if (mode === "encode" || mode === "enc") {
        const out = text.toUpperCase().split("").map(c => map[c] || c).join(" ");
        await reply(`📡 *Morse Encode*\n\n\`\`\`${out}\`\`\`\n\n${config.FOOTER}`);
    } else {
        const out = text.trim().split(/\s+/).map(c => rev[c] || c).join("");
        await reply(`📡 *Morse Decode*\n\n\`\`\`${out}\`\`\`\n\n${config.FOOTER}`);
    }
});

cmd({
    pattern: "ascii",
    react: "🔠",
    desc: "Text to simple ASCII art style",
    category: "convert",
    use: ".ascii <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Provide text!*");
    const t = q.slice(0, 20);
    await reply("```\n" + t.split("").join(" ") + "\n" + "─".repeat(Math.min(t.length * 2, 40)) + "\n```\n" + config.FOOTER);
});
// ============================================
// TOOLS COMMANDS
// ============================================

cmd({
    pattern: "translate",
    alias: ["tr", "trans"],
    react: "🌐",
    desc: "Translate text to another language",
    category: "tools",
    use: ".translate <lang> <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.translate si Hello world`\nLang codes: si, en, ta, hi, es, fr...");
        const args = q.trim().split(/ +/);
        const lang = args[0];
        const text = args.slice(1).join(" ");
        if (!text) return reply("❌ *Provide text to translate!*");
        const res = await fetch(`https://api.mymemory.translated.net/get?q=${encodeURIComponent(text)}&langpair=auto|${encodeURIComponent(lang)}`);
        const data = await res.json();
        const translated = data?.responseData?.translatedText;
        if (!translated) return reply("❌ *Translation failed!*");
        await reply(`🌐 *Translate*\n\n📝 *Original:* ${text}\n✅ *Result (${lang}):* ${translated}\n\n${config.FOOTER}`);
    } catch (e) {
        console.log(e);
        reply("❌ *Translate error!*");
    }
});

cmd({
    pattern: "weather",
    alias: ["wth"],
    react: "🌤️",
    desc: "Get weather info for a city",
    category: "tools",
    use: ".weather <city>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.weather Colombo`");
        const res = await fetch(`https://wttr.in/${encodeURIComponent(q)}?format=j1`);
        const data = await res.json();
        const cur = data.current_condition?.[0];
        const area = data.nearest_area?.[0];
        if (!cur) return reply("❌ *City not found!*");
        const text = `🌤️ *Weather — ${area?.areaName?.[0]?.value || q}*\n\n` +
            `🌡️ Temp: ${cur.temp_C}°C (feels ${cur.FeelsLikeC}°C)\n` +
            `☁️ ${cur.weatherDesc?.[0]?.value || ""}\n` +
            `💧 Humidity: ${cur.humidity}%\n` +
            `💨 Wind: ${cur.windspeedKmph} km/h\n\n${config.FOOTER}`;
        await reply(text);
    } catch (e) {
        console.log(e);
        reply("❌ *Weather fetch failed!*");
    }
});

cmd({
    pattern: "github",
    alias: ["gh", "git"],
    react: "🐙",
    desc: "Get GitHub user info",
    category: "tools",
    use: ".github <username>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.github torvalds`");
        const res = await fetch("https://api.github.com/users/" + encodeURIComponent(q.trim()));
        if (!res.ok) return reply("❌ *User not found!*");
        const u = await res.json();
        const text = `🐙 *GitHub — ${u.login}*\n\n` +
            `👤 Name: ${u.name || "N/A"}\n` +
            `📝 Bio: ${u.bio || "N/A"}\n` +
            `📦 Repos: ${u.public_repos}\n` +
            `👥 Followers: ${u.followers} | Following: ${u.following}\n` +
            `🔗 ${u.html_url}\n\n${config.FOOTER}`;
        if (u.avatar_url) {
            await manaofc.sendMessage(from, { image: { url: u.avatar_url }, caption: text }, { quoted: mek });
        } else {
            await reply(text);
        }
    } catch (e) {
        console.log(e);
        reply("❌ *GitHub fetch failed!*");
    }
});

cmd({
    pattern: "qr",
    react: "📱",
    desc: "Generate QR code from text/URL",
    category: "tools",
    use: ".qr <text or url>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.qr https://example.com`");
        const url = `https://api.qrserver.com/v1/create-qr-code/?size=500x500&data=${encodeURIComponent(q)}`;
        await manaofc.sendMessage(from, {
            image: { url },
            caption: `📱 *QR Code*\n\n${q}\n\n${config.FOOTER}`
        }, { quoted: mek });
    } catch (e) {
        console.log(e);
        reply("❌ *QR generation failed!*");
    }
});

cmd({
    pattern: "shorturl",
    alias: ["short", "tinyurl"],
    react: "🔗",
    desc: "Shorten a long URL",
    category: "tools",
    use: ".shorturl <url>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.shorturl https://example.com/long...`");
        const res = await fetch("https://tinyurl.com/api-create.php?url=" + encodeURIComponent(q.trim()));
        const short = await res.text();
        if (!short.startsWith("http")) return reply("❌ *Failed to shorten URL!*");
        await reply(`🔗 *URL Shortener*\n\n📎 Original: ${q}\n✅ Short: ${short}\n\n${config.FOOTER}`);
    } catch (e) {
        console.log(e);
        reply("❌ *Shorten failed!*");
    }
});

cmd({
    pattern: "ip",
    react: "🌍",
    desc: "Lookup IP address info",
    category: "tools",
    use: ".ip <ip address>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Usage:* `.ip 8.8.8.8`");
        const res = await fetch(`http://ip-api.com/json/${encodeURIComponent(q.trim())}?fields=status,message,country,regionName,city,isp,org,as,query`);
        const d = await res.json();
        if (d.status !== "success") return reply("❌ *" + (d.message || "Lookup failed") + "*");
        await reply(`🌍 *IP Lookup*\n\n🔎 IP: ${d.query}\n🏳️ Country: ${d.country}\n📍 Region: ${d.regionName}\n🏙️ City: ${d.city}\n🏢 ISP: ${d.isp}\n📡 Org: ${d.org}\n\n${config.FOOTER}`);
    } catch (e) {
        console.log(e);
        reply("❌ *IP lookup failed!*");
    }
});

  cmd({
    pattern: 'wame',
    alias: ['wa'],
    react: '📱',
    desc: 'Create wa.me link',
    category: 'tools',
    use: '.wame 9477xxxxxxx',
    filename: __filename
  }, async (manaofc, mek, m, { from, q, reply, senderNumber }) => {
    const num = (q || String(senderNumber || '')).replace(/[^0-9]/g, '');
    if (!num) return reply('❌ Give a number: `.wame 94771234567`');
    reply(`📱 *WhatsApp Link*\n\nhttps://wa.me/${num}`);
  });

  cmd({
    pattern: 'id',
    alias: ['jid'],
    react: '🆔',
    desc: 'Show chat / user JID',
    category: 'tools',
    use: '.id',
    filename: __filename
  }, async (manaofc, mek, m, { from, reply, sender }) => {
    reply(`🆔 *JID Info*\n\n*Chat:* ${from}\n*Sender:* ${sender || mek.key.participant || mek.key.remoteJid}`);
  });

  cmd({
    pattern: "define",
    alias: ["dict", "dictionary"],
    react: "📖",
    desc: "Dictionary definition",
    category: "tools",
    use: ".define <word>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply}) => {
    try {
        if (!q) return reply("❌ *Example:* `.define hello`");
        const res = await fetch("https://api.dictionaryapi.dev/api/v2/entries/en/" + encodeURIComponent(q.trim()));
        if (!res.ok) return reply("❌ *Word not found!*");
        const arr = await res.json();
        const entry = arr[0];
        const phonetic = entry.phonetic || (entry.phonetics && entry.phonetics[0] && entry.phonetics[0].text) || "";
        let text = `📖 *${entry.word}* ${phonetic}\n\n`;
        for (const m of (entry.meanings || []).slice(0, 3)) {
            text += `*${m.partOfSpeech}*\n`;
            for (const d of (m.definitions || []).slice(0, 2)) {
                text += `• ${d.definition}\n`;
                if (d.example) text += `  _Ex: ${d.example}_\n`;
            }
            text += "\n";
        }
        text += config.FOOTER;
        await reply(text);
    } catch (e) {
        reply("❌ *Dictionary error!*");
    }
});

cmd({
    pattern: "wiki",
    alias: ["wikipedia"],
    react: "📚",
    desc: "Wikipedia summary",
    category: "tools",
    use: ".wiki <topic>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply}) => {
    try {
        if (!q) return reply("❌ *Example:* `.wiki Sri Lanka`");
        const res = await fetch("https://en.wikipedia.org/api/rest_v1/page/summary/" + encodeURIComponent(q.trim()));
        if (!res.ok) return reply("❌ *Page not found!*");
        const d = await res.json();
        const extract = (d.extract || "No summary.").slice(0, 900);
        const caption = `📚 *${d.title}*\n\n${extract}\n\n🔗 ${d.content_urls?.desktop?.page || ""}\n\n${config.FOOTER}`;
        if (d.thumbnail?.source) {
            await manaofc.sendMessage(from, { image: { url: d.thumbnail.source }, caption }, { quoted: mek });
        } else {
            await reply(caption);
        }
    } catch (e) {
        reply("❌ *Wiki fetch failed!*");
    }
});

cmd({
    pattern: "calc",
    alias: ["calculate", "math"],
    react: "🧮",
    desc: "Calculate math expression",
    category: "tools",
    use: ".calc 2+2*5",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply}) => {
    try {
        if (!q) return reply("❌ *Example:* `.calc 25*4+10`");
        // safe-ish: only allow numbers and math operators
        if (!/^[0-9+\-*/().%\s^]+$/.test(q)) {
            return reply("❌ *Only numbers and + - * / ( ) % allowed!*");
        }
        const res = await fetch("https://api.mathjs.org/v4/?expr=" + encodeURIComponent(q.replace(/\^/g, "**")));
        const result = await res.text();
        if (result.toLowerCase().includes("error")) return reply("❌ *Invalid expression!*");
        await reply(`🧮 *Calculator*\n\n📝 ${q}\n✅ = *${result}*\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Calc failed!*");
    }
});



cmd({
    pattern: "news",
    react: "📰",
    desc: "Latest tech headlines (HN)",
    category: "tools",
    use: ".news",
    filename: __filename
}, async (manaofc, mek, m, { from, reply}) => {
    try {
        const res = await fetch("https://hacker-news.firebaseio.com/v0/topstories.json");
        const ids = (await res.json()).slice(0, 8);
        let text = `📰 *Top Headlines*\n\n`;
        for (let i = 0; i < ids.length; i++) {
            const item = await (await fetch(`https://hacker-news.firebaseio.com/v0/item/${ids[i]}.json`)).json();
            if (item && item.title) {
                text += `*${i + 1}.* ${item.title}\n${item.url ? item.url + "\n" : ""}\n`;
            }
        }
        text += config.FOOTER;
        await reply(text);
    } catch (e) {
        reply("❌ *News fetch failed!*");
    }
});

cmd({
    pattern: "password",
    alias: ["pass", "genpass"],
    react: "🔐",
    desc: "Generate a strong password",
    category: "tools",
    use: ".password [length]",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply}) => {
    const len = Math.min(Math.max(parseInt(q) || 12, 6), 64);
    const chars = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!@#$%^&*";
    let pass = "";
    for (let i = 0; i < len; i++) pass += chars[Math.floor(Math.random() * chars.length)];
    await reply(`🔐 *Password Generator*\n\nLength: ${len}\n\`\`\`${pass}\`\`\`\n\n${config.FOOTER}`);
});

cmd({
    pattern: "crypto",
    alias: ["btc", "coinprice"],
    react: "💰",
    desc: "Crypto price (CoinGecko)",
    category: "tools",
    use: ".crypto bitcoin",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        const id = (q || "bitcoin").trim().toLowerCase().replace(/\s+/g, "-");
        const res = await fetch(`https://api.coingecko.com/api/v3/simple/price?ids=${encodeURIComponent(id)}&vs_currencies=usd,eur,inr&include_24hr_change=true`);
        const data = await res.json();
        if (!data[id]) return reply("❌ *Coin not found!*\nTry: bitcoin, ethereum, dogecoin");
        const c = data[id];
        const ch = c.usd_24h_change != null ? c.usd_24h_change.toFixed(2) + "%" : "N/A";
        await reply(`💰 *${id.toUpperCase()}*\n\n💵 USD: $${c.usd}\n💶 EUR: €${c.eur}\n🇮🇳 INR: ₹${c.inr}\n📈 24h: ${ch}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Crypto fetch failed!*");
    }
});

cmd({
    pattern: "currency",
    alias: ["forex", "exchange"],
    react: "💱",
    desc: "Currency converter",
    category: "tools",
    use: ".currency 100 USD LKR",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.currency 100 USD LKR`");
        const p = q.trim().split(/ +/);
        if (p.length < 3) return reply("❌ *Usage:* `.currency <amount> <from> <to>`");
        const amount = parseFloat(p[0]);
        const fromC = p[1].toUpperCase();
        const toC = p[2].toUpperCase();
        if (isNaN(amount)) return reply("❌ *Invalid amount!*");
        const res = await fetch(`https://open.er-api.com/v6/latest/${fromC}`);
        const data = await res.json();
        if (data.result !== "success" || !data.rates?.[toC]) return reply("❌ *Currency not supported!*");
        const result = (amount * data.rates[toC]).toFixed(4);
        await reply(`💱 *Currency*\n\n${amount} ${fromC} = *${result} ${toC}*\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Conversion failed!*");
    }
});

cmd({
    pattern: "time",
    alias: ["clock", "timezone"],
    react: "🕐",
    desc: "World time",
    category: "tools",
    use: ".time Asia/Colombo",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        const zone = (q || "Asia/Colombo").trim();
        // use Intl
        const now = new Date();
        const fmt = new Intl.DateTimeFormat("en-GB", {
            timeZone: zone,
            dateStyle: "full",
            timeStyle: "long"
        });
        await reply(`🕐 *Time — ${zone}*\n\n${fmt.format(now)}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Invalid timezone!*\nExample: `.time Asia/Colombo` `.time America/New_York`");
    }
});



cmd({
    pattern: "uuid",
    alias: ["guid"],
    react: "🆔",
    desc: "Generate UUID",
    category: "tools",
    use: ".uuid",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    const id = crypto.randomUUID ? crypto.randomUUID() : ([1e7]+-1e3+-4e3+-8e3+-1e11).replace(/[018]/g, c => (c ^ crypto.randomBytes(1)[0] & 15 >> c / 4).toString(16));
    await reply(`🆔 *UUID*\n\n\`\`\`${id}\`\`\`\n\n${config.FOOTER}`);
});

cmd({
    pattern: "country",
    alias: ["countryinfo"],
    react: "🏳️",
    desc: "Country information",
    category: "tools",
    use: ".country Japan",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.country Sri Lanka`");
        const res = await fetch("https://restcountries.com/v3.1/name/" + encodeURIComponent(q.trim()) + "?fullText=false");
        if (!res.ok) return reply("❌ *Country not found!*");
        const arr = await res.json();
        const c = arr[0];
        const currencies = c.currencies ? Object.values(c.currencies).map(x => x.name).join(", ") : "N/A";
        const langs = c.languages ? Object.values(c.languages).join(", ") : "N/A";
        const text = `🏳️ *${c.name.common}*\n\n🏛️ Official: ${c.name.official}\n首都 Capital: ${(c.capital || []).join(", ")}\n🌍 Region: ${c.region} / ${c.subregion || ""}\n👥 Population: ${c.population?.toLocaleString()}\n💱 Currency: ${currencies}\n🗣️ Languages: ${langs}\n📞 Calling: +${(c.idd?.root || "")}${(c.idd?.suffixes || [""])[0]}\n\n${config.FOOTER}`;
        if (c.flags?.png) {
            await manaofc.sendMessage(from, { image: { url: c.flags.png }, caption: text }, { quoted: mek });
        } else await reply(text);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});


cmd({
    pattern: "readmore",
    react: "📄",
    desc: "Create read more text",
    category: "tools",
    use: ".readmore text1 | text2",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q || !q.includes("|")) return reply("❌ *Usage:* `.readmore Hello | this is hidden`");
    const [a, b] = q.split("|").map(s => s.trim());
    const more = String.fromCharCode(8206).repeat(4001);
    await reply(a + more + b);
});

cmd({
    pattern: "ssweb",
    alias: ["screenshot", "webss"],
    react: "📸",
    desc: "Website screenshot",
    category: "tools",
    use: ".ssweb <url>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.ssweb https://google.com`");
        let url = q.trim();
        if (!/^https?:\/\//i.test(url)) url = "https://" + url;
        await manaofc.sendMessage(from, { react: { text: "📸", key: mek.key } });
        const ss = `https://image.thum.io/get/full/width/1200/crop/900/${encodeURIComponent(url)}`;
        await manaofc.sendMessage(from, {
            image: { url: ss },
            caption: `📸 *Screenshot*\n🔗 ${url}\n\n${config.FOOTER}`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Screenshot failed!*");
    }
});

cmd({
    pattern: "expandurl",
    alias: ["unshort", "expand"],
    react: "🔗",
    desc: "Expand a short URL",
    category: "tools",
    use: ".expandurl <short url>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Provide a short URL!*");
        const res = await fetch(q.trim(), { method: "HEAD", redirect: "follow" });
        await reply(`🔗 *Expanded URL*\n\n📎 ${q}\n✅ ${res.url}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Could not expand URL!*");
    }
});

cmd({
    pattern: "pick",
    alias: ["choose", "select"],
    react: "🎯",
    desc: "Pick random option",
    category: "tools",
    use: ".pick a | b | c",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q || !q.includes("|")) return reply("❌ *Usage:* `.pick tea | coffee | juice`");
    const opts = q.split("|").map(s => s.trim()).filter(Boolean);
    const choice = opts[Math.floor(Math.random() * opts.length)];
    await reply(`🎯 *I pick*\n\n*${choice}*\n\n${config.FOOTER}`);
});

cmd({
    pattern: "count",
    react: "🔢",
    desc: "Count characters/words",
    category: "tools",
    use: ".count <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Provide text!*");
    const chars = q.length;
    const words = q.trim().split(/\s+/).filter(Boolean).length;
    const lines = q.split("\n").length;
    await reply(`🔢 *Text Stats*\n\nCharacters: *${chars}*\nWords: *${words}*\nLines: *${lines}*\n\n${config.FOOTER}`);
});

cmd({
    pattern: "dictionary",
    alias: ["dict"],
    react: "📖",
    desc: "English dictionary definition",
    category: "tools",
    use: ".dictionary word",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.dictionary hello`");
        const { data } = await axios.get(
            "https://api.dictionaryapi.dev/api/v2/entries/en/" + encodeURIComponent(q.trim())
        );
        const e = data[0];
        const mean = e.meanings?.[0]?.definitions?.[0]?.definition || "";
        const example = e.meanings?.[0]?.definitions?.[0]?.example || "";
        let text = `📖 *${e.word}*\n/${e.phonetic || ""}/\n\n${mean}`;
        if (example) text += `\n\n_Example:_ ${example}`;
        text += `\n\n${config.FOOTER}`;
        await reply(text);
    } catch (e) {
        reply("❌ *Word not found!*");
    }
});
// ============================================
// OTHERS COMMANDS
// ============================================


cmd({
    pattern: "device",
    react: "📱",
    desc: "Show your device type",
    category: "others",
    use: ".device",
    filename: __filename
}, async (manaofc, mek, m, { from, reply}) => {
    try {
        const id = mek.key?.id || "";
        let device = "Unknown";
        if (typeof getDevice === "function") {
            device = getDevice(id) || device;
        }
        await reply(`📱 *Device Info*\n\nDevice: *${device}*\nMsg ID: ${id.slice(0, 16)}...\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Could not detect device!*");
    }
});

cmd({
    pattern: "repeat",
    alias: ["say"],
    react: "📢",
    desc: "Repeat your text",
    category: "others",
    use: ".repeat <text>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Provide text!*");
    await reply(q);
});

//=======================================
//========== MOVIE COMMAND ============
//=======================================
cmd({
    pattern: "movie",
    alias: ["film", "moviedl"],
    react: "🎬",
    desc: "Search movie info (OMDb)",
    category: "movie",
    use: ".movie avatar",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.movie Inception`");
        const { data } = await axios.get(
            "https://www.omdbapi.com/?t=" + encodeURIComponent(q) + "&apikey=trilogy"
        );
        if (!data || data.Response === "False") return reply("❌ *Movie not found!*");
        const cap =
            `🎬 *${data.Title}* (${data.Year})\n` +
            `⭐ ${data.imdbRating} | ${data.Runtime}\n` +
            `🎭 ${data.Genre}\n\n` +
            `${data.Plot}\n\n` +
            `🎬 Director: ${data.Director}\n` +
            `${config.FOOTER || ""}`;
        if (data.Poster && data.Poster !== "N/A") {
            await manaofc.sendMessage(
                from,
                { image: { url: data.Poster }, caption: cap },
                { quoted: mek }
            );
        } else {
            await reply(cap);
        }
    } catch (e) {
        reply("❌ *Movie search failed!*");
    }
});

// ============================================
// SINHALASUB SEARCH 
// ============================================

cmd(
  {
    pattern: "sinhalasub",
    react: "🎬",
    alias: ["ssub", "ssubsearch"],
    category: "movie",
    use: ".sinhalasub <movie name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Please provide a movie name!*\n\n*Example:* `.sinhalasub deadpool`");

      await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalasub/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — data is array
      const ssList = Array.isArray(res?.data) ? res.data : [];
      if (!res?.status || !ssList.length) {
        return reply("❌ *No movies found for your search!*");
      }

      const sections = [{
        title: "🎬 Sinhalasub Results",
        rows: ssList.slice(0, 12).map((v, i) => {
          const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
          const short = title.length > 45 ? title.slice(0, 42) + "..." : title;
          return {
            title: `${i + 1}. ${short}`,
            description: "Sinhala Subtitles",
            rowId: prefix + "ssinfo " + (v.url || "")
          };
        })
      }];

      const listMessage = {
        image: "https://files.catbox.moe/pd13j8.webp",
        text: `*🎬 ${config.BOT_NAME} SINHALASUB*\n\n🔍 Query: *${q}*\n📊 Results: *${ssList.length}*\n\nSelect a movie:`,
        footer: config.FOOTER,
        buttonText: "📥 Open Results",
        sections
      };

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

// ============================================
// SINHALASUB INFO 
// ============================================

cmd(
  {
    pattern: "ssinfo",
    react: "📋",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a movie link!*");

      await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalasub/info?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse
      const data = res?.data;
      if (!res?.status || !data) {
        return reply("❌ *Failed to get movie info!*");
      }

      const genres = Array.isArray(data.genres) ? data.genres.join(", ") : (data.genres || "N/A");
      const directors = Array.isArray(data.directors)
        ? data.directors.slice(0, 5).join(", ")
        : (data.directors || "N/A");

      let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*🎬 ${data.title || "Movie"}*\n\n`;
      caption += `*📅 Year:* ${data.year || "N/A"}\n`;
      caption += `*⏱️ Duration:* ${data.duration || "N/A"}\n`;
      caption += `*⭐ IMDB:* ${data.imdb || "N/A"}\n`;
      if (data.language) caption += `*🗣️ Language:* ${data.language}\n`;
      if (data.country) caption += `*🌍 Country:* ${data.country}\n`;
      if (genres !== "N/A") caption += `*🎞️ Genres:* ${genres}\n`;
      if (directors !== "N/A") caption += `*🎬 Directors:* ${directors}\n`;
      caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

      // Only DLServer-01 and DLServer-02
      const allLinks = Array.isArray(data.links) ? data.links : [];
      const links = allLinks.filter((dl) => {
        const s = String(dl.server || "").toLowerCase().replace(/\s+/g, "");
        const d = String(dl.serverDomain || "").toLowerCase();
        return (
          s === "dlserver-01" ||
          s === "dlserver-02" ||
          s === "dlserver01" ||
          s === "dlserver02" ||
          d.includes("cdn.sinhalasub") ||
          d.includes("ddl.sinhalasub")
        );
      });

      if (!links.length) {
        if (data.thumbnail) {
          await manaofc.sendMessage(from, { image: { url: data.thumbnail }, caption }, { quoted: mek });
        }
        return reply("❌ *No DLServer-01 / DLServer-02 links found!*");
      }

      const sections = [{
        title: "📥 DLServer Downloads",
        rows: links.slice(0, 15).map((dl) => ({
          title: `${dl.quality || "DL"} (${dl.size || "N/A"})`,
          description: `${dl.server || "Server"} • ${dl.serverDomain || ""}`.slice(0, 60),
          rowId: prefix + "ssdown " + (dl.pageLink || dl.link || "")
        }))
      }];

      const listMessage = {
        text: caption + "\n\n*Select a quality (DLServer only):*",
        footer: config.FOOTER,
        title: (data.title || "Movie").slice(0, 50),
        buttonText: "📥 Download Options",
        sections
      };

      if (data.thumbnail) {
        await manaofc.sendMessage(from, { image: { url: data.thumbnail }, caption }, { quoted: mek });
      }

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get movie info!*");
    }
  }
);

// ============================================
// SINHALASUB DOWNLOAD 
// ============================================

cmd(
  {
    pattern: "ssdown",
    react: "📁",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a download link!*");

      await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });
      await reply("⏳ *Fetching download link...*");

      const api = await fetch("https://manaofc-api.vercel.app/sinhalasub/download?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse
      const data = res?.data;
      if (!res?.status || !data) {
        return reply("❌ *Failed to get download link!*");
      }

      const downloadUrl = data.downloadUrl || data.directUrl || null;
      if (!downloadUrl) {
        return reply("❌ *No direct download URL found!*");
      }

      let fileName = (data.title || "movie").replace(/[^\w\s\-\.]/g, "").slice(0, 80);
      if (!fileName) fileName = "movie";
      if (!/\.mp4$/i.test(fileName)) fileName += ".mp4";

      const serverTag = data.serverType ? `\n📡 ${data.serverType}` : "";

      await manaofc.sendMessage(
        from,
        {
          document: { url: downloadUrl },
          mimetype: "video/mp4",
          fileName,
          caption: `🎬 *${data.title || "Movie"}*${serverTag}\n✅ ${config.BOT_NAME}\n\n${config.FOOTER || ""}`
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Download failed!* (File may be too large for WhatsApp)");
    }
  }
);

// ============================================
// CINESUBZ SEARCH 
// ============================================

cmd(
  {
    pattern: "cinesubz",
    react: "🎬",
    alias: ["cs", "movie"],
    category: "movie",
    use: ".cinesubz <movie/tv name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Please provide a movie/TV name!*\n\n*Example:* `.cinesubz deadpool`\n*Example:* `.cinesubz game of thrones`");

      await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

      const api = await fetch("https://manaofc-api.vercel.app/cinesubz/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — no apiOk / apiList
      const csList = Array.isArray(res?.data) ? res.data : [];
      if (!res?.status || !csList.length) {
        return reply("❌ *No results found for your search!*");
      }

      const sections = [{
        title: "🎬 Search Results",
        rows: csList.slice(0, 15).map((v, i) => {
          const typeTag = (v.type === "tvshow" || (v.badge || "").toLowerCase().includes("s0") || (v.badge || "").toLowerCase().includes("complete"))
            ? "📺 TV"
            : "🎥 Movie";
          const badge = v.badge ? ` • ${v.badge}` : "";
          const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
          const short = title.length > 45 ? title.slice(0, 42) + "..." : title;
          return {
            title: `${i + 1}. ${short}`,
            description: `${typeTag}${badge}`,
            rowId: prefix + "cinfo " + (v.url || v.link || "")
          };
        })
      }];

      const listMessage = {
        image: "https://files.catbox.moe/19prro.jpeg",
        text: `*🎬 ${config.BOT_NAME} CINESUBZ SEARCH*\n\n🔍 Query: *${q}*\n📊 Results: *${csList.length}*\n\nSelect an item below:`,
        footer: config.FOOTER,
       // title: "CineSubz Results",
        buttonText: "📥 Open Results",
        sections
      };

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

// ============================================
// CINESUBZ INFO (movie / tvshow / episode)
// ============================================

cmd(
  {
    pattern: "cinfo",
    react: "📋",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a CineSubz link!*");

      await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });

      const api = await fetch("https://manaofc-api.vercel.app/cinesubz/info?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — no apiOk / apiData
      const data = res?.data;
      if (!res?.status || !data || typeof data !== "object") {
        return reply("❌ *Failed to get info!*");
      }

      const type = (data.type || "").toLowerCase();
      const directors = Array.isArray(data.directors)
        ? data.directors.slice(0, 5).join(", ")
        : (data.directors || "N/A");
      const genres = Array.isArray(data.genres) ? data.genres.join(", ") : (data.genres || "N/A");

      // ---------- TV SHOW: episode list ----------
      if (type === "tvshow" || (Array.isArray(data.episodes) && data.episodes.length && !(Array.isArray(data.links) && data.links.length))) {
        const episodes = Array.isArray(data.episodes) ? data.episodes : [];
        if (!episodes.length) {
          return reply("❌ *No episodes found for this TV show!*");
        }

        let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*📺 ${data.title || "TV Show"}*\n\n`;
        caption += `*📅 Year:* ${data.year || "N/A"}\n`;
        caption += `*⭐ IMDB:* ${data.imdb || data.rating || "N/A"}\n`;
        caption += `*🎞️ Genres:* ${genres}\n`;
        if (data.episodeInfo) caption += `*ℹ️ Info:* ${String(data.episodeInfo).slice(0, 200)}\n`;
        caption += `*📊 Episodes:* ${episodes.length}\n`;
        caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

        const bySeason = {};
        for (const ep of episodes) {
          const s = String(ep.season || "1");
          if (!bySeason[s]) bySeason[s] = [];
          bySeason[s].push(ep);
        }
        const seasonKeys = Object.keys(bySeason).sort((a, b) => Number(a) - Number(b));

        if (seasonKeys.length > 1 && episodes.length > 20) {
          const sections = [{
            title: "📺 Select Season",
            rows: seasonKeys.map((s) => ({
              title: `Season ${s}`,
              description: `${bySeason[s].length} episode(s)`,
              rowId: prefix + "cseason " + s + " " + q.trim()
            }))
          }];
          const listMessage = {
            text: caption + "\n\n*Select a season:*",
            footer: config.FOOTER,
            title: (data.title || "TV Show").slice(0, 50),
            buttonText: "📺 Seasons",
            sections
          };
          if (data.thumbnail) {
            await manaofc.sendMessage(from, { image: { url: data.thumbnail }, caption }, { quoted: mek });
          }
          await manaofc.listMessage(from, listMessage, mek);
        } else {
          const rows = episodes.slice(0, 25).map((ep) => {
            const sn = ep.season ? `S${String(ep.season).padStart(2, "0")}` : "";
            const en = ep.episode ? `E${String(ep.episode).padStart(2, "0")}` : "";
            const label = `${sn}${en}`.trim() || "EP";
            const etitle = (ep.title || "Episode").slice(0, 40);
            return {
              title: `${label} — ${etitle}`,
              description: ep.airDate || "Episode",
              rowId: prefix + "cinfo " + (ep.url || "")
            };
          });
          const sections = [{ title: "📺 Episodes", rows }];
          const listMessage = {
            text: caption + "\n\n*Select an episode to download:*",
            footer: config.FOOTER,
            title: (data.title || "TV Show").slice(0, 50),
            buttonText: "📥 Episodes",
            sections
          };
          if (data.thumbnail) {
            await manaofc.sendMessage(from, { image: { url: data.thumbnail }, caption }, { quoted: mek });
          }
          await manaofc.listMessage(from, listMessage, mek);
        }

        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
        return;
      }

      // ---------- MOVIE or EPISODE: quality links ----------
      const links = Array.isArray(data.links) ? data.links : [];
      if (!links.length) {
        return reply("❌ *No download links found!*");
      }

      let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*🎬 ${data.title || "Title"}*\n\n`;
      caption += `*📅 Year:* ${data.year || "N/A"}\n`;
      if (data.duration) caption += `*⏱️ Duration:* ${data.duration}\n`;
      caption += `*⭐ IMDB:* ${data.imdb || data.rating || "N/A"}\n`;
      if (data.language) caption += `*🗣️ Language:* ${data.language}\n`;
      if (data.country) caption += `*🌍 Country:* ${data.country}\n`;
      if (directors && directors !== "N/A") caption += `*🎬 Directors:* ${directors}\n`;
      if (genres && genres !== "N/A") caption += `*🎞️ Genres:* ${genres}\n`;
      if (data.subtitleBy) caption += `*📝 Subtitles:* ${data.subtitleBy}\n`;
      caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

      const sections = [{
        title: "📥 Download Qualities",
        rows: links.slice(0, 12).map((dl) => ({
          title: `${dl.quality || "Download"} (${dl.size || "N/A"})`,
          description: (dl.meta || dl.server || "Direct Link").slice(0, 60),
          rowId: prefix + "cdown " + (dl.pageLink || dl.link || "")
        }))
      }];

      const listMessage = {
        text: caption + "\n\n*Select a quality to download:*",
        footer: config.FOOTER,
        title: (data.title || "Movie").slice(0, 50),
        buttonText: "📥 Download Options",
        sections
      };

      if (data.thumbnail || data.image) {
        await manaofc.sendMessage(from, {
          image: { url: data.thumbnail || data.image },
          caption
        }, { quoted: mek });
      }

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get info!*");
    }
  }
);

// ============================================
// CINESUBZ SEASON (filter episodes for one season)
// ============================================

cmd(
  {
    pattern: "cseason",
    react: "📺",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Usage:* `.cseason <season> <tvshow-url>`");
      const parts = q.trim().split(/\s+/);
      const seasonNum = parts[0];
      const showUrl = parts.slice(1).join(" ");
      if (!showUrl) return reply("❌ *Need TV show URL!*");

      await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });

      const api = await fetch("https://manaofc-api.vercel.app/cinesubz/info?url=" + encodeURIComponent(showUrl) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — no apiOk / apiData
      const data = res?.data;
      if (!res?.status || !data) {
        return reply("❌ *Failed to load seasons!*");
      }

      const episodes = (Array.isArray(data.episodes) ? data.episodes : []).filter(
        (ep) => String(ep.season) === String(seasonNum)
      );
      if (!episodes.length) {
        return reply(`❌ *No episodes found for Season ${seasonNum}!*`);
      }

      const caption = `*📺 ${data.title || "TV Show"}*\n*Season ${seasonNum}* — ${episodes.length} episode(s)\n\nSelect an episode:`;

      const rows = episodes.slice(0, 25).map((ep) => {
        const en = ep.episode ? `E${String(ep.episode).padStart(2, "0")}` : "EP";
        return {
          title: `${en} — ${(ep.title || "Episode").slice(0, 40)}`,
          description: ep.airDate || `Season ${seasonNum}`,
          rowId: prefix + "cinfo " + (ep.url || "")
        };
      });

      const listMessage = {
        text: caption,
        footer: config.FOOTER,
        title: `Season ${seasonNum}`,
        buttonText: "📥 Episodes",
        sections: [{ title: `Season ${seasonNum}`, rows }]
      };
      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Season load failed!*");
    }
  }
);

// ============================================
// CINESUBZ DOWNLOAD 
// ============================================

cmd(
  {
    pattern: "cdown",
    react: "📁",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a download link!*");

      await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });
      await reply("⏳ *Fetching download link... Please wait*");

      const api = await fetch("https://manaofc-api.vercel.app/cinesubz/download?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — no apiOk / apiData / apiDownloadUrl
      const data = res?.data;
      if (!res?.status || !data) {
        return reply("❌ *Failed to get download link!*");
      }

      const downloadUrl = data.downloadUrl || data.directUrl || data.url || null;

      if (!downloadUrl) {
        return reply("❌ *No direct download URL found!*");
      }

      let fileName = data.filename
        ? decodeURIComponent(String(data.filename))
        : (data.title || "movie") + ".mp4";
      fileName = fileName.replace(/[^\w\s\-\.%\[\]]/g, "").slice(0, 100);
      if (!/\.mp4$/i.test(fileName)) fileName += ".mp4";

      await manaofc.sendMessage(
        from,
        {
          document: { url: downloadUrl },
          mimetype: "video/mp4",
          fileName,
          caption: `🎬 *${data.title || "Download"}*\n✅ ${config.BOT_NAME}\n\n${config.FOOTER || ""}`
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Download failed!* (File may be too large for WhatsApp — try another quality)");
    }
  }
);

// ============================================
// SINHALACARTOONS SEARCH
// ============================================

cmd(
  {
    pattern: "sinhalacartoons",
    react: "📺",
    alias: ["sc", "cartoon"],
    category: "movie",
    use: ".sinhalacartoons <cartoon name>",
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Please provide a cartoon name!*\n\n*Example:* `.sinhalacartoons ben 10`");

      await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — { status, data: { results: [...] } }
      const results = Array.isArray(res?.data?.results)
        ? res.data.results
        : (Array.isArray(res?.data) ? res.data : []);

      if (!res?.status || !results.length) {
        return reply("❌ *No cartoons found for your search!*");
      }

      const sections = [{
        title: "📺 Cartoons",
        rows: results.slice(0, 15).map((v, i) => {
          const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
          const short = title.length > 45 ? title.slice(0, 42) + "..." : title;
          return {
            title: `${i + 1}. ${short}`,
            description: "Sinhala Cartoons",
            rowId: prefix + "scinfo " + (v.link || v.url || "")
          };
        })
      }];

      const listMessage = {
        image: "https://files.catbox.moe/f98ki7.png",
        text: `*📺 ${config.BOT_NAME} SINHALACARTOONS*\n\n🔍 Query: *${q}*\n📊 Results: *${results.length}*\n\nSelect a series:`,
        footer: config.FOOTER,
        buttonText: "📥 Open Results",
        sections
      };

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *An error occurred while searching!*");
    }
  }
);

// ============================================
// SINHALACARTOONS INFO + EPISODE LIST
// ============================================

cmd(
  {
    pattern: "scinfo",
    react: "📋",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need a cartoon link!*");

      await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });

      const postUrl = q.trim();
      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/download?url=" + encodeURIComponent(postUrl) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse — { status, data: { title, episodes: [...] } }
      const data = res?.data;
      if (!res?.status || !data || !data.title) {
        return reply("❌ *Failed to get cartoon info!*");
      }

      const episodes = Array.isArray(data.episodes) ? data.episodes : [];

      let caption = `*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*📺 ${data.title}*\n\n`;
      caption += `*📅 Year:* ${data.year || "N/A"}\n`;
      caption += `*⭐ IMDB:* ${data.imdb || "N/A"}\n`;
      caption += `*🎞️ Quality:* ${data.quality || "N/A"}\n`;
      caption += `*📀 Episodes:* ${episodes.length}\n`;
      caption += `*╰━━━━━━━✧༺♥༻✧━━━━━━━*`;

      if (data.featuredImage) {
        await manaofc.sendMessage(from, {
          image: { url: data.featuredImage },
          caption
        }, { quoted: mek });
      } else {
        await reply(caption);
      }

      if (!episodes.length) {
        return reply("❌ *No episodes found!*");
      }

      const rows = episodes.slice(0, 25).map((ep, index) => {
        const num = ep.number || String(index + 1).padStart(2, "0");
        const etitle = (ep.title || `Episode ${num}`).slice(0, 40);
        return {
          title: `📀 EP ${num} — ${etitle}`,
          description: `Episode ${num}`,
          rowId: prefix + "scget " + index + " " + postUrl
        };
      });

      const sections = [{ title: "📂 Episodes", rows }];
      const listMessage = {
        text: `*📥 ${data.title}*\n\n*Total:* ${episodes.length} episode(s)\nSelect one to download:`,
        footer: config.FOOTER,
        title: (data.title || "Cartoon").slice(0, 50),
        buttonText: "📂 View Episodes",
        sections
      };

      await manaofc.listMessage(from, listMessage, mek);
      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Failed to get cartoon info!*");
    }
  }
);

// ============================================
// SINHALACARTOONS GET EPISODE
// ============================================

cmd(
  {
    pattern: "scget",
    react: "📤",
    dontAddCommandList: true,
    filename: __filename,
  },
  async (manaofc, mek, m, { from, q, reply }) => {
    try {
      if (!q) return reply("❌ *Need download parameters!*");

      const parts = q.trim().split(/\s+/);
      const index = parseInt(parts[0], 10);
      const postUrl = parts.slice(1).join(" ");

      if (isNaN(index) || !postUrl) return reply("❌ *Invalid download parameters!*");

      await manaofc.sendMessage(from, { react: { text: "⬆️", key: mek.key } });
      await reply("⏳ *Fetching episode...*");

      const api = await fetch("https://manaofc-api.vercel.app/sinhalacartoons/download?url=" + encodeURIComponent(postUrl) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz");
      const res = await api.json();

      // Direct parse
      const data = res?.data;
      if (!res?.status || !data) {
        return reply("❌ *Failed to load episodes!*");
      }

      const episodes = Array.isArray(data.episodes) ? data.episodes : [];
      const ep = episodes[index];

      if (!ep) {
        return reply("❌ *Episode not found!*");
      }

      const downloadUrl = ep.directUrl || ep.videoUrl || null;
      if (!downloadUrl) {
        return reply("❌ *No direct download URL for this episode!*");
      }

      const num = ep.number || String(index + 1).padStart(2, "0");
      let fileName = (ep.title || `Episode_${num}`).replace(/[^\w\s\-\.]/g, "").trim();
      if (!fileName) fileName = `Episode_${num}`;
      if (!/\.mp4$/i.test(fileName)) fileName += ".mp4";

      await manaofc.sendMessage(
        from,
        {
          document: { url: downloadUrl },
          mimetype: "video/mp4",
          fileName,
          caption: `📺 *${data.title || "Cartoon"}*\n📀 EP ${num} — ${ep.title || fileName}\n✅ ${config.BOT_NAME}\n\n${config.FOOTER || ""}`
        },
        { quoted: mek }
      );

      await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
      console.log(e);
      reply("❌ *Download failed!* (File may be too large — try another episode)");
    }
  }
);

// ============================================
// ZOOM SEARCH COMMAND
// ============================================
cmd({
    pattern: "zoom",
    desc: "Search Sinhala subtitles from Zoom.lk",
    use: ".zoom <movie name>",
    react: "📝",
    category: "movie",
    filename: __filename
},
async (manaofc, mek, m, { from, prefix, q, reply }) => {
    try {
        if (!q) return reply("*🔍 Please enter a movie name!*\n\nExample: `.zoom deadpool`");

        await manaofc.sendMessage(from, { react: { text: "🔍", key: mek.key } });

        const response = await fetch(
            "https://manaofc-api.vercel.app/zoom/search?q=" + encodeURIComponent(q) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const res = await response.json();

        // Direct parse — { status, data: { results: [...] } }
        const results = Array.isArray(res?.data?.results)
            ? res.data.results
            : (Array.isArray(res?.data) ? res.data : []);

        if (!res?.status || !results.length) {
            return reply("*❌ No results found!*");
        }

        const sections = [{
            title: "📝 Zoom Subtitles",
            rows: results.slice(0, 12).map((v, i) => {
                const title = (v.title || "Unknown").replace(/\s+/g, " ").trim();
                const short = title.length > 42 ? title.slice(0, 39) + "..." : title;
                const desc = [v.author, v.time].filter(Boolean).join(" • ") || "Sinhala Subtitle";
                return {
                    title: `${i + 1}. ${short}`,
                    description: desc.slice(0, 60),
                    rowId: prefix + "dzoom " + (v.link || v.url || "")
                };
            })
        }];

        const listMessage = {
            image: "https://files.catbox.moe/higob5.png",
            text: `*📝 ${config.BOT_NAME} ZOOM*\n\n🔍 Query: *${q}*\n📊 Results: *${results.length}*\n\nSelect a subtitle:`,
            footer: config.FOOTER,
            buttonText: "📥 Open Results",
            sections
        };

        await manaofc.listMessage(from, listMessage, mek);
        await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
    } catch (e) {
        console.log(e);
        reply("*❌ Error occurred while searching!*");
    }
});

// ============================================
// ZOOM DOWNLOAD COMMAND
// ============================================
cmd({
    pattern: "dzoom",
    desc: "Download Sinhala subtitle from Zoom.lk",
    react: "⬇️",
    dontAddCommandList: true,
    filename: __filename
},
async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("*Need a post URL!*");

        await manaofc.sendMessage(from, { react: { text: "⬇️", key: mek.key } });

        const response = await fetch(
            "https://manaofc-api.vercel.app/zoom/download?url=" + encodeURIComponent(q.trim()) + "&apikey=manaofc-fd0ip3t79rrkggfzyfd0txwz"
        );
        const res = await response.json();

        // Direct parse — { status, data: { title, downloadLink, ... } }
        const zoom = res?.data;
        if (!res?.status || !zoom || !zoom.title) {
            return reply("*❌ Failed to get subtitle info!*");
        }

        const dlLink = zoom.downloadLink || zoom.download_url || zoom.url || null;
        if (!dlLink) {
            return reply("*❌ Download link not found!*");
        }

        let infoCaption = "*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n*📝 Subtitle Info*\n\n";
        infoCaption += `*Title:* ${zoom.title}\n`;
        infoCaption += `*Author:* ${zoom.author || "N/A"}\n`;
        infoCaption += `*Views:* ${zoom.view || "N/A"}\n`;
        infoCaption += `*Hits:* ${zoom.downloadHits || "N/A"}\n`;
        if (zoom.downloadText) infoCaption += `*File:* ${zoom.downloadText}\n`;
        infoCaption += "*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n*⬇️ Downloading subtitle...*";

        await manaofc.sendMessage(from, { text: infoCaption }, { quoted: mek });

        const cleanTitle = String(zoom.title)
            .replace(/[^a-zA-Z0-9\s\u0D80-\u0DFF]/g, "")
            .replace(/\s+/g, "_")
            .slice(0, 60) || "subtitle";
        const fileName = cleanTitle + ".srt";

        try {
            await manaofc.sendMessage(from, {
                document: { url: dlLink },
                mimetype: "application/x-subrip",
                fileName,
                caption: `*✅ ${zoom.title}*\n*📥 ${zoom.downloadHits || ""}*\n\n${config.FOOTER || ""}`
            }, { quoted: mek });
            await manaofc.sendMessage(from, { react: { text: "✅", key: mek.key } });
        } catch (downloadError) {
            console.log("Download failed:", downloadError);
            await manaofc.sendMessage(from, {
                text: "*⚠️ Auto-send failed — use this link:*\n\n" +
                      `*Title:* ${zoom.title}\n` +
                      `*Link:* ${dlLink}\n\n` +
                      "Open the link in browser to download."
            }, { quoted: mek });
            await manaofc.sendMessage(from, { react: { text: "⚠️", key: mek.key } });
        }
    } catch (e) {
        console.log(e);
        reply("*❌ Error occurred!*");
    }
});


//===================================
//====== AI COMMAND =================
//===================================

cmd({
    pattern: "gpt",
    alias: ["chatgpt", "ask"],
    react: "🤖",
    desc: "AI chat (Pollinations text)",
    category: "ai",
    use: ".gpt What is gravity?",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.gpt What is gravity?`");
        await reply("🤔 Thinking...");
        const url = "https://text.pollinations.ai/" + encodeURIComponent(q);
        const { data } = await axios.get(url, {
            timeout: 60000,
            responseType: "text",
            transformResponse: [(r) => r],
        });
        const answer = typeof data === "string" ? data : JSON.stringify(data);
        await reply(`🤖 *AI*\n\n${answer.slice(0, 3500)}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *AI failed!*");
    }
});

cmd({
    pattern: "ai",
    react: "🤖",
    desc: "AI chat",
    category: "ai",
    use: ".ai question",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.ai hello`");
        const { data } = await axios.get(
            "https://text.pollinations.ai/" + encodeURIComponent(q),
            {
                timeout: 60000,
                responseType: "text",
                transformResponse: [(r) => r],
            }
        );
        await reply(`🤖 ${String(data).slice(0, 3500)}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *AI failed!*");
    }
});

//====================================
// ========== LOGO COMMANDS ==========
//====================================
// Helper: Download image buffer from URL
async function getBuffer(url) {
    try {
        const response = await axios.get(url, { 
            responseType: 'arraybuffer',
            timeout: 30000
        });
        return Buffer.from(response.data);
    } catch (e) {
        throw new Error("Failed to download image: " + e.message);
    }
}

// Helper: Generate image using Pollinations AI (FREE - No API Key)
async function generatePollinationsImage(prompt, options = {}) {
    const {
        width = 1024,
        height = 1024,
        seed = Math.floor(Math.random() * 1000000),
        model = 'flux',
        nologo = true
    } = options;

    // Pollinations AI - Completely FREE, No API Key needed
    const encodedPrompt = encodeURIComponent(prompt);
    const url = `https://image.pollinations.ai/prompt/${encodedPrompt}?width=${width}&height=${height}&seed=${seed}&model=${model}&nologo=${nologo}`;

    return await getBuffer(url);
}
//=========================

const logoStyles = [
    { pattern: "neon", react: "💡", prompt: (text) => `Neon glowing text logo "${text}", cyberpunk style, vibrant neon colors, glowing effect, dark background, high quality, professional logo design` },
    { pattern: "glitch", react: "👾", prompt: (text) => `Glitch effect text logo "${text}", digital distortion, RGB split, cyber glitch art, retro tech style, dark background, high quality` },
    { pattern: "metal", react: "🔩", prompt: (text) => `Metallic 3D text logo "${text}", chrome metal effect, reflective surface, gold and silver, industrial style, professional logo, high quality` },
    { pattern: "firelogo", react: "🔥", prompt: (text) => `Fire and flames text logo "${text}", burning fire effect, orange and red flames, intense heat, dark background, epic style, high quality` },
    { pattern: "graffiti", react: "🎨", prompt: (text) => `Graffiti street art text logo "${text}", colorful spray paint, urban wall art style, hip hop culture, vibrant colors, brick wall background, high quality` },
    { pattern: "logo3d", react: "🧊", prompt: (text) => `3D extruded text logo "${text}", three dimensional depth, shadows and lighting, modern geometric style, clean background, professional logo, high quality render` },
    { pattern: "gaming", react: "🎮", prompt: (text) => `Gaming esports text logo "${text}", aggressive font style, red and black colors, battle royale theme, professional gaming team logo, high quality` },
    { pattern: "devil", react: "😈", prompt: (text) => `Devil demon text logo "${text}", horns and fire, dark evil style, red and black colors, hell theme, scary font, high quality` },
    { pattern: "wolf", react: "🐺", prompt: (text) => `Wolf howling text logo "${text}", wolf silhouette, moon and stars, galaxy background, blue and silver colors, wild nature theme, high quality` },
    { pattern: "joker", react: "🃏", prompt: (text) => `Joker clown text logo "${text}", playing cards, purple and green colors, chaotic madness style, dark gothic theme, high quality` },
    { pattern: "blackpink", react: "💗", prompt: (text) => `Kpop pink neon text logo "${text}", Blackpink style, pink and black colors, girly aesthetic, sparkles and hearts, high quality` },
    { pattern: "cloud", react: "☁️", prompt: (text) => `Cloud sky text logo "${text}", fluffy white clouds, blue sky background, heavenly dreamy style, soft colors, peaceful, high quality` },
    { pattern: "thunder", react: "⚡", prompt: (text) => `Thunder lightning text logo "${text}", electric blue lightning bolts, stormy dark clouds, powerful energy, electric sparks, high quality` },
    { pattern: "blood", react: "🩸", prompt: (text) => `Blood dripping text logo "${text}", horror style, red blood splatter, dark creepy background, scary font, Halloween theme, high quality` },
    { pattern: "sand", react: "🏖️", prompt: (text) => `Sand beach text "${text}", written in wet sand, tropical beach, ocean waves, sunset background, realistic, high quality` },
    { pattern: "coffee", react: "☕", prompt: (text) => `Coffee cup text logo "${text}", latte art style, coffee beans, warm brown colors, cozy cafe aesthetic, steam rising, high quality` },
    { pattern: "christmas", react: "🎄", prompt: (text) => `Christmas holiday text logo "${text}", snowflakes, Christmas tree, red and green colors, festive decorations, winter theme, high quality` },
    { pattern: "love", react: "❤️", prompt: (text) => `Love romantic text logo "${text}", red hearts, roses, pink and red colors, valentine theme, cute aesthetic, high quality` },
    { pattern: "wood", react: "🪵", prompt: (text) => `Wood carved text logo "${text}", engraved in wooden planks, rustic natural style, brown wood texture, forest theme, high quality` },
    { pattern: "galaxy", react: "🌌", prompt: (text) => `Galaxy space text logo "${text}", stars and nebula, purple and blue cosmic colors, universe theme, glowing stars, high quality` },
    { pattern: "retro", react: "📺", prompt: (text) => `Retro vintage text logo "${text}", 80s style, VHS effect, old TV static, neon grid, synthwave colors, nostalgic, high quality` },
    { pattern: "watercolor", react: "🎨", prompt: (text) => `Watercolor paint text logo "${text}", artistic brush strokes, colorful splashes, hand painted style, soft pastel colors, creative art, high quality` },
    { pattern: "gold", react: "🏆", prompt: (text) => `Gold luxury text logo "${text}", golden shiny letters, rich elegant style, diamonds and jewels, black background, premium feel, high quality` },
    { pattern: "ice", react: "🧊", prompt: (text) => `Ice frozen text logo "${text}", crystal ice effect, snowflakes, winter cold theme, blue and white colors, frosty, high quality` },
    { pattern: "ninja", react: "🥷", prompt: (text) => `Ninja warrior text logo "${text}", Japanese katana, shadow silhouette, black and red colors, martial arts theme, stealth, high quality` },
    { pattern: "dragon", react: "🐉", prompt: (text) => `Dragon fire text logo "${text}", mythical dragon, scales and fire, epic fantasy style, gold and red colors, powerful, high quality` },
    { pattern: "anime", react: "🇯🇵", prompt: (text) => `Anime manga text logo "${text}", Japanese anime style, colorful kawaii, cherry blossoms, cute characters, vibrant colors, high quality` },
    { pattern: "skull", react: "💀", prompt: (text) => `Skull skeleton text logo "${text}", skull and crossbones, dark gothic style, bones and graveyard, horror punk theme, high quality` },
];

logoStyles.forEach(style => {
    cmd({
        pattern: style.pattern,
        react: style.react,
        desc: `Create ${style.pattern} style text logo`,
        category: "logo",
        use: `.${style.pattern} <text>`,
        filename: __filename
    },
    async (manaofc, mek, m, { from, q, reply}) => {
        try {
            if (!q) return reply(`❌ *Provide text!*\nExample: \`.${style.pattern} MANAOFC\``);

            await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });

            const prompt = style.prompt(q);
            const buffer = await generatePollinationsImage(prompt, { width: 1024, height: 512 });

            await manaofc.sendMessage(from, {
                image: buffer,
                caption: `${style.react} *${style.pattern.charAt(0).toUpperCase() + style.pattern.slice(1)} Logo*\n\nText: ${q}\n${config.FOOTER || '> _*Powered By Manaofc*_'} `
            }, { quoted: mek });

        } catch (e) {
            console.error(e);
            reply(`❌ *Failed to create ${style.pattern} logo!*\n` + e.message);
        }
    });
});

//===================================
//======== MAIN COMMAND ==========
//==================================
// system command
cmd({
    pattern: "system",
    react: "🎑",
    alias: ["os","cpu"],
    desc: "Check bot\'s system info",
    category: "main",
    use: '.system',
    filename: __filename
},
async(manaofc, mek, m,{from, reply}) => {
try{
  let totalStorage = Math.floor(os.totalmem() / 1024 / 1024) + 'MB'
  let freeStorage = Math.floor(os.freemem() / 1024 / 1024) + 'MB'
  let cpuModel = os.cpus()[0].model
  let cpuSpeed = os.cpus()[0].speed / 1000
  let cpuCount = os.cpus().length
  let hostname = os.hostname()

  let mes = `
*⚙️ ${config.BOT_NAME} SYSTEM INFO. ⚙️*

  ◈ *Owner*: manaofc
  ◈ *Version*: ${version}
  ◈ *Runtime*: ${runtime(process.uptime())}
  ◈ *Os Name*: ${hostname}
  ◈ *Total Ram*: ${totalStorage}
  ◈ *Free Ram*: ${freeStorage}
  ◈ *CPU Model*: ${cpuModel}
  ◈ *CPU Speed*: ${cpuSpeed} GHz
  ◈ *CPU Cores*: ${cpuCount} 
  
${config.FOOTER}`

await manaofc.sendMessage(from, { image: {url: config.IMAGE_PATH}, caption: mes }, { quoted: mek })
    
} catch (e) {
reply('*Error !!*')
console.log(e)
}
})

// main command
cmd({
    pattern: "ping",
    alias: ["speed", "pong"],
    use: '.ping',
    desc: "Check bot's response time.",
    category: "main",
    react: "⚡",
    filename: __filename
},
async (manaofc, mek, m, { from, quoted, sender, reply}) => {
    try {
        const start = Date.now();

        const reactionEmojis = ['🔥', '⚡', '🚀', '💨', '🎯', '🎉', '🌟', '💥', '🕐', '🔹'];
        const textEmojis = ['💎', '🏆', '⚡️', '🚀', '🎶', '🌠', '🌀', '🔱', '🛡️', '✨'];

        const reactionEmoji = reactionEmojis[Math.floor(Math.random() * reactionEmojis.length)];
        let textEmoji = textEmojis[Math.floor(Math.random() * textEmojis.length)];

        while (textEmoji === reactionEmoji) {
            textEmoji = textEmojis[Math.floor(Math.random() * textEmojis.length)];
        }

        await manaofc.sendMessage(from, {
            react: { text: textEmoji, key: mek.key }
        });

        const end = Date.now();
        const responseTime = end - start;

        const text = `${config.BOT_NAME}\n\n*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n🏓 *Pong!* ${reactionEmoji}\n⏱️ Response Time: *${responseTime} ms*\n*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n${config.FOOTER}`;

        await manaofc.sendMessage(from, {
            image: { url: config.IMAGE_PATH },
            caption: text
        }, { quoted: mek });

    } catch (e) {
        console.error("Error in ping command:", e);
        reply("An error occurred: " + e.message);
    }
});
// owner command 
cmd({
    pattern: "owner",
    desc: "Display owner contact information.",
    react: "🌝",
    use: ".owner",
    category: "main",
    filename: __filename
},
async (manaofc, mek, m, { from, reply }) => {
    try {
        const vcard = 
            'BEGIN:VCARD\n' +
            'VERSION:3.0\n' +
            'FN:MANAOFC\n' +
            'ORG:MANAOFC\n' +
            'TEL;type=CELL;type=VOICE;waid=94759934522:+94759934522\n' +
            'EMAIL:manishasasmith27@gmail.com\n' +
            'END:VCARD';

        await manaofc.sendMessage(from, { 
            contacts: { 
                displayName: "manaofc", 
                contacts: [{ vcard }] 
            },  
            quoted: mek 
        });
    } catch (e) {
        console.error(e);
        reply('⚠️ An error occurred while fetching owner information.');
    }
});

// ============================================
// FUN COMMANDS
// ============================================
cmd({
    pattern: "wallpaper",
    alias: ["wall", "wp"],
    react: "🖼️",
    desc: "Random anime wallpaper",
    category: "fun",
    use: ".wallpaper",
    filename: __filename
}, async (manaofc, mek, m, { from, reply}) => {
    try {
        await manaofc.sendMessage(from, { react: { text: "⏳", key: mek.key } });
        const res = await fetch("https://api.waifu.pics/sfw/waifu");
        const data = await res.json();
        if (!data.url) return reply("❌ *Failed to get wallpaper!*");
        await manaofc.sendMessage(from, {
            image: { url: data.url },
            caption: `🖼️ *Wallpaper*\n\n${config.FOOTER}`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Wallpaper failed!*");
    }
});

cmd({
    pattern: "joke",
    react: "😂",
    desc: "Get a random joke",
    category: "fun",
    use: ".joke",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://official-joke-api.appspot.com/random_joke");
        const j = await res.json();
        await reply(`😂 *Joke*\n\n*${j.setup}*\n\n_${j.punchline}_\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Could not fetch joke!*");
    }
});

cmd({
    pattern: "quote",
    react: "💬",
    desc: "Get a random quote",
    category: "fun",
    use: ".quote",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://api.quotable.io/random");
        const j = await res.json();
        await reply(`💬 *Quote*\n\n"${j.content}"\n\n— *${j.author}*\n\n${config.FOOTER}`);
    } catch (e) {
        // fallback
        try {
            const res2 = await fetch("https://zenquotes.io/api/random");
            const arr = await res2.json();
            await reply(`💬 *Quote*\n\n"${arr[0].q}"\n\n— *${arr[0].a}*\n\n${config.FOOTER}`);
        } catch (e2) {
            reply("❌ *Could not fetch quote!*");
        }
    }
});

cmd({
    pattern: "fact",
    react: "🧠",
    desc: "Get a random fun fact",
    category: "fun",
    use: ".fact",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://uselessfacts.jsph.pl/api/v2/facts/random");
        const j = await res.json();
        await reply(`🧠 *Fun Fact*\n\n${j.text}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Could not fetch fact!*");
    }
});

cmd({
    pattern: "pickup",
    alias: ["flirt", "pickupline"],
    react: "😘",
    desc: "Get a random pickup line",
    category: "fun",
    use: ".pickup",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    const lines = [
        "Are you a magician? Because whenever I look at you, everyone else disappears.",
        "Do you have a map? I keep getting lost in your eyes.",
        "Is your name Google? Because you have everything I've been searching for.",
        "Are you Wi-Fi? Because I'm feeling a connection.",
        "If you were a vegetable, you'd be a cute-cumber.",
        "Do you believe in love at first sight — or should I walk by again?",
        "Is it hot in here, or is it just you?",
        "You must be tired — you've been running through my mind all day.",
        "Are you made of copper and tellurium? Because you're Cu-Te.",
        "If beauty were time, you'd be eternity."
    ];
    const line = lines[Math.floor(Math.random() * lines.length)];
    await reply(`😘 *Pickup Line*\n\n${line}\n\n${config.FOOTER}`);
});

cmd({
    pattern: "dice",
    react: "🎲",
    desc: "Roll a dice",
    category: "fun",
    use: ".dice",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    const n = Math.floor(Math.random() * 6) + 1;
    await reply(`🎲 *Dice Roll*\n\nYou got: *${n}*\n\n${config.FOOTER}`);
});

cmd({
    pattern: "coin",
    alias: ["flip"],
    react: "🪙",
    desc: "Flip a coin",
    category: "fun",
    use: ".coin",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    const side = Math.random() < 0.5 ? "Heads" : "Tails";
    await reply(`🪙 *Coin Flip*\n\nResult: *${side}*\n\n${config.FOOTER}`);
});

cmd({
    pattern: "emoji",
    alias: ["emojimix", "mix"],
    react: "😃",
    desc: "Mix two emojis",
    category: "fun",
    use: ".emoji 😀 😎",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        if (!q) return reply("❌ *Example:* `.emoji 😀 😎`");
        const parts = q.trim().split(/ +/);
        if (parts.length < 2) return reply("❌ *Need two emojis!*");
        const e1 = parts[0], e2 = parts[1];
        const url = `https://tenor.googleapis.com/v2/featured?key=AIzaSyAyimkuZywD32ci9yhnbTa1QpXxOCpHfX8&contentfilter=high&media_filter=png_transparent&component=proactive&collection=emoji_kitchen_v5&q=${encodeURIComponent(e1)}_${encodeURIComponent(e2)}`;
        const res = await fetch(url);
        const data = await res.json();
        const img = data.results?.[0]?.media_formats?.png_transparent?.url || data.results?.[0]?.url;
        if (!img) return reply("❌ *Could not mix those emojis!*");
        await manaofc.sendMessage(from, { sticker: { url: img } }, { quoted: mek }).catch(async () => {
            await manaofc.sendMessage(from, { image: { url: img }, caption: `${e1} + ${e2}` }, { quoted: mek });
        });
    } catch (e) {
        reply("❌ *Emoji mix failed!*");
    }
});

cmd({
    pattern: "quoteanime",
    alias: ["animequote"],
    react: "🎌",
    desc: "Random anime quote",
    category: "fun",
    use: ".quoteanime",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://animechan.xyz/api/random");
        const d = await res.json();
        await reply(`🎌 *Anime Quote*\n\n"${d.quote}"\n\n— *${d.character}*\n_(${d.anime})_\n\n${config.FOOTER}`);
    } catch (e) {
        try {
            const res2 = await fetch("https://some-random-api.com/animu/quote");
            const d2 = await res2.json();
            await reply(`🎌 *Anime Quote*\n\n"${d2.quote}"\n\n— *${d2.character}*\n_(${d2.anime})_\n\n${config.FOOTER}`);
        } catch (_) {
            reply("❌ *Failed!*");
        }
    }
});


cmd({
    pattern: "number",
    alias: ["numfact", "numbers"],
    react: "🔢",
    desc: "Fun fact about a number",
    category: "fun",
    use: ".number 42",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        const n = q && /^\d+$/.test(q.trim()) ? q.trim() : "random";
        const res = await fetch(`http://numbersapi.com/${n}/trivia?json`);
        const d = await res.json();
        await reply(`🔢 *Number Fact*\n\n${d.text}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "insult",
    react: "😈",
    desc: "Funny roast (friendly)",
    category: "fun",
    use: ".insult",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://evilinsult.com/generate_insult.php?lang=en&type=json");
        const d = await res.json();
        await reply(`😈 *Roast*\n\n${d.insult}\n\n_${config.FOOTER}_`);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "yesno",
    react: "🤔",
    desc: "Yes or No answer",
    category: "fun",
    use: ".yesno <question>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    try {
        const res = await fetch("https://yesno.wtf/api");
        const d = await res.json();
        await manaofc.sendMessage(from, {
            image: { url: d.image },
            caption: `🤔 *${(q || "Question").slice(0, 80)}*\n\nAnswer: *${d.answer.toUpperCase()}*\n\n${config.FOOTER}`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "bored",
    react: "😴",
    desc: "Activity when bored",
    category: "fun",
    use: ".bored",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://www.boredapi.com/api/activity");
        const d = await res.json();
        await reply(`😴 *Try this*\n\n${d.activity}\n\nType: ${d.type}\nParticipants: ${d.participants}\n\n${config.FOOTER}`);
    } catch (e) {
        const fallback = ["Read a chapter of a book", "Go for a short walk", "Learn 5 words in a new language", "Organize your phone gallery", "Call a friend you miss"];
        await reply(`😴 *Try this*\n\n${fallback[Math.floor(Math.random() * fallback.length)]}\n\n${config.FOOTER}`);
    }
});

cmd({
    pattern: "advice",
    react: "💡",
    desc: "Random advice",
    category: "fun",
    use: ".advice",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://api.adviceslip.com/advice");
        const data = await res.json();
        await reply(`💡 *Advice*\n\n${data.slip.advice}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "dog",
    react: "🐶",
    desc: "Random dog image",
    category: "fun",
    use: ".dog",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        const res = await fetch("https://dog.ceo/api/breeds/image/random");
        const data = await res.json();
        await manaofc.sendMessage(from, { image: { url: data.message }, caption: `🐶 ${config.FOOTER}` }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "cat",
    react: "🐱",
    desc: "Random cat image",
    category: "fun",
    use: ".cat",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    try {
        await manaofc.sendMessage(from, {
            image: { url: "https://cataas.com/cat?type=" + Date.now() },
            caption: `🐱 ${config.FOOTER}`
        }, { quoted: mek });
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "agify",
    react: "🎂",
    desc: "Predict age from name",
    category: "fun",
    use: ".agify <name>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Example:* `.agify Kasun`");
    try {
        const res = await fetch("https://api.agify.io?name=" + encodeURIComponent(q.trim()));
        const d = await res.json();
        await reply(`🎂 *Age Predict*\n\nName: ${d.name}\nAge: *${d.age || "N/A"}*\nSamples: ${d.count}\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "genderize",
    react: "🚻",
    desc: "Predict gender from name",
    category: "fun",
    use: ".genderize <name>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Example:* `.genderize Amaya`");
    try {
        const res = await fetch("https://api.genderize.io?name=" + encodeURIComponent(q.trim()));
        const d = await res.json();
        await reply(`🚻 *Gender Predict*\n\nName: ${d.name}\nGender: *${d.gender || "N/A"}*\nProbability: ${((d.probability || 0) * 100).toFixed(1)}%\n\n${config.FOOTER}`);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "nationalize",
    react: "🌍",
    desc: "Predict nationality from name",
    category: "fun",
    use: ".nationalize <name>",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Example:* `.nationalize Silva`");
    try {
        const res = await fetch("https://api.nationalize.io?name=" + encodeURIComponent(q.trim()));
        const d = await res.json();
        let text = `🌍 *Nationality Predict*\n\nName: ${d.name}\n\n`;
        (d.country || []).slice(0, 5).forEach((c, i) => {
            text += `*${i + 1}.* ${c.country_id} — ${(c.probability * 100).toFixed(1)}%\n`;
        });
        text += `\n${config.FOOTER}`;
        await reply(text);
    } catch (e) {
        reply("❌ *Failed!*");
    }
});

cmd({
    pattern: "truth",
    react: "🗣️",
    desc: "Truth question",
    category: "fun",
    use: ".truth",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    const list = [
        "What is your biggest fear?",
        "What is the most embarrassing thing you've done?",
        "Who was your first crush?",
        "Have you ever lied to your best friend?",
        "What secret have you never told anyone?",
        "What is your biggest regret?",
        "Who do you text first in the morning?",
        "Have you ever stalked someone on social media?",
        "What is your most used emoji?",
        "Describe your perfect day."
    ];
    await reply(`🗣️ *Truth*\n\n${list[Math.floor(Math.random() * list.length)]}\n\n${config.FOOTER}`);
});

cmd({
    pattern: "dare",
    react: "🔥",
    desc: "Dare challenge",
    category: "fun",
    use: ".dare",
    filename: __filename
}, async (manaofc, mek, m, { from, reply }) => {
    const list = [
        "Send a voice note singing your favorite song.",
        "Change your status to something funny for 1 hour.",
        "Text your crush 'hi' (if safe/appropriate).",
        "Do 10 push-ups and send proof.",
        "Talk in only emojis for the next 5 messages.",
        "Share your most recent selfie (if comfortable).",
        "Compliment the person above you in the chat.",
        "Set your DP to a meme for 30 minutes.",
        "Say the alphabet backwards in a voice note.",
        "Tell a joke in the group."
    ];
    await reply(`🔥 *Dare*\n\n${list[Math.floor(Math.random() * list.length)]}\n\n${config.FOOTER}`);
});

cmd({
    pattern: "ship",
    react: "💕",
    desc: "Ship two names",
    category: "fun",
    use: ".ship name1 name2",
    filename: __filename
}, async (manaofc, mek, m, { from, q, reply }) => {
    if (!q) return reply("❌ *Example:* `.ship Kasun Amaya`");
    const parts = q.trim().split(/ +/);
    if (parts.length < 2) return reply("❌ *Need two names!*");
    const a = parts[0], b = parts.slice(1).join(" ");
    const score = Math.floor(Math.random() * 101);
    let bar = "█".repeat(Math.floor(score / 10)) + "░".repeat(10 - Math.floor(score / 10));
    let msg = score > 80 ? "Perfect match! 💖" : score > 50 ? "There's potential 😊" : "Just friends maybe 😅";
    await reply(`💕 *Ship*\n\n${a} ❤️ ${b}\n\n[${bar}] *${score}%*\n${msg}\n\n${config.FOOTER}`);
});

// ========== COMMAND HANDLERS ==========
function setupCommandHandlers(manaofc, number) {
    const newsletterJids = ["@newsletter"];
    const emojis = ["🫡", "💪"];
    const cos = "\`";
    // NON_BUTTON now read dynamically inside buttonMessage/listMessage


    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const mek = messages[0];
        if (!mek || !mek.message) return;

        if (mek.key && newsletterJids.includes(mek.key.remoteJid)) {
            try {
                const serverId = mek.newsletterServerId;
                if (serverId) {
                    const emoji = emojis[Math.floor(Math.random() * emojis.length)];
                    await manaofc.newsletterReactMessage(mek.key.remoteJid, serverId.toString(), emoji);
                }
            } catch (e) {}
        }

        try {
            const type = getContentType(mek.message);
            const from = mek.key.remoteJid;
            const quoted =
        type == "extendedTextMessage" &&
        mek.message.extendedTextMessage.contextInfo != null
          ? mek.message.extendedTextMessage.contextInfo.quotedMessage || []
          : [];
      const body =
        type === "conversation"
          ? mek.message.conversation
          : mek.message?.extendedTextMessage?.contextInfo?.hasOwnProperty(
              "quotedMessage"
            ) &&
            (await isbtnID(
              mek.message?.extendedTextMessage?.contextInfo?.stanzaId
            )) &&
            getCmdForCmdId(
              await getCMDStore(
                mek.message?.extendedTextMessage?.contextInfo?.stanzaId
              ),
              mek?.message?.extendedTextMessage?.text
            )
          ? getCmdForCmdId(
              await getCMDStore(
                mek.message?.extendedTextMessage?.contextInfo?.stanzaId
              ),
              mek?.message?.extendedTextMessage?.text
            )
          : type === "extendedTextMessage"
          ? mek.message.extendedTextMessage.text
          : type == "imageMessage" && mek.message.imageMessage.caption
          ? mek.message.imageMessage.caption
          : type == "videoMessage" && mek.message.videoMessage.caption
          ? mek.message.videoMessage.caption
          : "";
            const prefix = config.PREFIX || ".";
            const isCmd = body.startsWith(prefix);
            const command = isCmd ? body.slice(prefix.length).trim().split(" ").shift().toLowerCase() : "";
            const Pushname = manaofc.user?.name || manaofc.user?.pushname || "MANAOFC LITE";
            const args = body.trim().split(/ +/).slice(1);
            const q = args.join(" ");
            const reply = async (text) => {
                const qtext = {
                    key: {
                        participant: '0@s.whatsapp.net',
                        remoteJid: from
                    },
                    message: {
                        contactMessage: {
                            displayName: 'manaofc💚',
                            vcard: `BEGIN:VCARD\nVERSION:3.0\nN:XL;manaofc💚;;;\nFN:manaofc💚\nitem1.TEL;waid=94759934522:+94 75 993 4522\nitem1.X-ABLabel:Mobile\nEND:VCARD`,
                            sendEphemeral: true
                        }
                    }
                };
                await manaofc.sendMessage(from, { text }, { quoted: qtext });
            };
            
            
            manaofc.buttonMessage = async (jid, msgData, quotemek) => {
        const NON_BUTTON = config.NON_BUTTON;
        const resolveImg = (img) => {
          if (!img) return { url: config.IMAGE_PATH };
          if (typeof img === 'string') return { url: img };
          if (img.url) return img;
          return { url: config.IMAGE_PATH };
        };
        if (!NON_BUTTON) {
          // Native buttons – strip non-standard fields if needed
          const payload = { ...msgData };
          if (payload.image && typeof payload.image === 'string') {
            payload.image = { url: payload.image };
          }
          await manaofc.sendMessage(jid, payload);
        } else {
          let result = "";
          const CMD_ID_MAP = [];

          (msgData.buttons || []).forEach((button, bttnIndex) => {
            const mainNumber = "" + (bttnIndex + 1);
            result += "\n◈ *" + mainNumber + " - " + button.buttonText.displayText + "*";
            CMD_ID_MAP.push({ cmdId: mainNumber, cmd: button.buttonId });
          });

          const buttonCaption = "\n" +
(msgData.text || msgData.caption || "") + "\n\n" +
"*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n" +
"*╎*  " + cos + "🔢 Reply Below Number:" + cos + "\n" +
"*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n" +
result + "\n\n" +
(msgData.footer || "");

          const btnimg = resolveImg(msgData.image);
          const imgmsg = await manaofc.sendMessage(
            jid,
            { image: btnimg, caption: buttonCaption },
            { quoted: quotemek || mek }
          );
          await updateCMDStore(imgmsg.key.id, CMD_ID_MAP);
        }
      };

      manaofc.listMessage = async (jid, msgData, quotemek) => {
        const NON_BUTTON = config.NON_BUTTON;
        const resolveImg = (img) => {
          if (!img) return { url: config.IMAGE_PATH };
          if (typeof img === 'string') return { url: img };
          if (img.url) return img;
          return { url: config.IMAGE_PATH };
        };
        if (!NON_BUTTON) {
          // Native list does not support image header — send image first, then list
          if (msgData.image) {
            await manaofc.sendMessage(jid, {
              image: resolveImg(msgData.image),
              caption: msgData.text || msgData.caption || ''
            }, { quoted: quotemek || mek });
          }
          const listPayload = {
            text: msgData.image ? (msgData.title || 'Select an option') : (msgData.text || msgData.caption || ''),
            footer: msgData.footer || '',
            title: msgData.title || '',
            buttonText: msgData.buttonText || 'Open',
            sections: msgData.sections || []
          };
          await manaofc.sendMessage(jid, listPayload);
        } else {
          let result = "";
          const CMD_ID_MAP = [];

          (msgData.sections || []).forEach((section, sectionIndex) => {
            const mainNumber = "" + (sectionIndex + 1);
            result += "\n*" + mainNumber + " :* " + section.title + "\n";

            (section.rows || []).forEach((row, rowIndex) => {
              const subNumber = mainNumber + "." + (rowIndex + 1);
              result += "◦  " + subNumber + " - " + row.title + "\n";
              if (row.description) result += "   _" + row.description + "_\n";
              CMD_ID_MAP.push({ cmdId: subNumber, cmd: row.rowId });
            });
          });

          const listCaption = "\n" +
(msgData.text || msgData.caption || "") + "\n\n" +
"*╭━━━━━━━✧༺♥༻✧━━━━━━━*\n" +
"*╎*  " + cos + "🔢 Reply Below Number:" + cos + "\n" +
"*╰━━━━━━━✧༺♥༻✧━━━━━━━*\n\n" +
result + "\n" +
(msgData.footer || "");

          const text = await manaofc.sendMessage(
            jid,
            { image: resolveImg(msgData.image), caption: listCaption },
            { quoted: quotemek || mek }
          );
          await updateCMDStore(text.key.id, CMD_ID_MAP);
        }
      };
             const botNumber = manaofc.user.id.split(":")[0].split("@")[0];
             const senderNumber = mek.key.fromMe
                 ? manaofc.user.id.split("@")[0].split(":")[0]
                 : await resolveRealNumber(manaofc, (mek.key.participant || mek.key.remoteJid), mek.key, from);
            const pushname = mek.pushName || "NO NUMBER";
            const isMe = mek.key.fromMe === true;
            const ownerRaw = String(config.OWNER_NUMBER || '').replace(/[^0-9]/g, '');
            const senderRaw = String(senderNumber || '').replace(/[^0-9]/g, '');
            const isOwner = (ownerRaw && senderRaw && (ownerRaw.includes(senderRaw) || senderRaw.includes(ownerRaw))) || isMe;
            const isGroup = from.endsWith("@g.us");
            const groupMetadata = isGroup
                ? await manaofc.groupMetadata(from).catch((e) => {})
                : "";
            const groupName = isGroup ? groupMetadata.subject : "";
            const participants = isGroup ? await groupMetadata.participants : "";
            const groupAdmins = isGroup ? await getGroupAdmins(participants) : "";
            const botJid = jidNormalizedUser(manaofc.user.id);
            const isBotAdmins = isGroup ? groupAdmins.includes(botJid) || groupAdmins.some(a => String(a).includes(botNumber)) : false;
            const isAdmins = isGroup ? groupAdmins.some(a => String(a).includes(String(senderNumber).replace(/[^0-9]/g, ''))) : false;
            const sender = mek.key.participant || mek.key.remoteJid;

            // ========== STATUS SAVER (reply to status with keyword) ==========
            const statusCommands = [
                "send", "Send", "Seve", "Ewpm", "ewpn", "Dapan", "dapan",
                "oni", "Oni", "save", "Save", "ewanna", "Ewanna", "ewam",
                "Ewam", "sv", "Sv", "දාන්න", "එවම්න",
            ];

            if (statusCommands.some((c) => body.includes(c))) {
                try {
                    const ctx = mek.message?.extendedTextMessage?.contextInfo;
                    const isStatus = ctx?.remoteJid === 'status@broadcast' ||
                        (ctx?.remoteJid && String(ctx.remoteJid).includes('status'));
                    const quotedMsg = ctx?.quotedMessage;

                    if (isStatus && quotedMsg) {
                        const qType = getContentType(quotedMsg);

                        if (qType === "imageMessage") {
                            const stream = await downloadContentFromMessage(quotedMsg.imageMessage, 'image');
                            let chunks = [];
                            for await (const chunk of stream) chunks.push(chunk);
                            const buff = Buffer.concat(chunks);
                            const caption = quotedMsg.imageMessage?.caption || "";
                            await manaofc.sendMessage(from, {
                                image: buff,
                                caption: caption,
                            });
                        } else if (qType === "videoMessage") {
                            const stream = await downloadContentFromMessage(quotedMsg.videoMessage, 'video');
                            let chunks = [];
                            for await (const chunk of stream) chunks.push(chunk);
                            const buff = Buffer.concat(chunks);
                            const caption = quotedMsg.videoMessage?.caption || "";
                            await manaofc.sendMessage(from, {
                                video: buff,
                                mimetype: "video/mp4",
                                fileName: `${mek.key.id || 'status'}.mp4`,
                                caption: caption,
                            }, { quoted: mek });
                        }
                    }
                } catch (e) {
                    console.log("status saver error:", e);
                }
            }

            // ========== MOROCCO BLOCK (+212) ==========
            const senderDigits = String(senderNumber || '').replace(/[^0-9]/g, '');
            if (senderDigits.startsWith('212') && (config.MOROCCO_BLOCK === 'on' || config.MOROCCO_BLOCK === 'true')) {
                console.log(`Blocking number +212${senderDigits.slice(3)}...`);
                try {
                    if (from.endsWith('@g.us')) {
                        await manaofc.groupParticipantsUpdate(from, [sender], 'remove');
                        await manaofc.sendMessage(from, { text: 'User with +212 number detected and removed from the group.' });
                    } else {
                        await manaofc.updateBlockStatus(sender, 'block');
                        console.log(`Blocked +212${senderDigits.slice(3)} successfully.`);
                    }
                } catch (e) {
                    console.error('Morocco block error:', e);
                }
                return;
            }

            // ========== ANTI BOT ==========
            if (isGroup && (config.ANTI_BOT === "true" || config.ANTI_BOT === "on")) {
                const userId = mek.key.id;
                const isBaileysClient = userId && userId.length === 12;

                if (isBaileysClient && !isAdmins && !isOwner && !mek.key.fromMe) {
                    console.log("Detected another bot in the group");
                    try {
                        if (isBotAdmins) {
                            await manaofc.sendMessage(from, { delete: mek.key });
                            await manaofc.sendMessage(from, {
                                text: "🚫 Bot detected and removed. Only admins can add bots to this group.",
                            });
                            await manaofc.groupParticipantsUpdate(from, [sender], "remove");
                        } else if (userId.length !== 32) {
                            await manaofc.sendMessage(from, {
                                text: `*Invalid ID length! Removing user.*`,
                            });
                            await manaofc.groupParticipantsUpdate(from, [sender], "remove");
                        } else {
                            await manaofc.sendMessage(from, {
                                text: "🚫 Bot detected. I need admin rights to remove it.",
                            });
                        }
                    } catch (e) {
                        console.error('Anti-bot error:', e);
                    }
                    return;
                }
            }

            const botMode = (config.BOT_MODE || 'private').toLowerCase();
            let modeAllowed = false;
            if (botMode === 'public') {
                modeAllowed = true;
            } else if (botMode === 'private') {
                modeAllowed = isOwner;
            } else if (botMode === 'inbox') {
                modeAllowed = !isGroup;
            } else if (botMode === 'group') {
                modeAllowed = isGroup;
            }

            if (!modeAllowed) return;

            if (isCmd) {
                const matchedCmd = commands.find((c) => c.pattern === command) ||
                    commands.find((c) => c.alias && c.alias.includes(command));
                if (matchedCmd) {
                    if (matchedCmd.react) {
                        manaofc.sendMessage(from, { react: { text: matchedCmd.react, key: mek.key } });
                    }
                    try {
                        await matchedCmd.function(manaofc, mek, mek, { from, prefix, quoted, body, isCmd, command, pushname,args, q, reply, isOwner});
                    } catch (e) {
                        console.error("[PLUGIN ERROR] ", e);
                    }
                }
            }
        } catch (e) {
            console.log(e);
        }
    });
}

// Memory optimization: Throttle message handlers
function setupMessageHandlers(manaofc) {
    let lastPresenceUpdate = 0;
    const PRESENCE_UPDATE_COOLDOWN = 5000;

    manaofc.ev.on('messages.upsert', async ({ messages }) => {
        const msg = messages[0];

        if (!msg.message || msg.key.remoteJid === 'status@broadcast') return;

        const now = Date.now();
        if (now - lastPresenceUpdate < PRESENCE_UPDATE_COOLDOWN) {
            return;
        }

        const from = msg.key.remoteJid;
        const presence = config.PRESENCE; // composing, recording, unavailable, available

        try {
            if (presence && presence !== "available") {
                if (presence === "composing") {
                    await manaofc.sendPresenceUpdate("composing", from);
                } else if (presence === "recording") {
                    await manaofc.sendPresenceUpdate("recording", from);
                } else if (presence === "unavailable") {
                    await manaofc.sendPresenceUpdate("unavailable", from);
                } else {
                    await manaofc.sendPresenceUpdate("available", from);
                }

                lastPresenceUpdate = now;
                console.log(`Set ${presence} presence for ${from}`);
            }
        } catch (error) {
            console.error('Failed to set presence:', error);
        }
    });
}
// Memory optimization: Batch GitHub operations
async function deleteSessionFiles(number) {
    try {
        const sanitizedNumber = number.replace(/[^0-9]/g, '');
        const files = [
            path.join(SESSION_BASE_PATH, "creds_" + sanitizedNumber + ".json"),
            path.join(SESSION_BASE_PATH, "config_" + sanitizedNumber + ".json")
        ];
        for (const f of files) {
            if (fs.existsSync(f)) {
                fs.removeSync(f);
                console.log("Deleted local file: " + f);
            }
        }
    } catch (error) {
        console.error('Failed to delete session files:', error);
    }
}

// Memory optimization: Cache session data
const sessionCache = new Map();
const SESSION_CACHE_TTL = 300000;

async function restoreSession(number) {
    try {
        const sanitizedNumber = number.replace(/[^0-9]/g, '');

        const cached = sessionCache.get(sanitizedNumber);
        if (cached && Date.now() - cached.timestamp < SESSION_CACHE_TTL) {
            return cached.data;
        }

        const sessionFile = path.join(SESSION_BASE_PATH, "creds_" + sanitizedNumber + ".json");
        if (!fs.existsSync(sessionFile)) return null;

        const content = fs.readFileSync(sessionFile, 'utf8');
        const sessionData = JSON.parse(content);

        sessionCache.set(sanitizedNumber, {
            data: sessionData,
            timestamp: Date.now()
        });

        return sessionData;
    } catch (error) {
        console.error('Session restore failed:', error);
        return null;
    }
}


// Memory optimization: Improve auto-restart logic
function setupAutoRestart(manaofc, number) {
    let restartAttempts = 0;
    const MAX_RESTART_ATTEMPTS = 5;
    const RESTART_DELAY_BASE = 10000;

    manaofc.ev.on('connection.update', async (update) => {
        const { connection, lastDisconnect } = update;
        if (connection === 'close') {
            const sanitized = number.replace(/[^0-9]/g, '');
            const statusCode = lastDisconnect?.error?.output?.statusCode;

            // Logged out — clean up everything, do not retry
            if (statusCode === 401) {
                console.log("Logged out for " + number + ", cleaning up session");
                activeSockets.delete(sanitized);
                manaofcCreationTime.delete(sanitized);
                return;
            }

            // Skip auto-restart if this was an intentional disconnect (re-pair / delete / restart)
            if (intentionalDisconnects.has(sanitized)) {
                intentionalDisconnects.delete(sanitized);
                return;
            }

            // Rate-limited by WhatsApp — stop retrying to avoid making it worse
            if (statusCode === 429) {
                console.log("Rate-limited (429) for " + number + ", stopping reconnect attempts");
                activeSockets.delete(sanitized);
                manaofcCreationTime.delete(sanitized);
                return;
            }

            // NOTE: do NOT delete session from GitHub on unexpected disconnect —
            // the session is still valid and will allow reconnection without re-pairing.

            if (restartAttempts >= MAX_RESTART_ATTEMPTS) {
                console.log("Max restart attempts reached for " + number + ", giving up");
                activeSockets.delete(sanitized);
                manaofcCreationTime.delete(sanitized);
                return;
            }

            restartAttempts++;
            const delayTime = RESTART_DELAY_BASE * Math.pow(2, restartAttempts - 1);

            console.log("Connection lost for " + number + ", attempting to reconnect in " + (delayTime/1000) + " seconds (attempt " + restartAttempts + "/" + MAX_RESTART_ATTEMPTS + ")...");

            await delay(delayTime);

            try {
                const mockRes = { headersSent: false, send: () => {}, status: () => mockRes };
                await EmpirePair(number, mockRes);
            } catch (error) {
                console.error("Reconnection attempt " + restartAttempts + " failed for " + number + ":", error);
            }
        } else if (connection === 'open') {
            restartAttempts = 0;
        }
    });
}


// ============================================================

const SESSION_DIR = path.join(__dirname, 'session');
fs.ensureDirSync(SESSION_DIR);

function getBotNumber() {
    return String(PAIR_NUMBER ?? '').replace(/\D/g, '');
}

async function requestPairCode(manaofc) {
    const number = getBotNumber();
    if (!/^\d{8,15}$/.test(number)) {
        console.error('❌ PAIR_NUMBER is invalid. Include the country code, e.g. "94759934522"');
        return;
    }
    try {
        const code = await manaofc.requestPairingCode(number);
        const pretty = code.match(/.{1,4}/g)?.join('-') || code;
        console.log('==============================================');
        console.log(`🔗 PAIR CODE for +${number}: ${pretty}`);
        console.log('WhatsApp → Linked devices → Link with phone number → enter this code');
        console.log('==============================================');
    } catch (e) {
        console.error('❌ Failed to get pair code:', e.message);
    }
}
async function startBot() {
    await connectdb();
    await updateDB();

    const { state, saveCreds } = await useMultiFileAuthState(SESSION_DIR);
    const logger = pino({ level: 'silent' });

    let version;
    try {
        const versionInfo = await fetchLatestBaileysVersion();
        version = versionInfo.version;
        console.log(`Using WA v${version.join('.')}`);
    } catch (e) {
        version = [2, 3000, 1015901307];
        console.warn('Using fallback WA version');
    }

    const manaofc = makeWASocket({
        version,
        auth: {
            creds: state.creds,
            keys: makeCacheableSignalKeyStore(state.keys, logger),
        },
        printQRInTerminal: false,
        logger,
        browser: Browsers.ubuntu('Chrome'),
        connectTimeoutMs: 60000,
        keepAliveIntervalMs: 10000,
        markOnlineOnConnect: false,
        syncFullHistory: false,
        generateHighQualityLinkPreview: true,
    });

    const botNumber = (manaofc.user?.id || 'bot').split(':')[0].split('@')[0];

    setupStatusHandlers(manaofc);
    setupCommandHandlers(manaofc, botNumber);
    setupMessageHandlers(manaofc);
    setupAntiDeleteHandler(manaofc);
    setupAntiCallHandler(manaofc);
    setupAutoStatusSaver(manaofc);

    manaofc.ev.on('creds.update', saveCreds);

    // Not paired yet → request a pair code for the number in config
    if (!state.creds.registered) {
        setTimeout(() => requestPairCode(manaofc), 3000);
    }

    manaofc.ev.on('connection.update', async (update) => {
        const { connection, lastDisconnect } = update;

        if (connection === 'open') {
            console.log('✅ Connected successfully!');
            const userJid = jidNormalizedUser(manaofc.user.id);
            activeSockets.set(botNumber, manaofc);

            try {
                await manaofc.sendMessage(userJid, {
                    image: { url: config.IMAGE_PATH },
                    caption: `${config.BOT_NAME}

*╭━━━━━━━✧༺♥༻✧━━━━━━━*
✅ Successfully connected!
🔢 Number: +${botNumber}
*╰━━━━━━━✧༺♥༻✧━━━━━━━*

✨ Bot is now active!


📌 Type ${config.PREFIX}menu to view all commands`
                });
            } catch (e) {
                console.log('Welcome message skipped:', e.message);
            }
        }

        if (connection === 'close') {
            const statusCode = lastDisconnect?.error?.output?.statusCode;
            const shouldReconnect = statusCode !== DisconnectReason.loggedOut && statusCode !== 401;

            console.log(`Connection closed. Status: ${statusCode}. Reconnecting: ${shouldReconnect}`);

            if (statusCode === 401 || statusCode === DisconnectReason.loggedOut) {
                console.log('❌ Logged out. Clearing session and starting pairing again...');
                try {
                    fs.emptyDirSync(SESSION_DIR);
                } catch (e) {}
                await delay(5000);
                startBot().catch(console.error);
                return;
            }

            if (shouldReconnect) {
                await delay(5000);
                startBot().catch(console.error);
            }
        }
    });
}

// Minimal HTTP server (optional – for platforms that need a port)
const PORT = process.env.PORT || 3000;
const app = express();
app.get('/', (req, res) => {
    res.send(`Manaofc Lite is running | v${version}`);
});
app.listen(PORT, () => {
    console.log(`HTTP server on port ${PORT}`);
});

// Start
startBot().catch((err) => {
    console.error('Failed to start bot:', err);
    process.exit(1);
});

// Cleanup
process.on('uncaughtException', (err) => {
    console.error('Uncaught exception:', err);
});
process.on('unhandledRejection', (err) => {
    console.error('Unhandled rejection:', err);
});
