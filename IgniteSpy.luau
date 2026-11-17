-- CONFIG
local function boot()
assert(type(getgenv) == "function", "getgenv indisponível")
local env = getgenv()
local previous = rawget(env, "IgniteSpy") or rawget(env, "RemoteSpy")
if type(previous) == "table" and type(previous.unload) == "function" then
    local ok, result, reason = pcall(previous.unload)
    assert(ok and result ~= false, "Unload anterior falhou: " .. tostring(reason or result))
end
local useHook = type(hookmetamethod) == "function"
local C = {entries = 500, queue = 500, depth = 4, fields = 60, nodes = 800,
    string = 200, window = 2, threshold = 50, literalTables = 256,
    literalFields = 4096, literalBytes = 1000000,
    windowScale = 0.78, windowMaxWidth = 860, windowMaxHeight = 760, titleHeight = 40, catalogue = 1200}
local methods = {FireServer = true, InvokeServer = true, Fire = true, Invoke = true}
local classes = {RemoteEvent = "FireServer", UnreliableRemoteEvent = "FireServer",
    RemoteFunction = "InvokeServer", BindableEvent = "Fire", BindableFunction = "Invoke"}
local colors = {string = "85DB9D", number = "F4D477", boolean = "C6A1F6",
    ["nil"] = "9BA5B5", Instance = "70DDE8", table = "B1BCDA",
    other = "EAA887", error = "F18C99"}
local spy = {enabled = true, follow = true, ignore = {}, blocked = {}, ignoreNames = {}, blockedNames = {},
    spoofing = setmetatable({}, {__mode = "k"})}
local alive, restored, installed = true, false, false
local oldNamecall, hook, rawMT, installHook, unload
local pathCache = setmetatable({}, {__mode = "k"})
local connections, entries, rates, dirty = {}, {}, {}, {}
local queue, qHead, qTail, workerRunning = {}, 1, 0, false
local total, dropped, epoch, serial = 0, 0, 0, 0
local started = os.clock()
local gui, window, list, detail, modal, argsLabel, metaLabel, codeBox
local titleLabel, statusLabel, pauseButton, blockButton, ignoreButton, callButton
local selected, editing, query, busy = nil, nil, "", false
local setStatus, renderEntry, selectEntry, refreshActions, openSpoof, refreshFilter
local setSource, updateRow, runSelected, executeSpoof
local codeLines, codeScroll, body, ignoreNameButton, blockNameButton
local sourceText, sourceReady = "", false
local layoutEntries, statsLabel, emptyLabel
local layoutDirty, logFailures = false, 0
local ROW_HEIGHT, ROW_GAP = 52, 6
local identityGetter = getthreadidentity or getidentity
local identitySetter = setthreadidentity or setidentity
local copyDialog, copyBox, searchBox, followButton, runButton, modeLabel
local showCopyDialog, cancelReplay
local documentMode, documentRevision, runToken = "call", 0, 0
local inflightThread, pendingScript = nil, false
local scriptThread, scriptToken, cancelScriptLoad = nil, 0, nil
local ui = {pane = "list", filter = "all", filterButtons = {}, narrow = false}
ui.source, ui.actionGroup = "calls", "code"
ui.actionGroups, ui.actionTabs, ui.actionButtons = {}, {}, {}
local catalogue, catalogueIndex, nativeHooks = {}, setmetatable({}, {__mode = "k"}), {}
local retiredRemotes = {}
local insideOriginal = setmetatable({}, {__mode = "k"})
local scanGame, registerRemote, chooseSource, setActionGroup, isReplayable
local scanning, discoveryGeneration = false, 0
spy.favorites = setmetatable({}, {__mode = "k"})
spy.remotes = catalogue
spy.coverage = {namecall = false, direct = 0, incoming = 0, discovered = 0, nativeErrors = {}}
spy.startup = {ready = false, phase = "config", warnings = {}}
local responsiveLayout, matchesEntry
local uiIdentity
if type(identityGetter) == "function" then
    local ok, identity = pcall(identityGetter)
    if ok and type(identity) == "number" then uiIdentity = identity end
end
spy.version = "2.4.2"
spy.name = "ignite Spy"

-- UTILS
local function get(object, key)
    local ok, value = pcall(function() return object[key] end)
    if ok then return value end
end
local function set(object, properties)
    if not object then return end
    for key, value in pairs(properties) do
        pcall(function() object[key] = value end)
    end
end
local function call(object, method, ...)
    local packed = table.pack(...)
    return pcall(function()
        return object[method](object, table.unpack(packed, 1, packed.n))
    end)
end
local function destroy(object)
    if object then call(object, "Destroy") end
end
local function disconnect(bucket)
    for _, connection in ipairs(bucket) do
        pcall(function() connection:Disconnect() end)
    end
    table.clear(bucket)
end
local function on(object, event, callback, bucket)
    local signal = get(object, event)
    local connection = signal:Connect(function(...)
        if not alive then return end
        local ok, err = pcall(callback, ...)
        if not ok and setStatus then setStatus("Erro: " .. tostring(err)) end
    end)
    table.insert(bucket or connections, connection)
    return connection
end
local function make(class, properties, parent)
    local object = Instance.new(class)
    local ok, err = pcall(function()
        for key, value in pairs(properties or {}) do object[key] = value end
        if parent then object.Parent = parent end
    end)
    if not ok then destroy(object) error(err, 0) end
    return object
end
local function getInfo(object)
    local cached = pathCache[object]
    if cached then return cached end
    local names, seen, cursor = {}, {}, object
    for _ = 1, 128 do
        if cursor == game or cursor == nil or seen[cursor] then break end
        seen[cursor] = true
        local name = get(cursor, "Name")
        if type(name) ~= "string" then break end
        table.insert(names, 1, name)
        cursor = get(cursor, "Parent")
    end
    local ok, full = call(object, "GetFullName")
    local path = ok and type(full) == "string" and full ~= "" and full
        or table.concat(names, ".")
    if path == "" then path = "<Instance indisponível>" end
    local info = {path = path, names = names, rooted = cursor == game}
    pathCache[object] = info
    return info
end
local function resolve(info)
    assert(info.rooted, "Instance fora do DataModel")
    local cursor = game
    for _, name in ipairs(info.names) do
        local ok, children = call(cursor, "GetChildren")
        assert(ok, "Não foi possível resolver " .. info.path)
        local found
        for _, child in ipairs(children) do
            if get(child, "Name") == name then
                assert(found == nil, "Path ambíguo: " .. info.path)
                found = child
            end
        end
        assert(found, "Instance removida ou renomeada: " .. info.path)
        cursor = found
    end
    return cursor
end
local function keyFor(path, method) return path .. "|" .. method end
function spy.addIgnore(path, method) spy.ignore[keyFor(path, method)] = true end
function spy.addBlock(path, method) spy.blocked[keyFor(path, method)] = true end
local function quote(value)
    local valid, length = pcall(utf8.len, value)
    if valid and length then return string.format("%q", value) end
    local parts = {'"'}
    for index = 1, #value do
        local byte = value:byte(index)
        parts[#parts + 1] = byte >= 32 and byte <= 126 and byte ~= 34 and byte ~= 92
            and string.char(byte) or ("\\" .. string.format("%03d", byte))
    end
    parts[#parts + 1] = '"'
    return table.concat(parts)
end
local function escape(value)
    return (value:gsub("&", "&amp;"):gsub("<", "&lt;"):gsub(">", "&gt;")
        :gsub('"', "&quot;"):gsub("'", "&apos;"))
end
local function token(kind, value)
    return '<font color="#' .. (colors[kind] or colors.other) .. '">'
        .. escape(value) .. '</font>'
end
local function short(value, limit)
    if #value <= limit then return value end
    local cut = limit
    while cut > 0 do
        local ok, length = pcall(utf8.len, value:sub(1, cut))
        if ok and length then break end
        cut = cut - 1
    end
    return value:sub(1, cut) .. "…[+" .. (#value - cut) .. " bytes]"
end
local function snapshot(value)
    local ok, copy = pcall(table.clone, value)
    if ok then return copy end
    copy = {}
    for key, item in next, value do rawset(copy, key, item) end
    return copy
end

-- SERIALIZER
local function numberLiteral(value)
    if value ~= value then return "(0/0)" end
    if value == math.huge then return "math.huge" end
    if value == -math.huge then return "-math.huge" end
    if value == 0 and 1 / value < 0 then return "-0.0" end
    return string.format("%.17g", value)
end
local function instanceLiteral(value)
    local info = getInfo(value)
    assert(info.rooted, "Instance sem path resolvível: " .. info.path)
    local names = {}
    for index, name in ipairs(info.names) do names[index] = quote(name) end
    return '(function() local ok,v=pcall(function() local p=game '
        .. 'for _,n in ipairs({' .. table.concat(names, ",") .. '}) do '
        .. 'local f for _,c in ipairs(p:GetChildren()) do if c.Name==n then '
        .. 'assert(not f,"Path ambiguo");f=c end end '
        .. 'p=assert(f,"Instance ausente") end return p end) '
        .. 'assert(ok,v);return v end)()'
end
local atom
atom = function(value)
    local kind = typeof(value)
    if kind == "nil" then return "nil" end
    if kind == "boolean" then return value and "true" or "false" end
    if kind == "number" then return numberLiteral(value) end
    if kind == "string" then return quote(value) end
    if kind == "buffer" then
        assert(type(buffer) == "table" and type(buffer.tostring) == "function", "buffer.tostring indisponível")
        return "buffer.fromstring(" .. quote(buffer.tostring(value)) .. ")"
    end
    if kind == "Instance" then return instanceLiteral(value) end
    if kind == "EnumItem" then return tostring(value) end
    local function ctor(name, values)
        local parts = {}
        for index, item in ipairs(values) do parts[index] = atom(item) end
        return name .. "(" .. table.concat(parts, ", ") .. ")"
    end
    if kind == "Vector2" then return ctor("Vector2.new", {value.X, value.Y}) end
    if kind == "Vector3" then return ctor("Vector3.new", {value.X, value.Y, value.Z}) end
    if kind == "Color3" then return ctor("Color3.new", {value.R, value.G, value.B}) end
    if kind == "UDim" then return ctor("UDim.new", {value.Scale, value.Offset}) end
    if kind == "UDim2" then
        return ctor("UDim2.new", {value.X.Scale, value.X.Offset, value.Y.Scale, value.Y.Offset})
    end
    if kind == "CFrame" then return ctor("CFrame.new", {value:GetComponents()}) end
    if kind == "Rect" then return ctor("Rect.new", {value.Min, value.Max}) end
    if kind == "Ray" then return ctor("Ray.new", {value.Origin, value.Direction}) end
    if kind == "Region3" then
        local half = value.Size / 2
        return ctor("Region3.new", {value.CFrame.Position - half, value.CFrame.Position + half})
    end
    if kind == "NumberSequenceKeypoint" then
        return ctor("NumberSequenceKeypoint.new", {value.Time, value.Value, value.Envelope})
    end
    if kind == "ColorSequenceKeypoint" then
        return ctor("ColorSequenceKeypoint.new", {value.Time, value.Value})
    end
    if kind == "NumberSequence" or kind == "ColorSequence" then
        local parts = {}
        for index, point in ipairs(value.Keypoints) do parts[index] = atom(point) end
        return kind .. ".new({" .. table.concat(parts, ", ") .. "})"
    end
    error("Tipo sem literal reproduzível: " .. kind, 0)
end
local function displayArguments(args, preview)
    local seen, nextID, nodes = {}, 0, 0
    local serialize
    serialize = function(value, depth)
        local ok, plain, rich = pcall(function()
            nodes = nodes + 1
            if nodes > (preview and 40 or C.nodes) then return "<limite>", token("error", "<limite>") end
            local kind = typeof(value)
            if kind == "table" then
                if seen[value] then
                    local text = "<ref #" .. seen[value] .. ">"
                    return text, token("table", text)
                end
                nextID = nextID + 1
                seen[value] = nextID
                if depth >= (preview and 2 or C.depth) then return "{…}", token("table", "{…}") end
                local plainParts, richParts, count = {}, {}, 0
                for key, item in next, snapshot(value) do
                    count = count + 1
                    if count > (preview and 4 or C.fields) then
                        table.insert(plainParts, "…[mais campos]")
                        table.insert(richParts, token("table", "…[mais campos]"))
                        break
                    end
                    local kp, kr = serialize(key, depth + 1)
                    local vp, vr = serialize(item, depth + 1)
                    table.insert(plainParts, "[" .. kp .. "]=" .. vp)
                    table.insert(richParts, "[" .. kr .. "]=" .. vr)
                end
                return "{" .. table.concat(plainParts, ", ") .. "}",
                    "{" .. table.concat(richParts, ", ") .. "}"
            end
            local text
            if kind == "string" then text = quote(short(value, preview and 64 or C.string))
            elseif kind == "Instance" then
                text = (get(value, "ClassName") or "Instance") .. " <" .. getInfo(value).path .. ">"
            elseif kind == "function" then
                local worked, source = pcall(function() return debug.info(value, "s") end)
                text = "function <" .. (worked and type(source) == "string" and source or "?") .. ">"
            elseif kind == "thread" or kind == "userdata" then text = "<" .. kind .. ">"
            elseif kind == "buffer" then text = "<buffer " .. buffer.len(value) .. " bytes>"
            else
                local worked, literal = pcall(atom, value)
                text = worked and literal or ("<" .. kind .. ">")
            end
            return text, token(kind, text)
        end)
        if ok then return plain, rich end
        return "<erro de serialização>", token("error", "<erro de serialização>")
    end
    local plain, rich = {}, {}
    for index = 1, math.min(args.n, preview and 3 or args.n) do
        local p, r = serialize(args[index], 0)
        plain[index], rich[index] = "[" .. index .. "] " .. p, "[" .. index .. "] " .. r
    end
    if preview and args.n > 3 then
        plain[#plain + 1], rich[#rich + 1] = "…[mais argumentos]", "…[mais argumentos]"
    end
    if args.n == 0 then return "(sem argumentos)", "(sem argumentos)" end
    return table.concat(plain, "\n"), table.concat(rich, "\n")
end
local function literalArguments(args)
    local ids, tables, records, fieldCount = {}, {}, {}, 0
    local function ref(value)
        if typeof(value) ~= "table" then return atom(value) end
        if not ids[value] then
            assert(#tables < C.literalTables, "Muitas tabelas para o editor")
            tables[#tables + 1] = value
            ids[value] = #tables
        end
        return "T[" .. ids[value] .. "]"
    end
    local values = {}
    for index = 1, args.n do values[index] = ref(args[index]) end
    local index = 1
    while index <= #tables do
        local fields = {}
        for key, value in next, snapshot(tables[index]) do
            fieldCount = fieldCount + 1
            assert(fieldCount <= C.literalFields, "Muitos campos para o editor")
            fields[#fields + 1] = {ref(key), ref(value)}
        end
        records[index] = fields
        index = index + 1
    end
    local lines = {"(function()", "local T = {}"}
    for i = 1, #tables do lines[#lines + 1] = "T[" .. i .. "] = {}" end
    for i, fields in ipairs(records) do
        for _, field in ipairs(fields) do
            lines[#lines + 1] = "T[" .. i .. "][" .. field[1] .. "] = " .. field[2]
        end
    end
    if args.n > 0 then lines[#lines + 1] = "return " .. table.concat(values, ", ") end
    lines[#lines + 1] = "end)()"
    local text = table.concat(lines, "\n")
    assert(#text <= C.literalBytes, "Literal maior que 1 MB")
    return text
end
local function readableArguments(args)
    local seen, fields, tables = {}, 0, 0
    local pretty
    pretty = function(value, depth)
        if typeof(value) ~= "table" then return atom(value) end
        assert(not seen[value] and depth <= 8, "Usar serialização de referências")
        seen[value], tables = true, tables + 1
        assert(tables <= C.literalTables, "Muitas tabelas")
        local parts, padding = {}, string.rep("    ", depth)
        for key, item in next, snapshot(value) do
            fields = fields + 1
            assert(fields <= C.literalFields, "Muitos campos")
            parts[#parts + 1] = padding .. "    [" .. pretty(key, depth + 1) .. "] = " .. pretty(item, depth + 1)
        end
        if #parts == 0 then return "{}" end
        return "{\n" .. table.concat(parts, ",\n") .. "\n" .. padding .. "}"
    end
    local ok, text = pcall(function()
        local values = {}
        for index = 1, args.n do values[index] = "    " .. pretty(args[index], 1) end
        local result = table.concat(values, ",\n")
        assert(#result <= C.literalBytes, "Literal muito grande")
        return result
    end)
    if ok then return text end
    -- Ciclos e referências compartilhadas mantêm o construtor de grafo completo.
    return literalArguments(args)
end

-- HOOK
local function removeEntry(entry)
    entry.dead = true
    disconnect(entry.connections)
    destroy(entry.row)
    layoutDirty = true
    if entry.bucket.group == entry then entry.bucket.group = nil end
    if selected == entry then
        selected, editing = nil, nil
        set(modal, {Visible = false})
        set(copyDialog, {Visible = false})
        if setSource then setSource("-- Selecione uma chamada na lista.") end
    end
end
local function newEntry(job, collapsed)
    if not alive or job.epoch ~= epoch then return end
    serial = serial + 1
    local plain, rich = displayArguments(job.args)
    local _, summary = displayArguments(job.args, true)
    local entry = {remote = job.remote, info = job.info, key = job.key,
        method = job.method, class = job.class, args = job.args, at = job.at,
        blocked = job.blocked, plain = plain, rich = rich, summary = summary, bucket = job.bucket,
        collapsed = collapsed, connections = {}, order = serial, callerScript = job.callerScript,
        kind = "call", direction = job.direction, observation = job}
    entry.name = entry.info.names[#entry.info.names] or entry.info.path
    entry.search = string.lower(entry.info.path .. "\n" .. entry.method .. "\n" .. plain)
    local ok, err = pcall(renderEntry, entry)
    if not ok then
        disconnect(entry.connections)
        destroy(entry.row)
        error(err, 0)
    end
    if collapsed then
        for i = #entries, 1, -1 do
            if entries[i].bucket == job.bucket then
                removeEntry(entries[i])
                table.remove(entries, i)
            end
        end
    end
    entries[#entries + 1] = entry
    if collapsed then job.bucket.group = entry end
    layoutDirty = true
    while #entries > C.entries do removeEntry(table.remove(entries, 1)) end
    if not selected and (not matchesEntry or matchesEntry(entry)) then pcall(selectEntry, entry, false) end
end
local function process(job)
    if not alive or job.epoch ~= epoch then return end
    job.bucket.pending = false
    if job.bucket.collapsed then
        if not job.bucket.group or job.bucket.group.dead then newEntry(job, true) end
    else newEntry(job, false) end
end
local function enqueue(job)
    if qTail - qHead + 1 >= C.queue then
        local discarded = queue[qHead]
        if discarded then discarded.bucket.pending = false end
        queue[qHead], qHead, dropped = nil, qHead + 1, dropped + 1
    end
    qTail = qTail + 1
    queue[qTail] = job
end
local function pumpLogger()
    if workerRunning or qHead > qTail or not alive then return end
    workerRunning = true
    -- A rotina nasce na conexão da UI, preservando o contexto do executor.
    task.defer(function()
        if uiIdentity and type(identitySetter) == "function" then pcall(identitySetter, uiIdentity) end
        local processed = 0
        while alive and qHead <= qTail do
            local item = queue[qHead]
            queue[qHead], qHead = nil, qHead + 1
            if item then
                local ok, err = pcall(process, item)
                if not ok then
                    logFailures = logFailures + 1
                    spy.lastError = tostring(err)
                    setStatus("Falha ao exibir chamada: " .. spy.lastError)
                end
            end
            processed = processed + 1
            if processed % 12 == 0 then
                if layoutDirty and layoutEntries then layoutEntries() end
                task.wait()
            end
        end
        if alive and layoutDirty and layoutEntries then layoutEntries() end
        if qHead > qTail then queue, qHead, qTail = {}, 1, 0 end
        workerRunning = false
    end)
end
local function capture(remote, method, class, args)
    local info = getInfo(remote)
    local key, now = keyFor(info.path, method), os.clock()
    local nameKey = keyFor(info.names[#info.names] or info.path, method)
    local incoming = method == "OnClientEvent"
    local blocked = not incoming and (spy.blocked[key] == true or spy.blockedNames[nameKey] == true)
    local known = catalogueIndex[remote]
    if known then
        known.activity = (known.activity or 0) + 1
        known.lastAt = now - started
        if not incoming then known.args, known.hasOutgoing, known.callSource = args, true, nil end
        dirty[known.bucket] = true
    end
    if not spy.enabled or spy.ignore[key] or spy.ignoreNames[nameKey] then return blocked end
    total = total + 1
    local bucket = rates[key]
    if not bucket or now - bucket.last > C.window then
        bucket = {times = {}, head = 1, tail = 0, total = 0, last = now}
        rates[key] = bucket
    end
    bucket.total, bucket.last = bucket.total + 1, now
    bucket.tail = bucket.tail + 1
    bucket.times[bucket.tail] = now
    while bucket.head <= bucket.tail and
        (now - bucket.times[bucket.head] > C.window or bucket.tail - bucket.head > C.threshold) do
        bucket.times[bucket.head] = nil
        bucket.head = bucket.head + 1
    end
    if bucket.tail - bucket.head + 1 > C.threshold then bucket.collapsed = true end
    if bucket.collapsed then
        dirty[bucket] = true
        if bucket.group and not bucket.group.dead then return blocked end
        if bucket.pending then return blocked end
        bucket.pending = true
    end
    local callerScript
    if not incoming and type(getcallingscript) == "function" then
        local ok, value = pcall(getcallingscript)
        if ok and typeof(value) == "Instance" then callerScript = value end
    end
    local job = {remote = remote, info = info, key = key, method = method, class = class,
        args = args, at = now - started, blocked = blocked, bucket = bucket, epoch = epoch,
        callerScript = callerScript, direction = incoming and "in"
            or (class == "BindableEvent" or class == "BindableFunction") and "local" or "out"}
    enqueue(job)
    return blocked, job
end
local function invokeOriginal(original, self, method, args, job)
    local thread, previous, began = coroutine.running(), insideOriginal[coroutine.running()], os.clock()
    insideOriginal[thread] = {remote = self, method = method}
    local result = table.pack(pcall(original, self, table.unpack(args, 1, args.n)))
    insideOriginal[thread] = previous
    if job then
        job.duration = os.clock() - began
        if result[1] then
            job.results = {n = result.n - 1}
            for index = 2, result.n do job.results[index - 1] = result[index] end
        else job.error = tostring(result[2]) end
    end
    if not result[1] then error(result[2], 0) end
    return table.unpack(result, 2, result.n)
end
installHook = function()
    assert(type(getnamecallmethod) == "function", "getnamecallmethod indisponível neste executor")
    local backup
    if type(getrawmetatable) == "function" then
        local found, mt = pcall(getrawmetatable, game)
        if found and type(mt) == "table" then
            local original = rawget(mt, "__namecall")
            if type(original) == "function" then rawMT, backup = mt, original end
        end
    end
    hook = function(self, ...)
        local method = getnamecallmethod()
        if not methods[method] or typeof(self) ~= "Instance" then return oldNamecall(self, ...) end
        if not alive or spy.spoofing[coroutine.running()] then return oldNamecall(self, ...) end
        local forwarding = insideOriginal[coroutine.running()]
        if forwarding and forwarding.remote == self and forwarding.method == method then return oldNamecall(self, ...) end
        local class = get(self, "ClassName")
        if classes[class] ~= method then return oldNamecall(self, ...) end
        local args = table.pack(...)
        local ok, blocked, job = pcall(capture, self, method, class, args)
        if ok and blocked then return nil end
        return invokeOriginal(oldNamecall, self, method, args, ok and job or nil)
    end
    if type(newcclosure) == "function" then
        local wrapped, closure = pcall(newcclosure, hook)
        if wrapped and type(closure) == "function" then hook = closure end
    end
    local nativeError
    if useHook then
        local ok, original = pcall(hookmetamethod, game, "__namecall", hook)
        if ok and type(original) == "function" then
            oldNamecall, installed = original, true
            spy.coverage.namecall = true
            return
        end
        nativeError = tostring(original)
    end
    if rawMT and type(setreadonly) == "function" and type(backup) == "function" then
        oldNamecall, useHook = backup, false
        setreadonly(rawMT, false)
        local ok, err = pcall(rawset, rawMT, "__namecall", hook)
        local locked, lockErr = pcall(setreadonly, rawMT, true)
        if not ok then error(err, 0) end
        installed = true
        if not locked then error(lockErr, 0) end
        spy.coverage.namecall = true
        return
    end
    if useHook and backup and rawget(rawMT, "__namecall") == hook then oldNamecall, installed = backup, true end
    error("Captura indisponível: " .. (nativeError or "hookmetamethod ou getrawmetatable + setreadonly necessários"), 0)
end
local function installDirectHooks()
    if type(hookfunction) ~= "function" then return end
    local installedTargets = {}
    for class, method in pairs(classes) do
        local object = Instance.new(class)
        local target = get(object, method)
        destroy(object)
        if type(target) == "function" then
            if installedTargets[target] then installedTargets[target].methods[method] = true
            else
                local record = {target = target, methods = {[method] = true}}
                local replacement = function(self, ...)
                    if not alive or spy.spoofing[coroutine.running()] or typeof(self) ~= "Instance" then return record.original(self, ...) end
                    local actualClass = get(self, "ClassName")
                    local actualMethod = classes[actualClass]
                    if not actualMethod or not record.methods[actualMethod] then return record.original(self, ...) end
                    local forwarding = insideOriginal[coroutine.running()]
                    if forwarding and forwarding.remote == self and forwarding.method == actualMethod then return record.original(self, ...) end
                    local args = table.pack(...)
                    local ok, blocked, job = pcall(capture, self, actualMethod, actualClass, args)
                    if ok and blocked then return nil end
                    return invokeOriginal(record.original, self, actualMethod, args, ok and job or nil)
                end
                if type(newcclosure) == "function" then
                    local wrapped, closure = pcall(newcclosure, replacement)
                    if wrapped and type(closure) == "function" then replacement = closure end
                end
                local ok, original = pcall(hookfunction, target, replacement)
                if ok and type(original) == "function" then
                    record.original = original
                    nativeHooks[#nativeHooks + 1], installedTargets[target] = record, record
                    spy.coverage.direct = spy.coverage.direct + 1
                else spy.coverage.nativeErrors[#spy.coverage.nativeErrors + 1] = class .. ": " .. tostring(original) end
            end
        end
    end
end
local function restoreDirectHooks()
    local failures, remaining = {}, 0
    for index = #nativeHooks, 1, -1 do
        local record = nativeHooks[index]
        if not record.restored then
            local ok, reason = pcall(hookfunction, record.target, record.original)
            if ok then record.restored = true
            else
                failures[#failures + 1] = tostring(reason)
                remaining = remaining + 1
            end
        end
    end
    spy.coverage.direct = remaining
    if remaining == 0 then table.clear(nativeHooks) end
    return #failures == 0, table.concat(failures, "; ")
end
function spy.enableDirect(enabled)
    if not alive then return false, "Spy descarregado" end
    if enabled == false then return restoreDirectHooks() end
    if spy.coverage.direct > 0 then return true end
    if type(hookfunction) ~= "function" then return false, "hookfunction indisponível neste executor" end
    local ok, reason = pcall(installDirectHooks)
    if not ok then return false, tostring(reason) end
    return spy.coverage.direct > 0, #spy.coverage.nativeErrors > 0 and table.concat(spy.coverage.nativeErrors, "; ") or ""
end
registerRemote = function(remote)
    if not alive or catalogueIndex[remote] or #catalogue >= C.catalogue then return end
    local class = get(remote, "ClassName")
    if not classes[class] then return end
    pathCache[remote] = nil
    local info = getInfo(remote)
    if not info.rooted then return end
    local record = {remote = remote, info = info, class = class, method = classes[class],
        name = info.names[#info.names] or info.path, key = keyFor(info.path, classes[class]),
        args = {n = 0}, at = os.clock() - started, kind = "remote", direction = "found",
        plain = "Ainda não houve envio capturado", rich = "", connections = {}, watchers = {}, bucket = {}}
    record.bucket.group = record
    record.search = string.lower(record.info.path .. "\n" .. class)
    catalogueIndex[remote], catalogue[#catalogue + 1] = record, record
    spy.coverage.discovered = #catalogue
    local signal = get(remote, "OnClientEvent")
    if (class == "RemoteEvent" or class == "UnreliableRemoteEvent") and signal then
        local ok, connection = pcall(function()
            return signal:Connect(function(...)
                if alive then pcall(capture, remote, "OnClientEvent", class, table.pack(...)) end
            end)
        end)
        if ok then
            record.watchers[#record.watchers + 1] = connection
            record.receives = true
            spy.coverage.incoming = spy.coverage.incoming + 1
        end
    end
    on(remote, "Changed", function(property)
        if property == "Name" or property == "Parent" then
            pathCache[remote] = nil
            record.info = getInfo(remote)
            record.name = record.info.names[#record.info.names] or record.info.path
            record.key, record.callSource = keyFor(record.info.path, record.method), nil
            record.search = string.lower(record.info.path .. "\n" .. record.class)
            layoutDirty = true
        end
    end, record.watchers)
    layoutDirty = true
end
scanGame = function()
    if scanning or not alive then return end
    scanning = true
    local generation = discoveryGeneration
    task.defer(function()
        local ok, descendants = call(game, "GetDescendants")
        if ok then
            for index, object in ipairs(descendants) do
                if not alive or generation ~= discoveryGeneration then break end
                pcall(registerRemote, object)
                if index % 80 == 0 then task.wait() end
            end
        end
        scanning = false
        if alive then setStatus(ok and (#catalogue .. " remotes encontrados no cliente") or "Não foi possível percorrer o DataModel") end
    end)
end
spy.scan = function() scanGame() end
local function startDiscovery()
    on(game, "DescendantAdded", function(object) pcall(registerRemote, object) end)
    on(game, "DescendantRemoving", function(object)
        local record = catalogueIndex[object]
        if not record then return end
        disconnect(record.watchers)
        record.dead = true
        retiredRemotes[#retiredRemotes + 1] = record
        layoutDirty = true
        catalogueIndex[object] = nil
        for index = #catalogue, 1, -1 do if catalogue[index] == record then table.remove(catalogue, index) break end end
        if record.receives then spy.coverage.incoming = math.max(0, spy.coverage.incoming - 1) end
        spy.coverage.discovered = #catalogue
    end)
    scanGame()
end

-- UI
local bg = Color3.fromRGB(13, 14, 21)
local panel, ink = Color3.fromRGB(22, 23, 34), Color3.fromRGB(239, 239, 248)
local editorBG = Color3.fromRGB(16, 18, 28)
local violet, border, muted = Color3.fromRGB(159, 91, 255), Color3.fromRGB(53, 54, 76), Color3.fromRGB(149, 151, 174)
local buttonBG = Color3.fromRGB(28, 29, 43)
local accents = {
    RemoteEvent = Color3.fromRGB(245, 236, 35),
    RemoteFunction = Color3.fromRGB(181, 107, 242),
    UnreliableRemoteEvent = Color3.fromRGB(255, 157, 63),
    BindableEvent = Color3.fromRGB(75, 213, 219),
    BindableFunction = Color3.fromRGB(105, 226, 168),
}
local semantic = {code = Color3.fromRGB(125, 182, 255), run = violet,
    ignore = Color3.fromRGB(244, 199, 96), block = Color3.fromRGB(245, 103, 121),
    tool = Color3.fromRGB(75, 213, 219)}
local function label(parent, text, position, size)
    return make("TextLabel", {BackgroundTransparency = 1, Text = text, TextColor3 = ink,
        TextSize = 14, Font = Enum.Font.Code, TextXAlignment = Enum.TextXAlignment.Left,
        TextYAlignment = Enum.TextYAlignment.Top, Position = position, Size = size,
        Visible = true, TextTransparency = 0, Active = false, Selectable = false, ZIndex = 23}, parent)
end
local function round(object, radius, color)
    make("UICorner", {CornerRadius = UDim.new(0, radius)}, object)
    if color then
        make("UIStroke", {Name = "Outline", ApplyStrokeMode = Enum.ApplyStrokeMode.Border,
            Color = color, Thickness = 1, Transparency = 0.15}, object)
    end
end
local function tintOutline(object, color, transparency)
    local ok, outline = call(object, "FindFirstChild", "Outline")
    if ok and outline then set(outline, {Color = color, Transparency = transparency or 0}) end
end
--[=[
Ícones Lucide; fontes e licença também acompanham o pacote.
ISC License

Copyright (c) 2026 Lucide Icons and Contributors

Permission to use, copy, modify, and/or distribute this software for any
purpose with or without fee is hereby granted, provided that the above
copyright notice and this permission notice appear in all copies.

THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

---

The following Lucide icons are derived from the Feather project:

airplay, alert-circle, alert-octagon, alert-triangle, aperture, arrow-down-circle, arrow-down-left, arrow-down-right, arrow-down, arrow-left-circle, arrow-left, arrow-right-circle, arrow-right, arrow-up-circle, arrow-up-left, arrow-up-right, arrow-up, at-sign, calendar, cast, check, chevron-down, chevron-left, chevron-right, chevron-up, chevrons-down, chevrons-left, chevrons-right, chevrons-up, circle, clipboard, clock, code, columns, command, compass, corner-down-left, corner-down-right, corner-left-down, corner-left-up, corner-right-down, corner-right-up, corner-up-left, corner-up-right, crosshair, database, divide-circle, divide-square, dollar-sign, download, external-link, feather, frown, hash, headphones, help-circle, info, italic, key, layout, life-buoy, link-2, link, loader, lock, log-in, log-out, maximize, meh, minimize, minimize-2, minus-circle, minus-square, minus, monitor, moon, more-horizontal, more-vertical, move, music, navigation-2, navigation, octagon, pause-circle, percent, plus-circle, plus-square, plus, power, radio, rss, search, server, share, shopping-bag, sidebar, smartphone, smile, square, table-2, tablet, target, terminal, trash-2, trash, triangle, tv, type, upload, x-circle, x-octagon, x-square, x, zoom-in, zoom-out

The MIT License (MIT) (for the icons listed above)

Copyright (c) 2013-present Cole Bemis

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.

]=]
local iconAssets = {nodes = setmetatable({}, {__mode = "k"}), rects = {
    ["copy"] = Vector2.new(0, 0),
    ["link"] = Vector2.new(64, 0),
    ["play"] = Vector2.new(128, 0),
    ["file-code"] = Vector2.new(192, 0),
    ["info"] = Vector2.new(256, 0),
    ["ban"] = Vector2.new(320, 0),
    ["search"] = Vector2.new(384, 0),
    ["star"] = Vector2.new(448, 0),
    ["trash"] = Vector2.new(0, 64),
    ["pencil"] = Vector2.new(64, 64),
    ["rotate-ccw"] = Vector2.new(128, 64),
    ["list-filter"] = Vector2.new(192, 64),
    ["code-xml"] = Vector2.new(256, 64),
    ["wrench"] = Vector2.new(320, 64),
    ["shield"] = Vector2.new(384, 64),
    ["flame"] = Vector2.new(448, 64),
    ["pause"] = Vector2.new(0, 128),
    ["minus"] = Vector2.new(64, 128),
    ["maximize"] = Vector2.new(128, 128),
    ["x"] = Vector2.new(192, 128),
    ["circle-question-mark"] = Vector2.new(256, 128),
    ["list"] = Vector2.new(320, 128),
    ["arrow-down-left"] = Vector2.new(384, 128),
    ["zap"] = Vector2.new(448, 128),
    ["radio"] = Vector2.new(0, 192),
    ["send"] = Vector2.new(64, 192),
    ["braces"] = Vector2.new(128, 192),
    ["eye-off"] = Vector2.new(192, 192),
    ["lock"] = Vector2.new(256, 192),
    ["layers"] = Vector2.new(320, 192),
    ["settings-2"] = Vector2.new(384, 192),
    ["refresh-cw"] = Vector2.new(448, 192),
}, file = "IgniteSpy_Icons_v2.png", bytes = 18031, image = nil}
spy.icons = {ready = false, source = "vector", message = "Ícones locais ativos", count = 32}
local function iconRect(kind)
    local aliases = {block = "ban", scan = "search", edit = "pencil", filter = "list-filter",
        reset = "rotate-ccw", script = "file-code", help = "circle-question-mark", close = "x", code = "code-xml"}
    return iconAssets.rects[aliases[kind] or kind] or iconAssets.rects.copy
end
local function useIconImage(node)
    if not iconAssets.image then return end
    set(node.image, {Image = iconAssets.image, ImageRectOffset = iconRect(node.kind), ImageRectSize = Vector2.new(64, 64)})
    if get(node.image, "IsLoaded") == true then set(node.fallback, {Visible = false}) end
end
local function startIcons()
    task.defer(function()
        if not alive then return end
        local assetFunction = type(getcustomasset) == "function" and getcustomasset or getsynasset
        if type(assetFunction) ~= "function" or type(writefile) ~= "function" then
            spy.icons.message = "Imagens precisam de writefile e getcustomasset; ícones locais ativos"
            return
        end
        local ok, result = pcall(function()
            local cached
            if type(readfile) == "function" then
                local read, bytes = pcall(readfile, iconAssets.file)
                cached = read and type(bytes) == "string" and #bytes == iconAssets.bytes and bytes:sub(1, 8) == "\137PNG\13\10\26\10"
            end
            if not cached then
                -- O atlas acompanha o script: uma única imagem, sem requisições por botão.
                local encoded = [=[
iVBORw0KGgoAAAANSUhEUgAAAgAAAAEACAMAAADyTj5VAAADAFBMVEX/////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////////////////8AAAC/
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
]=]
                local alphabet, digits, parts = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/", {}, {}
                for index = 1, #alphabet do digits[alphabet:sub(index, index)] = index - 1 end
                encoded = encoded:gsub("%s", "")
                for offset = 1, #encoded, 4 do
                    local a, b, c, d = encoded:sub(offset, offset), encoded:sub(offset + 1, offset + 1),
                        encoded:sub(offset + 2, offset + 2), encoded:sub(offset + 3, offset + 3)
                    local value = digits[a] * 262144 + digits[b] * 4096 + (digits[c] or 0) * 64 + (digits[d] or 0)
                    parts[#parts + 1] = string.char(math.floor(value / 65536) % 256)
                    if c ~= "=" then parts[#parts + 1] = string.char(math.floor(value / 256) % 256) end
                    if d ~= "=" then parts[#parts + 1] = string.char(value % 256) end
                end
                local bytes = table.concat(parts)
                assert(#bytes == iconAssets.bytes and bytes:sub(1, 8) == "\137PNG\13\10\26\10", "Atlas inválido")
                writefile(iconAssets.file, bytes)
            end
            local content = assetFunction(iconAssets.file)
            assert(type(content) == "string" and content ~= "", "getcustomasset não retornou uma imagem")
            return content
        end)
        if not alive then return end
        if not ok then spy.icons.message = "Falha nas imagens; ícones locais ativos: " .. tostring(result) return end
        iconAssets.image = result
        spy.icons.ready, spy.icons.source, spy.icons.message = true, "embedded", "Atlas Lucide carregado do script e mantido em cache"
        for _, node in pairs(iconAssets.nodes) do useIconImage(node) end
    end)
end

local function icon(parent, kind, color)
    local canvas = make("Frame", {Name = "Icon", Position = UDim2.new(0, 8, 0.5, -10),
        Size = UDim2.fromOffset(20, 20), BackgroundTransparency = 1, Active = false, ZIndex = 17}, parent)
    local fallback = make("Frame", {Name = "VectorFallback", Position = UDim2.fromOffset(2, 2),
        Size = UDim2.fromOffset(16, 16), BackgroundTransparency = 1, ZIndex = 18}, canvas)
    local function line(x, y, w, h, rotation)
        return make("Frame", {Position = UDim2.fromOffset(x, y), Size = UDim2.fromOffset(w, h),
            Rotation = rotation or 0, BorderSizePixel = 0, BackgroundColor3 = color, ZIndex = 18}, fallback)
    end
    local function box(x, y, w, h)
        local frame = make("Frame", {Position = UDim2.fromOffset(x, y), Size = UDim2.fromOffset(w, h),
            BackgroundTransparency = 1, BorderSizePixel = 0, ZIndex = 18}, fallback)
        round(frame, 2, color)
    end
    if kind == "play" then
        line(3, 1, 2, 14) line(5, 3, 8, 2, 35) line(5, 11, 8, 2, -35)
    elseif kind == "pause" then
        line(3, 2, 3, 12) line(10, 2, 3, 12)
    elseif kind == "minus" then
        line(2, 7, 12, 2)
    elseif kind == "close" then
        line(1, 7, 14, 2, 45) line(1, 7, 14, 2, -45)
    elseif kind == "maximize" then
        box(1, 1, 14, 14)
    elseif kind == "help" then
        box(1, 1, 14, 14) line(5, 4, 6, 2) line(9, 5, 2, 4) line(7, 8, 4, 2) line(7, 12, 2, 2)
    elseif kind == "script" then
        box(2, 0, 12, 16) line(5, 4, 6, 1) line(5, 8, 6, 1) line(5, 12, 4, 1)
    elseif kind == "block" then
        box(1, 1, 14, 14) line(0, 7, 16, 2, -45)
    elseif kind == "star" then
        line(7, 1, 2, 14) line(1, 7, 14, 2) line(2, 7, 12, 2, 45) line(2, 7, 12, 2, -45)
    elseif kind == "trash" then
        box(3, 5, 10, 10) line(1, 2, 14, 2) line(6, 0, 4, 2) line(7, 7, 2, 6)
    elseif kind == "info" then
        box(1, 1, 14, 14) line(7, 4, 2, 2) line(7, 8, 2, 5)
    elseif kind == "scan" then
        box(1, 1, 11, 11) line(10, 12, 7, 2, 45) line(6, 3, 1, 7) line(3, 6, 7, 1)
    elseif kind == "edit" then
        box(1, 5, 10, 10) line(4, 6, 13, 3, -45)
    elseif kind == "filter" then
        line(1, 2, 14, 2) line(3, 7, 10, 2) line(6, 12, 4, 2)
    elseif kind == "link" then
        box(0, 2, 9, 7) box(7, 7, 9, 7) line(5, 7, 7, 2, 45)
    elseif kind == "reset" then
        box(3, 3, 12, 12) line(0, 0, 2, 8) line(0, 6, 7, 2)
    else
        box(5, 1, 10, 11) box(1, 5, 10, 11)
    end
    local created, image = pcall(make, "ImageLabel", {Name = "Glyph", Size = UDim2.fromScale(1, 1),
        BackgroundTransparency = 1, BorderSizePixel = 0, Image = "", ImageColor3 = color,
        ScaleType = Enum.ScaleType.Fit, ZIndex = 19}, canvas)
    if not created then
        spy.icons.message = "ImageLabel indisponível; ícones locais ativos"
        return canvas
    end
    local node = {image = image, fallback = fallback, kind = kind}
    iconAssets.nodes[canvas] = node
    pcall(on, image, "Changed", function(property)
        if property == "IsLoaded" then set(fallback, {Visible = get(image, "IsLoaded") ~= true}) end
    end)
    useIconImage(node)
    return canvas
end
local function button(parent, text, position, size, callback, bucket, compact)
    local object = make("TextButton", {Text = text, TextColor3 = ink, TextSize = 14,
        Font = Enum.Font.GothamMedium, BackgroundColor3 = buttonBG,
        BorderSizePixel = 0,
        Position = position, Size = size, AutoButtonColor = true, TextScaled = true,
        Visible = true, Active = true, Selectable = true,
        TextTransparency = compact and 0 or 1, ZIndex = 15}, parent)
    round(object, compact and 6 or 8, compact and nil or border)
    make("UITextSizeConstraint", {MinTextSize = 8, MaxTextSize = compact and 18 or 14}, object)
    if not compact then
        make("Frame", {Name = "Accent", Position = UDim2.fromOffset(0, 7),
            Size = UDim2.new(0, 3, 1, -14), BorderSizePixel = 0, BackgroundTransparency = 1,
            BackgroundColor3 = violet, ZIndex = 16}, object)
        local caption = label(object, text, UDim2.new(0, 7, 0.06, 0), UDim2.new(1, -14, 0.88, 0))
        set(caption, {Name = "Caption", Font = Enum.Font.GothamMedium, TextScaled = true,
            TextXAlignment = Enum.TextXAlignment.Center, TextYAlignment = Enum.TextYAlignment.Center, ZIndex = 17})
        make("UITextSizeConstraint", {MinTextSize = 8, MaxTextSize = 14}, caption)
        on(object, "Changed", function(property)
            if property == "Text" then set(caption, {Text = get(object, "Text") or ""}) end
            if property == "TextColor3" then set(caption, {TextColor3 = get(object, "TextColor3") or ink}) end
        end, bucket)
    end
    if compact then
        local glyphs = {["?"] = "help", ["−"] = "minus", ["□"] = "maximize", ["×"] = "close",
            ["Ⅱ"] = "pause", ["▶"] = "play", ["★"] = "star"}
        if glyphs[text] then
            set(object, {TextTransparency = 1})
            local variants = {}
            local function variant(caption)
                if not variants[caption] then
                    local canvas = icon(object, glyphs[caption], get(object, "TextColor3") or ink)
                    set(canvas, {Position = UDim2.new(0.5, -10, 0.5, -10)})
                    variants[caption] = canvas
                end
                for key, canvas in pairs(variants) do set(canvas, {Visible = key == caption}) end
            end
            variant(text)
            if text == "Ⅱ" then variant("▶") variant(text) end
            on(object, "Changed", function(property)
                if property == "Text" then
                    local caption = get(object, "Text")
                    if glyphs[caption] then variant(caption) end
                elseif property == "TextColor3" then
                    local tint = get(object, "TextColor3") or ink
                    for _, canvas in pairs(variants) do
                        local node = iconAssets.nodes[canvas]
                        if node then
                            set(node.image, {ImageColor3 = tint})
                            local found, descendants = call(node.fallback, "GetDescendants")
                            if found then for _, child in ipairs(descendants) do
                                local class = get(child, "ClassName")
                                if class == "Frame" then set(child, {BackgroundColor3 = tint})
                                elseif class == "UIStroke" then set(child, {Color = tint}) end
                            end end
                        end
                    end
                end
            end, bucket)
        end
    end
    if callback then on(object, "Activated", callback, bucket) end
    return object
end
setStatus = function(text)
    if not alive then return end
    set(statusLabel, {Text = short(text, 300)})
    local failed = text:find("Falha", 1, true) or text:find("Erro", 1, true) or text:find("Sintaxe", 1, true)
    set(ui.statusDot, {BackgroundColor3 = failed and Color3.fromRGB(244, 111, 135) or Color3.fromRGB(92, 219, 158)})
end
matchesEntry = function(entry)
    if entry.dead then return false end
    if (entry.kind == "remote") ~= (ui.source == "catalogue") then return false end
    local isFunction = entry.class == "RemoteFunction" or entry.class == "BindableFunction"
    if ui.filter == "function" and not isFunction then return false end
    if ui.filter == "event" and isFunction then return false end
    if ui.favoritesOnly and not spy.favorites[entry.remote] then return false end
    return query == "" or entry.search:find(query, 1, true) ~= nil
end
responsiveLayout = function(width)
    if width then ui.width = width end
    if not ui.sidebar or not detail then return end
    ui.narrow = (ui.width or C.windowMaxWidth) < 520
    set(ui.mobileNav, {Visible = ui.narrow})
    set(ui.divider, {Visible = not ui.narrow})
    if ui.narrow then
        set(ui.sidebar, {Position = UDim2.fromOffset(0, 36), Size = UDim2.new(1, 0, 1, -36), Visible = ui.pane == "list"})
        set(detail, {Position = UDim2.fromOffset(0, 36), Size = UDim2.new(1, 0, 1, -36), Visible = ui.pane == "code"})
    else
        set(ui.sidebar, {Position = UDim2.new(), Size = UDim2.fromScale(0.32, 1), Visible = true})
        set(detail, {Position = UDim2.fromScale(0.32, 0), Size = UDim2.fromScale(0.68, 1), Visible = true})
    end
    set(ui.listTab, {BackgroundColor3 = ui.pane == "list" and Color3.fromRGB(77, 39, 122) or buttonBG})
    set(ui.codeTab, {BackgroundColor3 = ui.pane == "code" and Color3.fromRGB(77, 39, 122) or buttonBG})
    local showVersion = (ui.width or C.windowMaxWidth) >= 500
    set(ui.version, {Visible = showVersion})
    set(ui.captureBadge, {Visible = showVersion})
    set(titleLabel, {Size = UDim2.new(1, showVersion and -120 or -52, 1, -10)})
    layoutDirty = true
end
local function highlight(source)
    local out, index, length = {}, 1, #source
    local keywords = {["local"] = true, ["function"] = true, ["end"] = true,
        ["return"] = true, ["for"] = true, ["in"] = true, ["do"] = true, ["if"] = true,
        ["then"] = true, ["else"] = true, ["elseif"] = true, ["while"] = true,
        ["repeat"] = true, ["until"] = true, ["and"] = true, ["or"] = true, ["not"] = true}
    local function paint(text, color)
        return '<font color="#' .. color .. '">' .. escape(text) .. '</font>'
    end
    while index <= length do
        local char = source:sub(index, index)
        local text, color
        if source:sub(index, index + 1) == "--" then
            local equals = source:match("^%-%-%[(=*)%[", index)
            local finish
            if equals then
                local _, close = source:find("]" .. equals .. "]", index + 4 + #equals, true)
                finish = close or length
            else finish = (source:find("\n", index, true) or (length + 1)) - 1 end
            text, color = source:sub(index, finish), "858B98"
        elseif char == '"' or char == "'" then
            local cursor = index + 1
            while cursor <= length do
                local c = source:sub(cursor, cursor)
                if c == "\\" then cursor = cursor + 2
                elseif c == char then cursor = cursor + 1 break
                else cursor = cursor + 1 end
            end
            text, color = source:sub(index, cursor - 1), "A8CA8A"
        elseif char:match("[%a_]") then
            text = source:match("^[%a_][%w_]*", index)
            if keywords[text] then color = "B980D1"
            elseif text == "nil" or text == "true" or text == "false" then color = "D5B38E"
            elseif text == "args" or text == "T" then color = "DE8699"
            elseif source:match("^%s*%(", index + #text) then color = "82B6DC"
            elseif text == "game" then color = "D8C59B" end
        elseif char:match("%d") then
            text = source:match("^0[xX][%da-fA-F]+", index)
                or source:match("^%d+%.?%d*[eE][%+%-]?%d+", index) or source:match("^%d+%.?%d*", index)
            color = "E2C778"
        else text = char end
        out[#out + 1] = color and paint(text, color) or escape(text)
        index = index + #text
    end
    return table.concat(out)
end
setSource = function(source, mode)
    sourceText = source
    documentMode = mode or "call"
    documentRevision = documentRevision + 1
    set(modeLabel, {Text = documentMode == "call" and "CHAMADA" or documentMode == "info" and "INFORMAÇÕES" or "SCRIPT"})
    local visible = source
    if #visible > 40000 then visible = short(visible, 40000) .. "\n-- Prévia limitada; Copy Code copia tudo." end
    local numbers, count, longest = {}, 0, 0
    for line in (visible .. "\n"):gmatch("(.-)\n") do
        count = count + 1
        numbers[count], longest = tostring(count), math.max(longest, #line)
    end
    local width, height = math.max(320, longest * 8.5 + 20), math.max(30, count * 17)
    set(argsLabel, {Text = highlight(visible), Size = UDim2.fromOffset(width, height)})
    set(codeLines, {Text = table.concat(numbers, "\n"), Size = UDim2.fromOffset(38, height)})
    set(codeScroll, {CanvasSize = UDim2.fromOffset(width + 60, height + 16), CanvasPosition = Vector2.new(0, 0)})
end
local function remoteExpression(info)
    assert(info.rooted, "Remote fora do DataModel")
    local expression = "game"
    for index, name in ipairs(info.names) do
        local ok, service = false, nil
        if index == 1 then ok, service = call(game, "GetService", name) end
        if ok and service and get(service, "Name") == name then
            expression = expression .. ":GetService(" .. quote(name) .. ")"
        else expression = expression .. ":FindFirstChild(" .. quote(name) .. ")" end
    end
    return expression
end
local function callSource(entry, explicitArgs)
    assert(resolve(entry.info) == entry.remote, "O path do remote mudou")
    local expression = remoteExpression(entry.info)
    local arguments = not explicitArgs and entry.editedSource
        or readableArguments(explicitArgs or entry.args)
    local prefix = "local args = table.pack(\n" .. arguments .. "\n)\n\n"
    if entry.direction == "in" then
        return "-- Evento recebido do servidor; somente inspeção.\n" .. prefix
            .. "local remote = " .. expression .. "\n-- Sinal: remote.OnClientEvent"
    end
    if entry.kind == "remote" and not entry.hasOutgoing and not entry.editedSource and not explicitArgs then
        return "-- Remote encontrado; nenhum envio capturado.\nlocal remote = " .. expression
            .. "\n-- Use Editar args para informar os argumentos antes de executar."
    end
    return prefix .. expression .. ":" .. entry.method .. "(table.unpack(args, 1, args.n))"
end
isReplayable = function(entry)
    return entry and not entry.dead and entry.direction ~= "in"
        and (entry.kind ~= "remote" or entry.hasOutgoing or entry.editedSource ~= nil)
end
local function copy(text, message)
    local clipboard = type(setclipboard) == "function" and setclipboard or toclipboard
    if type(clipboard) == "function" then
        local ok = pcall(clipboard, text)
        if ok then setStatus(message) return end
    end
    showCopyDialog(text)
    setStatus("Selecione o texto e use Copiar no teclado do celular")
end
showCopyDialog = function(text)
    set(copyBox, {Text = text})
    set(copyDialog, {Visible = true})
    call(copyBox, "CaptureFocus")
    set(copyBox, {CursorPosition = #text + 1, SelectionStart = 1})
end
refreshActions = function()
    local entry = selected
    local named = entry and keyFor(entry.name, entry.method)
    local function active(object, enabled, tint)
        set(object, {BackgroundColor3 = enabled and Color3.new(tint.R * 0.23, tint.G * 0.23, tint.B * 0.23) or buttonBG})
        tintOutline(object, enabled and tint or border, enabled and 0 or 0.15)
        local ok, bar = call(object, "FindFirstChild", "Accent")
        if ok and bar then set(bar, {BackgroundColor3 = tint, BackgroundTransparency = enabled and 0 or 1}) end
    end
    local purple, red = semantic.ignore, semantic.block
    active(ignoreButton, entry and spy.ignore[entry.key], purple)
    active(ignoreNameButton, named and spy.ignoreNames[named], purple)
    active(blockButton, entry and spy.blocked[entry.key], red)
    active(blockNameButton, named and spy.blockedNames[named], red)
    local function captionText(object, text)
        local found, caption = call(object, "FindFirstChild", "Caption")
        if found then set(caption, {Text = text}) end
    end
    captionText(ignoreButton, entry and spy.ignore[entry.key] and "Reativar path" or "Ignorar path")
    captionText(ignoreNameButton, named and spy.ignoreNames[named] and "Reativar nome" or "Ignorar nome")
    captionText(blockButton, entry and spy.blocked[entry.key] and "Desbloquear path" or "Bloquear path")
    captionText(blockNameButton, named and spy.blockedNames[named] and "Desbloquear nome" or "Bloquear nome")
    set(runButton, {Text = busy and "Parar espera" or "Run Code",
        BackgroundColor3 = busy and Color3.fromRGB(124, 48, 67) or Color3.fromRGB(104, 45, 178)})
    tintOutline(runButton, busy and red or violet)
    local ok, caption = call(runButton, "FindFirstChild", "Caption")
    if ok then set(caption, {Text = busy and "Parar espera" or "Executar chamada"}) end
    set(runButton, {BackgroundTransparency = not busy and not isReplayable(entry) and 0.4 or 0})
    active(ui.favoriteButton, entry and spy.favorites[entry.remote], semantic.ignore)
    captionText(ui.favoriteButton, entry and spy.favorites[entry.remote] and "Remover favorito" or "Favoritar remote")
    set(ui.favoriteFilter, {TextColor3 = ui.favoritesOnly and semantic.ignore or muted})
    for source, object in pairs(ui.sourceButtons or {}) do
        set(object, {BackgroundColor3 = ui.source == source and Color3.fromRGB(71, 38, 112) or buttonBG,
            TextColor3 = ui.source == source and ink or muted})
    end
    for filter, object in pairs(ui.filterButtons) do
        set(object, {BackgroundColor3 = ui.filter == filter and Color3.fromRGB(71, 38, 112) or buttonBG,
            TextColor3 = ui.filter == filter and ink or muted})
    end
    set(ui.captureBadge, {Text = spy.enabled and "AO VIVO" or "PAUSADO",
        TextColor3 = spy.enabled and Color3.fromRGB(105, 226, 168) or Color3.fromRGB(242, 199, 96),
        BackgroundColor3 = spy.enabled and Color3.fromRGB(22, 55, 42) or Color3.fromRGB(59, 46, 26)})
end
layoutEntries = function()
    if not alive or not list then return end
    local visibleCount, source = 0, ui.source == "catalogue" and catalogue or entries
    local viewport = get(list, "AbsoluteWindowSize") or get(list, "AbsoluteSize")
    local scroll = get(list, "CanvasPosition")
    local top = typeof(scroll) == "Vector2" and scroll.Y or 0
    local bottom = top + (typeof(viewport) == "Vector2" and viewport.Y or 600)
    for _, entry in ipairs(ui.source == "catalogue" and entries or catalogue) do
        set(entry.row, {Visible = false})
        entry.layoutVisible = false
    end
    for _, entry in ipairs(source) do
        local visible = matchesEntry(entry)
        local y = visibleCount * (ROW_HEIGHT + ROW_GAP)
        local materialize = visible and (entry.kind ~= "remote" or y + ROW_HEIGHT >= top - 116 and y <= bottom + 116)
        if materialize and not entry.row then renderEntry(entry) end
        if entry.kind == "remote" and not materialize and entry.row then
            disconnect(entry.connections)
            destroy(entry.row)
            entry.row, entry.nameLabel, entry.countLabel, entry.accent = nil, nil, nil, nil
            entry.layoutY, entry.layoutVisible = nil, nil
        end
        visible = visible and materialize
        if entry.layoutVisible ~= visible then
            set(entry.row, {Visible = visible})
            entry.layoutVisible = visible
        end
        if visible then
            if entry.layoutY ~= y then
                set(entry.row, {Position = UDim2.fromOffset(0, y), Size = UDim2.new(1, -8, 0, ROW_HEIGHT)})
                entry.layoutY = y
            end
        end
        if matchesEntry(entry) then visibleCount = visibleCount + 1 end
    end
    local height = math.max(0, visibleCount * (ROW_HEIGHT + ROW_GAP) - ROW_GAP + 4)
    set(list, {CanvasSize = UDim2.new(1, 0, 0, height)})
    if spy.follow and ui.source == "calls" and typeof(viewport) == "Vector2" then
        set(list, {CanvasPosition = Vector2.new(0, math.max(0, height - viewport.Y))})
    end
    set(emptyLabel, {Visible = visibleCount == 0, Text = query ~= "" and "Nenhuma chamada nesta busca"
        or ui.filter ~= "all" and "Nenhuma chamada deste tipo"
        or logFailures > 0 and "Falha ao exibir chamadas. Veja a mensagem abaixo."
        or ui.favoritesOnly and "Nenhum favorito neste filtro"
        or ui.source == "catalogue" and "Nenhum remote encontrado no cliente"
        or "Aguardando chamadas…"})
    layoutDirty = false
end
refreshFilter = function() layoutDirty = true layoutEntries() end
chooseSource = function(source)
    ui.source = source
    set(list, {CanvasPosition = Vector2.new(0, 0)})
    refreshFilter()
    refreshActions()
    setStatus(source == "catalogue" and "Encontrados: remotes disponíveis no cliente; selecione para inspecionar"
        or "Chamadas: envios, eventos locais e eventos recebidos capturados")
end
updateRow = function(entry)
    if entry.kind == "remote" and entry.displayedArgs ~= entry.args then
        entry.displayedArgs = entry.args
        entry.plain, entry.rich = displayArguments(entry.args)
        entry.search = string.lower(entry.info.path .. "\n" .. entry.class .. "\n" .. entry.plain)
        entry.callSource = nil
        layoutDirty = true
    end
    local suffix = entry.collapsed and (" ×" .. entry.bucket.total) or ""
    set(entry.nameLabel, {Text = (spy.favorites[entry.remote] and "★ " or "") .. entry.name .. suffix})
    set(entry.countLabel, {Text = entry.kind == "remote"
        and ("Encontrado · " .. (entry.activity or 0) .. " chamadas" .. (entry.receives and " · RX" or ""))
        or string.format("%s · +%.3fs%s", entry.direction == "in" and "Recebido" or entry.method, entry.at,
        entry.blocked and " · BLOCK" or "") .. (entry.collapsed and (" · ×" .. entry.bucket.total) or "")})
    set(entry.row, {BackgroundColor3 = selected == entry and Color3.fromRGB(49, 29, 75) or panel,
        BorderSizePixel = 0})
    tintOutline(entry.row, violet, selected == entry and 0.15 or 1)
end
selectEntry = function(entry, showDetail)
    if entry.dead then return end
    if pendingScript and cancelScriptLoad then cancelScriptLoad() end
    local old = selected
    selected = entry
    if old and not old.dead then updateRow(old) end
    updateRow(entry)
    set(modal, {Visible = false})
    set(copyDialog, {Visible = false})
    set(metaLabel, {Text = entry.class .. " · " .. entry.info.path})
    if not entry.callSource then
        local ok, source = pcall(callSource, entry)
        entry.callSource = ok and source or nil
        entry.sourceError = not ok and tostring(source) or nil
    end
    sourceReady = entry.callSource ~= nil
    setSource(entry.callSource or ("-- Não há literal executável: " .. (entry.sourceError or "indisponível")
        .. "\n-- Use Edit Args para informar os argumentos.\n\n-- Argumentos capturados:\n-- "
        .. entry.plain:gsub("\n", "\n-- ")))
    refreshActions()
    if showDetail ~= false then ui.pane = "code" responsiveLayout() end
end
renderEntry = function(entry)
    local row = make("TextButton", {Name = "RemoteRow", Size = UDim2.new(1, -8, 0, ROW_HEIGHT), Text = "",
        BackgroundColor3 = panel, BorderColor3 = Color3.fromRGB(120, 128, 159), BorderSizePixel = 0,
        LayoutOrder = entry.order, AutoButtonColor = false, BackgroundTransparency = 0,
        Active = true, ZIndex = 21, Visible = matchesEntry(entry)}, list)
    entry.row = row
    round(row, 8, violet)
    entry.accent = make("Frame", {Name = "TypeColor", Position = UDim2.fromOffset(0, 9), Size = UDim2.new(0, 3, 1, -18),
        BackgroundColor3 = accents[entry.class] or ink, BorderSizePixel = 0,
        Visible = true, BackgroundTransparency = 0, ZIndex = 22}, row)
    entry.nameLabel = label(row, entry.name, UDim2.fromOffset(11, 7), UDim2.new(1, -82, 0, 23))
    set(entry.nameLabel, {Font = Enum.Font.GothamMedium, TextSize = 14, TextTruncate = Enum.TextTruncate.AtEnd})
    local tag = label(row, entry.class == "RemoteFunction" and "Function" or entry.class == "UnreliableRemoteEvent"
        and "Unrel" or entry.class == "BindableEvent" and "Local" or entry.class == "BindableFunction" and "Local Fn"
        or "Event", UDim2.new(1, -65, 0, 8), UDim2.fromOffset(57, 20))
    set(tag, {BackgroundTransparency = 0, BackgroundColor3 = Color3.fromRGB(40, 29, 57),
        Font = Enum.Font.GothamMedium, TextSize = 9, TextColor3 = accents[entry.class] or ink,
        TextXAlignment = Enum.TextXAlignment.Center, TextYAlignment = Enum.TextYAlignment.Center})
    round(tag, 5)
    entry.countLabel = label(row, "", UDim2.fromOffset(11, 33), UDim2.new(1, -21, 0, 14))
    set(entry.countLabel, {TextSize = 10, TextColor3 = Color3.fromRGB(177, 180, 189),
        TextTruncate = Enum.TextTruncate.AtEnd})
    updateRow(entry)
    on(row, "Activated", function() selectEntry(entry) end, entry.connections)
end
local function clear()
    if busy and cancelReplay then cancelReplay() end
    if pendingScript and cancelScriptLoad then cancelScriptLoad() end
    call(codeBox, "ReleaseFocus")
    call(copyBox, "ReleaseFocus")
    epoch = epoch + 1
    for _, entry in ipairs(entries) do removeEntry(entry) end
    entries, rates, dirty, queue, qHead, qTail = {}, {}, {}, {}, 1, 0
    total, dropped, selected, editing, sourceReady = 0, 0, nil, nil, false
    query = ""
    ui.filter, ui.pane, ui.source, ui.favoritesOnly = "all", "list", "calls", false
    set(searchBox, {Text = ""})
    logFailures, spy.lastError, layoutDirty = 0, nil, true
    set(modal, {Visible = false})
    set(copyDialog, {Visible = false})
    set(metaLabel, {Text = "Selecione um remote"})
    setSource("-- Selecione uma chamada na lista.")
    refreshActions()
    layoutEntries()
    responsiveLayout()
    setStatus("Logs limpos")
end
local function needSelection(action)
    if not selected or selected.dead then setStatus("Selecione uma chamada na lista") return end
    action(selected)
end
local function functionInfo(entry)
    local origin = entry.callerScript and getInfo(entry.callerScript).path or "Origem não fornecida pelo executor"
    local native = get(entry.remote, entry.method)
    local nativeSource, nativeName = "indisponível", entry.method
    if type(native) == "function" and type(debug.info) == "function" then
        local ok, source, name = pcall(debug.info, native, "sn")
        if ok then nativeSource, nativeName = source or "?", name or entry.method end
    end
    local observation = entry.observation
    local returns = observation and observation.results
    local resultText = returns and displayArguments(returns) or "Ainda não disponível"
    setSource("-- FUNCTION INFO\n-- Remote: " .. entry.info.path .. "\n-- Classe: " .. entry.class
        .. "\n-- Método: " .. entry.method .. "\n-- Argumentos: " .. entry.args.n
        .. "\n-- Script: " .. origin .. "\n-- Instante: +" .. string.format("%.3f", entry.at)
        .. "s\n-- Chamadas no grupo: " .. (entry.collapsed and entry.bucket.total or 1)
        .. "\n-- Função: " .. nativeName .. "\n-- Fonte da função: " .. nativeSource
        .. "\n-- Argumentos editados: " .. (entry.editedArgs and entry.editedArgs.n or "não")
        .. "\n-- Último retorno: " .. (entry.lastResult and entry.lastResult.n or "nenhum")
        .. "\n-- Direção: " .. (entry.direction == "in" and "Recebido do servidor" or entry.direction == "local" and "Local" or entry.kind == "remote" and "Descoberto" or "Enviado ao servidor")
        .. "\n-- Duração capturada: " .. (observation and observation.duration and string.format("%.3f ms", observation.duration * 1000) or "pendente / indisponível")
        .. "\n-- Retornos capturados: " .. (returns and returns.n or "indisponível")
        .. "\n-- " .. resultText:gsub("\n", "\n-- ")
        .. (observation and observation.error and ("\n-- Erro original: " .. observation.error) or "")
        .. "\n\n-- Use Chamada para voltar ao código executável.", "info")
    sourceReady = false
end
cancelScriptLoad = function()
    scriptToken = scriptToken + 1
    local thread = scriptThread
    pendingScript, scriptThread = false, nil
    if thread and type(task.cancel) == "function" and thread ~= coroutine.running() then pcall(task.cancel, thread) end
end
local function showScript(entry)
    local origin = entry.callerScript
    if not origin then
        setSource("-- SCRIPT DE ORIGEM INDISPONÍVEL\n-- O executor não retornou getcallingscript para esta chamada.\n"
            .. "-- Remote: " .. entry.info.path .. "\n-- Método: " .. entry.method, "script")
        setStatus("Origem indisponível neste executor; os dados do remote continuam acessíveis")
        return
    end
    if pendingScript then cancelScriptLoad() end
    local revision = documentRevision
    scriptToken = scriptToken + 1
    local token = scriptToken
    pendingScript = true
    setStatus("Carregando script de origem…")
    local spawned = task.spawn(function()
        local ok, source = pcall(function()
            local direct = get(origin, "Source")
            if type(direct) == "string" and direct ~= "" then return direct end
            if type(decompile) == "function" then return decompile(origin) end
        end)
        if token ~= scriptToken then return end
        pendingScript, scriptThread = false, nil
        if not alive or entry.dead or selected ~= entry or revision ~= documentRevision then return end
        sourceReady = false
        if ok and type(source) == "string" and source ~= "" then
            setSource(source, "script")
            setStatus("Script: " .. getInfo(origin).path)
        else
            local resolved, reference = pcall(instanceLiteral, origin)
            setSource("-- Fonte não disponibilizada pelo executor.\n-- Referência real do script de origem:\n"
                .. (resolved and ("local origin = " .. reference) or ("-- " .. getInfo(origin).path)), "script")
            setStatus("Fonte indisponível; referência do script exibida para copiar")
        end
    end)
    scriptThread = pendingScript and spawned or nil
end
local function buildUI()
    local ok, core = call(game, "GetService", "CoreGui")
    local _, players = call(game, "GetService", "Players")
    local _, input = call(game, "GetService", "UserInputService")
    local _, run = call(game, "GetService", "RunService")
    gui = make("ScreenGui", {Name = "IgniteSpy", IgnoreGuiInset = true,
        DisplayOrder = 100000, ResetOnSpawn = false, ZIndexBehavior = Enum.ZIndexBehavior.Sibling})
    local parented = false
    if type(gethui) == "function" then
        local found, hidden = pcall(gethui)
        if found and typeof(hidden) == "Instance" then parented = pcall(function() gui.Parent = hidden end) end
    end
    if not parented then parented = ok and pcall(function() gui.Parent = core end) end
    if not parented then
        local player = get(players, "LocalPlayer")
        local deadline = os.clock() + 5
        while not player and os.clock() < deadline do task.wait(0.1) player = get(players, "LocalPlayer") end
        local found, playerGui = call(player, "FindFirstChildOfClass", "PlayerGui")
        if not found or not playerGui then found, playerGui = call(player, "WaitForChild", "PlayerGui", 5) end
        assert(found and playerGui, "CoreGui e PlayerGui indisponíveis")
        local attached, err = pcall(function() gui.Parent = playerGui end)
        assert(attached, err)
    end
    window = make("Frame", {Name = "IgniteSpyWindow", Size = UDim2.fromScale(C.windowScale, 0.86),
        Position = UDim2.fromScale((1 - C.windowScale) / 2, 0.07), BackgroundColor3 = bg,
        BorderSizePixel = 0,
        Active = true, ClipsDescendants = true}, gui)
    round(window, 11, violet)
    local sizeConstraint = make("UISizeConstraint", {Name = "WindowBounds",
        MaxSize = Vector2.new(C.windowMaxWidth, C.windowMaxHeight), MinSize = Vector2.new(290, C.titleHeight)}, window)
    local brandLine = make("Frame", {Name = "BrandAccent", Position = UDim2.fromOffset(10, 0),
        Size = UDim2.new(1, -20, 0, 2), BorderSizePixel = 0,
        BackgroundColor3 = Color3.new(1, 1, 1), ZIndex = 30}, window)
    make("UIGradient", {Color = ColorSequence.new(violet, Color3.fromRGB(247, 221, 64))}, brandLine)
    local header = make("Frame", {Name = "TitleBar", Size = UDim2.new(1, -144, 0, C.titleHeight),
        BackgroundColor3 = bg, BorderSizePixel = 0, Active = true}, window)
    local mark = make("Frame", {Position = UDim2.fromOffset(9, 7), Size = UDim2.fromOffset(27, 27),
        BackgroundColor3 = Color3.fromRGB(94, 41, 162), BorderSizePixel = 0}, header)
    round(mark, 7, violet)
    local markText = label(mark, "i", UDim2.new(), UDim2.fromScale(1, 1))
    set(markText, {Font = Enum.Font.GothamBold, TextSize = 22, TextXAlignment = Enum.TextXAlignment.Center,
        TextYAlignment = Enum.TextYAlignment.Center})
    titleLabel = label(header, "ignite Spy", UDim2.fromOffset(44, 9), UDim2.new(1, -120, 1, -10))
    set(titleLabel, {Name = "BrandName", Font = Enum.Font.SourceSansBold, TextSize = 20,
        TextColor3 = ink, TextTruncate = Enum.TextTruncate.AtEnd})
    ui.version = label(header, "v" .. spy.version, UDim2.new(1, -72, 0, 4), UDim2.fromOffset(65, 13))
    set(ui.version, {TextSize = 10, TextColor3 = muted, TextXAlignment = Enum.TextXAlignment.Right})
    body = make("Frame", {Name = "Body", Position = UDim2.fromOffset(0, C.titleHeight),
        Size = UDim2.new(1, 0, 1, -C.titleHeight - 26), BackgroundTransparency = 1}, window)
    local minimized, maximized, restoreSize, normalSize, normalPosition = false, false, nil, nil, nil
    local function fitWindow()
        local viewport = get(gui, "AbsoluteSize")
        if typeof(viewport) ~= "Vector2" or viewport.X < 64 or viewport.Y < 64 then return end
        local minimum = math.min(290, viewport.X - 16)
        local compactWidth = math.max(minimum, math.min(C.windowMaxWidth, math.floor(viewport.X * C.windowScale), viewport.X - 16))
        local compactHeight = math.max(C.titleHeight, math.min(C.windowMaxHeight, math.floor(viewport.Y * 0.86), viewport.Y - 16))
        ui.compactWidth = compactWidth
        local width, height = compactWidth, compactHeight
        if maximized then
            normalSize = UDim2.fromOffset(compactWidth, compactHeight)
            normalPosition = UDim2.fromOffset(math.floor((viewport.X - compactWidth) / 2), math.floor((viewport.Y - compactHeight) / 2))
            width, height = math.floor(viewport.X * 0.98), math.floor(viewport.Y * 0.96)
        end
        local x, y = math.floor((viewport.X - width) / 2), math.floor((viewport.Y - height) / 2)
        set(sizeConstraint, {MinSize = Vector2.new(minimum, C.titleHeight),
            MaxSize = maximized and Vector2.new(100000, 100000) or Vector2.new(C.windowMaxWidth, C.windowMaxHeight)})
        if minimized then restoreSize, height = UDim2.fromOffset(width, height), C.titleHeight end
        set(window, {Size = UDim2.fromOffset(width, height), Position = UDim2.fromOffset(x, y)})
        responsiveLayout(width)
        layoutDirty = true
    end
    on(gui, "Changed", function(property) if property == "AbsoluteSize" then fitWindow() end end)
    fitWindow()
    button(window, "?", UDim2.new(1, -136, 0, 5), UDim2.fromOffset(30, 30), function()
        set(ui.helpPanel, {Visible = true})
    end, nil, true)
    button(window, "−", UDim2.new(1, -102, 0, 5), UDim2.fromOffset(30, 30), function()
        minimized = not minimized
        if minimized then
            call(codeBox, "ReleaseFocus")
            call(copyBox, "ReleaseFocus")
            restoreSize = get(window, "Size")
            set(body, {Visible = false})
            set(statusLabel, {Visible = false})
            set(window, {Size = UDim2.new(restoreSize.X.Scale, restoreSize.X.Offset, 0, C.titleHeight)})
        else
            set(window, {Size = restoreSize or UDim2.fromScale(C.windowScale, 0.86)})
            set(body, {Visible = true})
            set(statusLabel, {Visible = true})
        end
    end, nil, true)
    button(window, "□", UDim2.new(1, -68, 0, 5), UDim2.fromOffset(30, 30), function()
        if minimized then return end
        maximized = not maximized
        if maximized then
            normalSize, normalPosition = get(window, "Size"), get(window, "Position")
            set(sizeConstraint, {MaxSize = Vector2.new(100000, 100000)})
            set(window, {Size = UDim2.fromScale(0.98, 0.96), Position = UDim2.fromScale(0.01, 0.02)})
        else
            set(sizeConstraint, {MaxSize = Vector2.new(C.windowMaxWidth, C.windowMaxHeight)})
            set(window, {Size = normalSize, Position = normalPosition})
        end
        local viewport = get(gui, "AbsoluteSize")
        if typeof(viewport) == "Vector2" then responsiveLayout(maximized and viewport.X * 0.98 or ui.compactWidth or math.min(C.windowMaxWidth, viewport.X * C.windowScale)) end
    end, nil, true)
    button(window, "×", UDim2.new(1, -34, 0, 5), UDim2.fromOffset(30, 30), function()
        local done, err = unload()
        if not done then warn("ignite Spy: " .. tostring(err)) end
    end, nil, true)
    local sidebar = make("Frame", {Name = "RemoteList", Size = UDim2.new(0.32, 0, 1, 0),
        BackgroundColor3 = panel, BorderSizePixel = 0, ClipsDescendants = true,
        Visible = true, BackgroundTransparency = 0, ZIndex = 10}, body)
    ui.sidebar = sidebar
    round(sidebar, 9)
    ui.sourceButtons = {}
    for index, item in ipairs({{"calls", "Chamadas"}, {"catalogue", "Encontrados"}}) do
        local source = item[1]
        local sourceButton = button(sidebar, item[2], UDim2.new((index - 1) * 0.5, 7, 0, 5),
            UDim2.new(0.5, -12, 0, 24), function() chooseSource(source) end, nil, true)
        set(sourceButton, {Name = "Source_" .. source, TextSize = 10})
        ui.sourceButtons[source] = sourceButton
    end
    ui.captureBadge = label(header, "AO VIVO", UDim2.new(1, -72, 0, 20), UDim2.fromOffset(65, 14))
    set(ui.captureBadge, {BackgroundTransparency = 0, BackgroundColor3 = Color3.fromRGB(22, 55, 42),
        TextColor3 = Color3.fromRGB(105, 226, 168), TextSize = 9, Font = Enum.Font.GothamBold,
        TextXAlignment = Enum.TextXAlignment.Center, TextYAlignment = Enum.TextYAlignment.Center})
    set(ui.captureBadge, {Visible = false})
    round(ui.captureBadge, 6)
    local search = make("TextBox", {Name = "Search", Position = UDim2.fromOffset(8, 34), Size = UDim2.new(1, -80, 0, 30),
        BackgroundColor3 = editorBG, BorderSizePixel = 0,
        Text = "", PlaceholderText = "Buscar remote…", PlaceholderColor3 = muted,
        TextColor3 = ink, TextSize = 12, Font = Enum.Font.Gotham, ClearTextOnFocus = false}, sidebar)
    round(search, 7, border)
    searchBox = search
    pauseButton = button(sidebar, "Ⅱ", UDim2.new(1, -34, 0, 34), UDim2.fromOffset(26, 30), function()
        spy.enabled = not spy.enabled
        set(pauseButton, {Text = spy.enabled and "Ⅱ" or "▶"})
        refreshActions()
        setStatus(spy.enabled and "Captura retomada" or "Captura pausada; bloqueios continuam ativos")
    end, nil, true)
    ui.favoriteFilter = button(sidebar, "★", UDim2.new(1, -64, 0, 34), UDim2.fromOffset(26, 30), function()
        ui.favoritesOnly = not ui.favoritesOnly
        refreshFilter() refreshActions()
        setStatus(ui.favoritesOnly and "Mostrando somente favoritos" or "Mostrando todos os remotes do filtro")
    end, nil, true)
    set(ui.favoriteFilter, {Name = "FavoriteFilter", TextColor3 = muted})
    on(search, "Changed", function(property)
        if property == "Text" then query = string.lower(get(search, "Text") or "") refreshFilter() end
    end)
    for index, choice in ipairs({{"all", "Todos"}, {"event", "Eventos"}, {"function", "Funções"}}) do
        local filter = choice[1]
        local object = button(sidebar, choice[2], UDim2.new((index - 1) / 3, 6, 0, 70),
            UDim2.new(1 / 3, -8, 0, 24), function()
                ui.filter = filter
                refreshFilter()
                refreshActions()
            end, nil, true)
        set(object, {Name = "Filter_" .. filter, TextScaled = false, TextSize = 10})
        ui.filterButtons[filter] = object
    end
    list = make("ScrollingFrame", {Name = "RemoteScroll", Position = UDim2.fromOffset(8, 103),
        Size = UDim2.new(1, -12, 1, -129), BackgroundTransparency = 1, BorderSizePixel = 0,
        ScrollBarThickness = 5, ScrollBarImageColor3 = Color3.fromRGB(147, 149, 157),
        CanvasSize = UDim2.new(1, 0, 0, 0), AutomaticCanvasSize = Enum.AutomaticSize.None,
        ScrollingDirection = Enum.ScrollingDirection.Y, ScrollingEnabled = true,
        Active = true, Visible = true, ClipsDescendants = true, ZIndex = 20}, sidebar)
    emptyLabel = label(sidebar, "Aguardando chamadas…", UDim2.fromOffset(15, 122), UDim2.new(1, -30, 0, 90))
    set(emptyLabel, {TextWrapped = true, TextSize = 13, TextColor3 = Color3.fromRGB(175, 177, 186)})
    statsLabel = label(sidebar, "0 chamadas · 0 logs", UDim2.new(0, 8, 1, -21), UDim2.new(1, -60, 0, 18))
    set(statsLabel, {Name = "ListStats", TextSize = 10, TextColor3 = Color3.fromRGB(181, 183, 191),
        TextTruncate = Enum.TextTruncate.AtEnd})
    followButton = button(sidebar, "Live", UDim2.new(1, -48, 1, -23), UDim2.fromOffset(42, 21), function()
        spy.follow = not spy.follow
        set(followButton, {Text = spy.follow and "Live" or "Manual"})
        layoutDirty = true
        setStatus(spy.follow and "Lista acompanha as novas chamadas" or "Rolagem manual ativada")
    end, nil, true)
    on(list, "InputBegan", function()
        spy.follow = false
        set(followButton, {Text = "Manual"})
    end)
    on(list, "Changed", function(property)
        if property == "CanvasPosition" and ui.source == "catalogue" then layoutDirty = true end
    end)
    detail = make("Frame", {Name = "CodeAndActions", Position = UDim2.fromScale(0.32, 0),
        Size = UDim2.fromScale(0.68, 1), BackgroundColor3 = bg, BorderSizePixel = 0}, body)
    ui.divider = make("Frame", {Name = "PanelDivider", Position = UDim2.new(0.32, -1, 0, 0),
        Size = UDim2.new(0, 1, 1, 0), BorderSizePixel = 0,
        BackgroundColor3 = border, ZIndex = 25}, body)
    ui.mobileNav = make("Frame", {Name = "MobileNavigation", Size = UDim2.new(1, 0, 0, 30),
        BackgroundTransparency = 1, BorderSizePixel = 0, Visible = false}, body)
    ui.listTab = button(ui.mobileNav, "Remotes", UDim2.fromOffset(4, 0), UDim2.new(0.5, -6, 1, 0), function()
        ui.pane = "list" responsiveLayout()
    end, nil, true)
    ui.codeTab = button(ui.mobileNav, "Detalhes", UDim2.new(0.5, 2, 0, 0), UDim2.new(0.5, -6, 1, 0), function()
        ui.pane = "code" responsiveLayout()
    end, nil, true)
    local codePanel = make("Frame", {Name = "CodePanel", Position = UDim2.fromOffset(8, 6), Size = UDim2.new(1, -16, 0.55, -10),
        BackgroundColor3 = editorBG, BorderSizePixel = 0, ClipsDescendants = true}, detail)
    round(codePanel, 9, border)
    metaLabel = label(codePanel, "Selecione um remote", UDim2.fromOffset(8, 3), UDim2.new(1, -165, 0, 20))
    set(metaLabel, {TextSize = 10, TextColor3 = Color3.fromRGB(163, 171, 186), TextTruncate = Enum.TextTruncate.AtEnd})
    button(codePanel, "Chamada", UDim2.new(1, -152, 0, 0), UDim2.fromOffset(72, 23), function()
        needSelection(selectEntry)
    end, nil, true)
    button(codePanel, "Edit Args", UDim2.new(1, -77, 0, 0), UDim2.fromOffset(75, 23), function()
        needSelection(function(entry) openSpoof(entry) end)
    end, nil, true)
    codeScroll = make("ScrollingFrame", {Name = "SourceScroll", Position = UDim2.fromOffset(0, 25),
        Size = UDim2.new(1, 0, 1, -44), BackgroundTransparency = 1, BorderSizePixel = 0,
        CanvasSize = UDim2.new(), ScrollBarThickness = 6, ScrollingDirection = Enum.ScrollingDirection.XY}, codePanel)
    modeLabel = label(codePanel, "CHAMADA", UDim2.new(0, 9, 1, -16), UDim2.new(1, -18, 0, 14))
    set(modeLabel, {Name = "SourceMode", TextSize = 9, TextColor3 = violet})
    codeLines = label(codeScroll, "", UDim2.fromOffset(0, 6), UDim2.fromOffset(38, 40))
    set(codeLines, {TextColor3 = Color3.fromRGB(130, 135, 146), TextXAlignment = Enum.TextXAlignment.Right})
    argsLabel = label(codeScroll, "", UDim2.fromOffset(53, 6), UDim2.fromOffset(320, 40))
    set(argsLabel, {RichText = true, TextWrapped = false})
    local actions = make("Frame", {Name = "Actions", Position = UDim2.new(0, 8, 0.55, 2),
        Size = UDim2.new(1, -16, 0.45, -8), BackgroundColor3 = panel, BorderSizePixel = 0,
        ClipsDescendants = true}, detail)
    round(actions, 9, border)
    local specs = {{"code", "Código", semantic.code}, {"run", "Execução", semantic.run},
        {"protect", "Proteção", semantic.ignore}, {"tools", "Ferramentas", semantic.tool}}
    local groupCounts = {}
    for index, spec in ipairs(specs) do
        local key, text, tint = spec[1], spec[2], spec[3]
        local tab = button(actions, text, UDim2.new((index - 1) / 4, 4, 0, 5),
            UDim2.new(0.25, -8, 0, 29), function() setActionGroup(key) end, nil, true)
        set(tab, {Name = "ActionTab_" .. key, TextSize = 10})
        ui.actionTabs[key] = tab
        local group = make("ScrollingFrame", {Name = "ActionGroup_" .. key, Position = UDim2.fromOffset(6, 40),
            Size = UDim2.new(1, -12, 1, -46), BackgroundTransparency = 1, BorderSizePixel = 0,
            CanvasSize = UDim2.new(1, 0, 0, 0), AutomaticCanvasSize = Enum.AutomaticSize.None,
            ScrollingDirection = Enum.ScrollingDirection.Y, ScrollBarThickness = 3,
            ScrollBarImageColor3 = tint, Active = true, Visible = false}, actions)
        local grid = make("UIGridLayout", {CellSize = UDim2.new(0.5, -7, 0, 42),
            CellPadding = UDim2.new(0, 8, 0, 8), FillDirectionMaxCells = 2,
            SortOrder = Enum.SortOrder.LayoutOrder}, group)
        ui.actionGroups[key], groupCounts[key] = group, 0
        ui.actionButtons[key] = {}
        local function fitGroup()
            local size = get(group, "AbsoluteSize")
            local rows = math.max(1, math.ceil(groupCounts[key] / 2))
            local height = typeof(size) == "Vector2" and math.min(50, math.max(42, math.floor((size.Y - (rows - 1) * 8) / rows))) or 42
            set(grid, {CellSize = UDim2.new(0.5, -7, 0, height)})
            set(group, {CanvasSize = UDim2.new(1, 0, 0, rows * (height + 8) - 8)})
        end
        on(group, "Changed", function(property) if property == "AbsoluteSize" then fitGroup() end end)
        ui.actionButtons[key].fit = fitGroup
    end
    setActionGroup = function(key)
        if not ui.actionGroups[key] then return end
        ui.actionGroup = key
        for _, spec in ipairs(specs) do
            local active = spec[1] == key
            set(ui.actionGroups[spec[1]], {Visible = active})
            set(ui.actionTabs[spec[1]], {TextColor3 = active and spec[3] or muted,
                BackgroundColor3 = active and Color3.fromRGB(42, 33, 60) or buttonBG})
            tintOutline(ui.actionTabs[spec[1]], spec[3], active and 0.1 or 1)
        end
    end
    local function action(group, text, caption, glyph, tint, callback)
        groupCounts[group] = groupCounts[group] + 1
        local object = button(ui.actionGroups[group], text, UDim2.new(), UDim2.new(), callback)
        set(object, {LayoutOrder = groupCounts[group], Name = "Action_" .. text:gsub("%W", "")})
        local _, captionLabel = call(object, "FindFirstChild", "Caption")
        set(captionLabel, {Text = caption, Position = UDim2.new(0, 34, 0.06, 0),
            Size = UDim2.new(1, -40, 0.88, 0), TextXAlignment = Enum.TextXAlignment.Left,
            TextScaled = false, TextSize = 12, TextWrapped = true})
        icon(object, glyph, tint)
        return object
    end
    action("code", "Copy Code", "Copiar código", "copy", semantic.code, function()
        copy(sourceText, "Código copiado")
    end)
    action("code", "Copy Remote", "Copiar remote", "link", semantic.code, function() needSelection(function(entry)
        copy(remoteExpression(entry.info), "Referência do remote copiada")
    end) end)
    action("code", "Copy Args", "Copiar args", "copy", semantic.code, function() needSelection(function(entry)
        if entry.kind == "remote" and not entry.hasOutgoing and not entry.editedSource then
            setStatus("Nenhum argumento de envio capturado neste remote") return
        end
        local okArgs, args = pcall(readableArguments, entry.args)
        if entry.editedSource or okArgs then copy(entry.editedSource or args, "Argumentos copiados")
        else setStatus("Falha ao gerar argumentos: " .. tostring(args)) end
    end) end)
    action("code", "Get Script", "Script de origem", "script", semantic.code, function() needSelection(showScript) end)
    action("code", "Function Info", "Informações", "info", semantic.code, function() needSelection(functionInfo) end)
    runButton = action("run", "Run Code", "Executar chamada", "play", semantic.run, function()
        if busy then cancelReplay() return end
        if documentMode ~= "call" then setStatus("Abra Chamada para executar o remote selecionado") return end
        needSelection(function(entry) runSelected(entry) end)
    end)
    action("run", "Edit Args", "Editar args", "edit", semantic.run, function() needSelection(openSpoof) end)
    action("run", "Reset Args", "Restaurar args", "reset", semantic.run, function() needSelection(function(entry)
        if busy then setStatus("Encerre a espera antes de restaurar os argumentos") return end
        entry.editedSource, entry.editedArgs, entry.callSource = nil, nil, nil
        selectEntry(entry)
        setStatus("Argumentos originais restaurados")
    end) end)
    ignoreButton = action("protect", "Exclude (i)", "Ignorar path", "filter", semantic.ignore, function() needSelection(function(entry)
        spy.ignore[entry.key] = not spy.ignore[entry.key] or nil
        setStatus(spy.ignore[entry.key] and "Este remote foi excluído dos logs" or "Este remote voltou aos logs")
        refreshActions()
    end) end)
    ignoreNameButton = action("protect", "Exclude (n)", "Ignorar nome", "filter", semantic.ignore, function() needSelection(function(entry)
        local key = keyFor(entry.name, entry.method)
        spy.ignoreNames[key] = not spy.ignoreNames[key] or nil
        setStatus(spy.ignoreNames[key] and ("Nome excluído: " .. entry.name) or ("Nome reativado: " .. entry.name))
        refreshActions()
    end) end)
    blockButton = action("protect", "Block (i)", "Bloquear path", "block", semantic.block, function() needSelection(function(entry)
        if entry.direction == "in" then setStatus("Recebidos são somente leitura; use Ignorar para ocultar os logs") return end
        spy.blocked[entry.key] = not spy.blocked[entry.key] or nil
        setStatus(spy.blocked[entry.key] and "Este remote foi bloqueado" or "Este remote foi desbloqueado")
        refreshActions()
    end) end)
    blockNameButton = action("protect", "Block (n)", "Bloquear nome", "block", semantic.block, function() needSelection(function(entry)
        if entry.direction == "in" then setStatus("Recebidos são somente leitura; use Ignorar para ocultar os logs") return end
        local key = keyFor(entry.name, entry.method)
        spy.blockedNames[key] = not spy.blockedNames[key] or nil
        setStatus(spy.blockedNames[key] and ("Nome bloqueado: " .. entry.name) or ("Nome desbloqueado: " .. entry.name))
        refreshActions()
    end) end)
    action("protect", "Clr Blacklist", "Limpar ignorados", "reset", semantic.ignore, function()
        spy.ignore, spy.ignoreNames = {}, {}
        refreshActions() setStatus("Lista de exclusões limpa")
    end)
    action("protect", "Clr Blocklist", "Limpar bloqueios", "reset", semantic.block, function()
        spy.blocked, spy.blockedNames = {}, {}
        refreshActions() setStatus("Lista de bloqueios limpa")
    end)
    action("tools", "Clr Logs", "Limpar logs", "trash", semantic.tool, clear)
    action("tools", "Scan Remotes", "Buscar remotes", "scan", semantic.tool, function()
        scanGame() chooseSource("catalogue")
    end)
    ui.favoriteButton = action("tools", "Favorite", "Favoritar remote", "star", semantic.ignore, function() needSelection(function(entry)
        spy.favorites[entry.remote] = not spy.favorites[entry.remote] or nil
        for _, item in ipairs(entries) do if item.remote == entry.remote then updateRow(item) end end
        local found = catalogueIndex[entry.remote]
        if found then updateRow(found) end
        refreshFilter() refreshActions()
        setStatus(spy.favorites[entry.remote] and "Remote adicionado aos favoritos" or "Remote removido dos favoritos")
    end) end)
    action("tools", "Coverage", "Cobertura", "info", semantic.tool, function()
        setSource("-- COBERTURA DA CAPTURA\n-- Namecall: " .. tostring(spy.coverage.namecall)
            .. "\n-- Inicialização: " .. spy.startup.phase
            .. (#spy.startup.warnings > 0 and ("\n-- Avisos: " .. table.concat(spy.startup.warnings, "\n-- ")) or "")
            .. "\n-- Funções diretas monitoradas: " .. spy.coverage.direct
            .. "\n-- Ícones: " .. spy.icons.message
            .. "\n-- Sinais OnClientEvent: " .. spy.coverage.incoming
            .. "\n-- Remotes encontrados: " .. #catalogue .. " / " .. C.catalogue
            .. "\n-- Eventos locais: BindableEvent.Fire / BindableFunction.Invoke"
            .. "\n-- Somente Instances disponíveis no cliente são visíveis."
            .. "\n-- OnClientInvoke não é substituído."
            .. "\n-- Chamadas diretas dependem de hookfunction compatível."
            .. (#spy.coverage.nativeErrors > 0 and ("\n-- " .. table.concat(spy.coverage.nativeErrors, "\n-- ")) or ""), "info")
        setStatus("Cobertura real disponível neste executor")
    end)
    action("tools", "Direct Capture", "Captura direta", "scan", semantic.tool, function()
        local enabled = spy.coverage.direct == 0
        local done, reason = spy.enableDirect(enabled)
        if done then setStatus(enabled and ("Captura direta ativada: " .. spy.coverage.direct .. " funções") or "Captura direta desativada")
        else setStatus("Falha na captura direta: " .. tostring(reason)) end
    end)
    for _, controls in pairs(ui.actionButtons) do controls.fit() end
    setActionGroup(ui.actionGroup)
    modal = make("Frame", {Name = "ArgsEditor", Size = UDim2.fromScale(1, 1), BackgroundColor3 = bg,
        BorderSizePixel = 0, Visible = false, ZIndex = 3}, detail)
    button(modal, "Cancelar", UDim2.fromOffset(6, 4), UDim2.new(0.48, -6, 0, 28), function()
        if busy then cancelReplay() end
        call(codeBox, "ReleaseFocus")
        set(modal, {Visible = false})
    end)
    callButton = button(modal, "Executar chamada", UDim2.new(0.50, 0, 0, 4), UDim2.new(0.50, -6, 0, 28))
    local editorScroll = make("ScrollingFrame", {Position = UDim2.fromOffset(6, 40),
        Size = UDim2.new(1, -12, 1, -46), BackgroundColor3 = editorBG, BorderSizePixel = 0,
        CanvasSize = UDim2.new(), AutomaticCanvasSize = Enum.AutomaticSize.Y, ScrollBarThickness = 6}, modal)
    codeBox = make("TextBox", {Name = "ArgsText", Position = UDim2.fromOffset(6, 4), Size = UDim2.new(1, -18, 0, 100),
        AutomaticSize = Enum.AutomaticSize.Y, BackgroundTransparency = 1, Text = "", TextColor3 = ink,
        TextSize = 13, Font = Enum.Font.Code, TextWrapped = true, ClearTextOnFocus = false,
        MultiLine = true, TextXAlignment = Enum.TextXAlignment.Left, TextYAlignment = Enum.TextYAlignment.Top}, editorScroll)
    copyDialog = make("Frame", {Name = "CopyDialog", Size = UDim2.fromScale(1, 1), BackgroundColor3 = bg,
        BorderSizePixel = 0, Visible = false, ZIndex = 6}, detail)
    local copyTitle = label(copyDialog, "Copiar código", UDim2.fromOffset(8, 6), UDim2.new(1, -16, 0, 22))
    set(copyTitle, {Font = Enum.Font.SourceSansBold, TextSize = 18})
    button(copyDialog, "Voltar", UDim2.fromOffset(6, 34), UDim2.new(0.48, -6, 0, 28), function()
        call(copyBox, "ReleaseFocus")
        set(copyDialog, {Visible = false})
    end)
    button(copyDialog, "Selecionar tudo", UDim2.new(0.50, 0, 0, 34), UDim2.new(0.50, -6, 0, 28), function()
        call(copyBox, "CaptureFocus")
        set(copyBox, {SelectionStart = 1, CursorPosition = #(get(copyBox, "Text") or "") + 1})
        setStatus("Texto selecionado; toque em Copiar no teclado")
    end)
    local copyScroll = make("ScrollingFrame", {Position = UDim2.fromOffset(6, 70),
        Size = UDim2.new(1, -12, 1, -76), BackgroundColor3 = editorBG, BorderSizePixel = 0,
        CanvasSize = UDim2.new(1, 0, 0, 0), AutomaticCanvasSize = Enum.AutomaticSize.Y,
        ScrollBarThickness = 6}, copyDialog)
    copyBox = make("TextBox", {Name = "CopyText", Position = UDim2.fromOffset(6, 4),
        Size = UDim2.new(1, -18, 0, 100), AutomaticSize = Enum.AutomaticSize.Y,
        BackgroundTransparency = 1, Text = "", RichText = false, TextColor3 = ink,
        TextSize = 13, Font = Enum.Font.Code, MultiLine = true, TextWrapped = true,
        ClearTextOnFocus = false, TextXAlignment = Enum.TextXAlignment.Left,
        TextYAlignment = Enum.TextYAlignment.Top}, copyScroll)
    ui.helpPanel = make("Frame", {Name = "HelpPanel", Position = UDim2.fromOffset(8, C.titleHeight + 4),
        Size = UDim2.new(1, -16, 1, -C.titleHeight - 32), BackgroundColor3 = panel,
        BorderSizePixel = 0, ZIndex = 50, Visible = false}, window)
    round(ui.helpPanel, 9, violet)
    local helpTitle = label(ui.helpPanel, "Como usar o ignite Spy", UDim2.fromOffset(12, 10), UDim2.new(1, -24, 0, 24))
    set(helpTitle, {Font = Enum.Font.GothamBold, TextSize = 16})
    local helpScroll = make("ScrollingFrame", {Position = UDim2.fromOffset(10, 43),
        Size = UDim2.new(1, -20, 1, -95), BackgroundTransparency = 1, BorderSizePixel = 0,
        CanvasSize = UDim2.new(1, 0, 0, 0), AutomaticCanvasSize = Enum.AutomaticSize.Y, ScrollBarThickness = 4}, ui.helpPanel)
    local helpText = label(helpScroll,
        "Toque em um remote para abrir os detalhes.\n\n"
        .. "Todos / Eventos / Funções filtram a lista. A busca também procura nos argumentos.\n\n"
        .. "Chamadas mostra o tráfego capturado. Encontrados lista remotes existentes no cliente, mesmo sem atividade.\n\n"
        .. "Código: copiar código, remote e argumentos; script de origem e informações.\n\n"
        .. "Execução: executar, editar argumentos e restaurar os originais. Eventos recebidos são somente leitura.\n\n"
        .. "Proteção: ignorar logs, bloquear envios e limpar essas listas.\n\n"
        .. "Ferramentas: limpar logs, buscar remotes, favoritar e consultar a cobertura. A estrela ao lado da busca filtra favoritos.\n\n"
        .. "Captura direta é opcional. Ative em Ferramentas se seu executor oferecer hookfunction compatível.\n\n"
        .. "Exclude remove dos logs; Block impede a chamada. (i) vale para este caminho e método; (n) vale para o mesmo nome e método.\n\n"
        .. "Live acompanha o final da lista. Manual permite navegar pelo histórico.\n\n"
        .. "Em telas estreitas, use Remotes e Detalhes para alternar as áreas.\n\n"
        .. "Get Script depende da origem e das funções que o executor disponibiliza.\n\n"
        .. "Parar espera libera os controles; não desfaz uma chamada já enviada.",
        UDim2.new(), UDim2.new(1, -10, 0, 0))
    set(helpText, {Font = Enum.Font.Gotham, TextSize = 12, TextWrapped = true, AutomaticSize = Enum.AutomaticSize.Y})
    button(ui.helpPanel, "Entendi", UDim2.new(0, 12, 1, -44), UDim2.new(1, -24, 0, 32), function()
        set(ui.helpPanel, {Visible = false})
    end)
    ui.statusDot = make("Frame", {Position = UDim2.new(0, 10, 1, -16), Size = UDim2.fromOffset(6, 6),
        BackgroundColor3 = Color3.fromRGB(92, 219, 158), BorderSizePixel = 0}, window)
    round(ui.statusDot, 3)
    statusLabel = label(window, "Pronto", UDim2.new(0, 24, 1, -20), UDim2.new(1, -34, 0, 18))
    set(statusLabel, {TextSize = 10, TextColor3 = muted, TextTruncate = Enum.TextTruncate.AtEnd})
    setSource("-- Selecione um item em Chamadas ou Encontrados.\n-- Amarelo: RemoteEvent\n-- Roxo: RemoteFunction\n-- Laranja: UnreliableRemoteEvent\n-- Ciano: BindableEvent\n-- Verde: BindableFunction\n-- Ações organizadas nas quatro abas abaixo.")
    local dragging, dragInput, origin, position
    on(header, "InputBegan", function(event)
        local kind = get(event, "UserInputType")
        if kind == Enum.UserInputType.MouseButton1 or kind == Enum.UserInputType.Touch then
            dragging, dragInput = true, event
            origin, position = get(event, "Position"), get(window, "Position")
        end
    end)
    on(input, "InputChanged", function(event)
        if not dragging then return end
        if event ~= dragInput and get(event, "UserInputType") ~= Enum.UserInputType.MouseMovement then return end
        local delta = get(event, "Position") - origin
        local nextPosition = UDim2.new(position.X.Scale, position.X.Offset + delta.X,
            position.Y.Scale, position.Y.Offset + delta.Y)
        local viewport, size = get(gui, "AbsoluteSize"), get(window, "AbsoluteSize")
        if typeof(viewport) == "Vector2" and typeof(size) == "Vector2" then
            nextPosition = UDim2.fromOffset(
                math.max(0, math.min(viewport.X - math.min(size.X, viewport.X), viewport.X * nextPosition.X.Scale + nextPosition.X.Offset)),
                math.max(0, math.min(viewport.Y - C.titleHeight, viewport.Y * nextPosition.Y.Scale + nextPosition.Y.Offset)))
        end
        set(window, {Position = nextPosition})
    end)
    on(input, "InputEnded", function(event)
        if event == dragInput then dragging, dragInput = false, nil end
    end)
    local elapsed = 0
    on(run, "Heartbeat", function(dt)
        if #retiredRemotes > 0 then
            for _, entry in ipairs(retiredRemotes) do removeEntry(entry) end
            table.clear(retiredRemotes)
        end
        pumpLogger()
        if layoutDirty then layoutEntries() end
        elapsed = elapsed + dt
        if elapsed < 0.1 then return end
        elapsed = 0
        set(titleLabel, {Text = "ignite Spy"})
        set(pauseButton, {Text = spy.enabled and "Ⅱ" or "▶"})
        set(followButton, {Text = spy.follow and "Live" or "Manual"})
        set(ui.captureBadge, {Text = spy.enabled and "AO VIVO" or "PAUSADO",
            TextColor3 = spy.enabled and Color3.fromRGB(105, 226, 168) or Color3.fromRGB(242, 199, 96),
            BackgroundColor3 = spy.enabled and Color3.fromRGB(22, 55, 42) or Color3.fromRGB(59, 46, 26)})
        set(statsLabel, {Text = ui.source == "catalogue" and (#catalogue .. " encontrados · " .. spy.coverage.incoming .. " RX")
            or total .. " chamadas · " .. #entries .. " logs"
            .. (logFailures > 0 and (" · erros " .. logFailures) or "")})
        for bucket in pairs(dirty) do
            local entry = bucket.group
            if entry and not entry.dead then updateRow(entry) end
            dirty[bucket] = nil
        end
        local now = os.clock()
        for key, bucket in pairs(rates) do if now - bucket.last > C.window then rates[key] = nil end end
        if selected then refreshActions() end
    end)
    responsiveLayout(ui.width or C.windowMaxWidth)
    refreshActions()
end


-- SPOOF
openSpoof = function(entry)
    if busy then setStatus("Uma chamada ainda aguarda retorno") return end
    if entry.direction == "in" then setStatus("Eventos recebidos são somente leitura; copie os argumentos para inspecionar") return end
    local ok, source = pcall(literalArguments, entry.args)
    editing = entry
    set(codeBox, {Text = entry.editedSource or (ok and source or "")})
    set(modal, {Visible = true})
    setStatus((entry.editedSource or ok) and "Edite expressões Luau; nils finais são preservados"
        or ("Não foi gerado literal: " .. tostring(source) .. ". Digite os argumentos manualmente."))
end
cancelReplay = function()
    if not busy then return end
    runToken = runToken + 1
    local thread = inflightThread
    inflightThread, busy = nil, false
    if thread then
        spy.spoofing[thread] = nil
        if type(task.cancel) == "function" and thread ~= coroutine.running() then pcall(task.cancel, thread) end
    end
    set(callButton, {Text = "Executar chamada"})
    refreshActions()
    setStatus("Espera encerrada; a chamada enviada não é desfeita")
end
executeSpoof = function()
        if busy or not editing or editing.dead then return end
        local entry, source = editing, get(codeBox, "Text") or ""
        if type(loadstring) ~= "function" then setStatus("loadstring indisponível") return end
        if #source > C.literalBytes then setStatus("Editor limitado a 1 MB") return end
        local ok, chunk, compileError = pcall(loadstring, "return " .. source, "IgniteSpyArguments")
        if not ok or not chunk then setStatus("Sintaxe: " .. tostring(compileError or chunk)) return end
        busy = true
        runToken = runToken + 1
        local token = runToken
        set(callButton, {Text = "Aguardando…"})
        refreshActions()
        local spawned = task.spawn(function()
            local thread = coroutine.running()
            -- A marca é global pela API, mas pertence à thread para não ocultar outras chamadas.
            spy.spoofing[thread] = true
            local returned = table.pack(pcall(function()
                local target = resolve(entry.info)
                assert(target == entry.remote, "O path agora aponta para outra Instance")
                assert(classes[get(target, "ClassName")] == entry.method, "Classe/método incompatível")
                local args = table.pack(chunk())
                entry.editedSource, entry.editedArgs = source, args
                local generated, code = pcall(callSource, entry)
                entry.callSource = generated and code or nil
                if generated and selected == entry and documentMode == "call" then setSource(code) end
                if not alive then error("Spy descarregado", 0) end
                -- Dot call evita depender do estado interno de getnamecallmethod fora do hook.
                local method = get(target, entry.method)
                assert(type(method) == "function", "Método indisponível")
                return method(target, table.unpack(args, 1, args.n))
            end))
            spy.spoofing[thread] = nil
            if token ~= runToken or not alive then return end
            busy, inflightThread = false, nil
            set(callButton, {Text = "Executar chamada"})
            refreshActions()
            if returned[1] then
                local result = {n = returned.n - 1}
                for i = 2, returned.n do result[i - 1] = returned[i] end
                entry.lastResult = result
                local plain = displayArguments(result)
                setStatus("Executado; retorno: " .. short(plain:gsub("\n", " | "), 240))
            else setStatus("Falha: " .. tostring(returned[2])) end
        end)
        inflightThread = busy and spawned or nil
end
runSelected = function(entry)
    if busy then setStatus("Uma chamada ainda aguarda retorno") return end
    if entry.direction == "in" then setStatus("Eventos recebidos são somente leitura; não existe reenvio de OnClientEvent") return end
    if not isReplayable(entry) then
        openSpoof(entry)
        setStatus("Nenhum envio capturado; informe os argumentos antes de confirmar a chamada")
        return
    end
    local ok, value = pcall(literalArguments, entry.args)
    local source = entry.editedSource or (ok and value)
    if not source then setStatus("Use Edit Args: " .. tostring(value)) return end
    editing = entry
    set(codeBox, {Text = source})
    executeSpoof()
end
local function bindSpoof()
    on(callButton, "Activated", executeSpoof)
end

-- UNLOAD
unload = function()
    if restored then return true end
    if busy and cancelReplay then cancelReplay() end
    if pendingScript and cancelScriptLoad then cancelScriptLoad() end
    call(codeBox, "ReleaseFocus")
    call(copyBox, "ReleaseFocus")
    alive, spy.enabled = false, false
    discoveryGeneration = discoveryGeneration + 1
    local ok, err = true, nil
    local failures = {}
    local directDone, directError = restoreDirectHooks()
    if not directDone then failures[#failures + 1] = "hookfunction: " .. tostring(directError) end
    if installed and type(oldNamecall) == "function" then
        if useHook then
            ok, err = pcall(hookmetamethod, game, "__namecall", oldNamecall)
        else
            ok, err = pcall(function()
                setreadonly(rawMT, false)
                local written, writeError = pcall(rawset, rawMT, "__namecall", oldNamecall)
                local locked, lockError = pcall(setreadonly, rawMT, true)
                assert(written, writeError)
                assert(locked, lockError)
            end)
        end
    end
    if not ok then failures[#failures + 1] = "__namecall: " .. tostring(err) end
    disconnect(connections)
    for _, entry in ipairs(entries) do removeEntry(entry) end
    for _, entry in ipairs(catalogue) do disconnect(entry.watchers) removeEntry(entry) end
    for _, entry in ipairs(retiredRemotes) do removeEntry(entry) end
    table.clear(retiredRemotes)
    table.clear(catalogue)
    spy.coverage.namecall, spy.coverage.direct, spy.coverage.incoming, spy.coverage.discovered = false, 0, 0, 0
    destroy(gui)
    entries, rates, dirty, queue, pathCache = {}, {}, {}, {}, setmetatable({}, {__mode = "k"})
    selected, editing, gui = nil, nil, nil
    window, list, detail, modal, argsLabel, metaLabel, codeBox = nil, nil, nil, nil, nil, nil, nil
    titleLabel, statusLabel, pauseButton, blockButton, ignoreButton, callButton = nil, nil, nil, nil, nil, nil
    codeLines, codeScroll, body, ignoreNameButton, blockNameButton = nil, nil, nil, nil, nil
    statsLabel, emptyLabel = nil, nil
    table.clear(ui)
    copyDialog, copyBox, searchBox, followButton, runButton, modeLabel = nil, nil, nil, nil, nil, nil
    sourceText, sourceReady = "", false
    if #failures > 0 then return false, "Não foi possível restaurar os hooks: " .. table.concat(failures, "; ") end
    restored, installed = true, false
    if rawget(env, "RemoteSpy") == spy then env.RemoteSpy = nil end
    if rawget(env, "IgniteSpy") == spy then env.IgniteSpy = nil end
    return true
end
spy.unload = unload
local ok, err = pcall(function()
    spy.startup.phase = "interface"
    buildUI()
    bindSpoof()
end)
if not ok then
    local cleaned, cleanupError = unload()
    error("ignite Spy: " .. tostring(err) .. (cleaned and "" or ("; " .. tostring(cleanupError))), 0)
end
env.IgniteSpy = spy
env.RemoteSpy = spy
local function startPart(name, callback)
    spy.startup.phase = name
    local done, reason = pcall(callback)
    if not done then
        local warning = name .. ": " .. tostring(reason)
        spy.startup.warnings[#spy.startup.warnings + 1] = warning
        spy.lastError = warning
        pcall(warn, "ignite Spy: " .. warning)
    end
    return done
end
startPart("captura", installHook)
startPart("descoberta", startDiscovery)
startPart("ícones", startIcons)
spy.startup.ready, spy.startup.phase = true, "pronto"
setStatus(#spy.startup.warnings > 0 and ("Erro na inicialização · " .. spy.startup.warnings[1] .. " · Veja Ferramentas > Cobertura")
    or "Pronto · Captura direta opcional em Ferramentas · Ícones carregam em segundo plano")
return spy

end

local booted, result = xpcall(boot, function(message)
    local text = tostring(message)
    pcall(warn, "ignite Spy: " .. text)
    pcall(function()
        game:GetService("StarterGui"):SetCore("SendNotification", {Title = "ignite Spy · erro ao abrir",
            Text = text:sub(1, 220), Duration = 15})
    end)
    if type(debug) == "table" and type(debug.traceback) == "function" then
        local ok, trace = pcall(debug.traceback, text, 2)
        if ok then return trace end
    end
    return text
end)
if not booted then error(result, 0) end
return result
