-- CONFIG
assert(type(getgenv) == "function", "getgenv indisponível")
local env = getgenv()
local previous = rawget(env, "IgniteSpy") or rawget(env, "RemoteSpy")
if type(previous) == "table" and type(previous.unload) == "function" then
    local ok, result, reason = pcall(previous.unload)
    assert(ok and result ~= false, "Unload anterior falhou: " .. tostring(reason or result))
end
assert(type(getnamecallmethod) == "function", "getnamecallmethod indisponível")
local useHook = type(hookmetamethod) == "function"
assert(useHook or (type(getrawmetatable) == "function" and type(setreadonly) == "function"),
    "É necessário hookmetamethod ou getrawmetatable + setreadonly")
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
local responsiveLayout, matchesEntry
local uiIdentity
if type(identityGetter) == "function" then
    local ok, identity = pcall(identityGetter)
    if ok and type(identity) == "number" then uiIdentity = identity end
end
spy.version = "2.4.1"
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
    if type(newcclosure) == "function" then hook = newcclosure(hook) end
    if useHook then
        oldNamecall = hookmetamethod(game, "__namecall", hook)
    else
        rawMT = getrawmetatable(game)
        oldNamecall = rawget(rawMT, "__namecall")
        assert(type(oldNamecall) == "function", "__namecall original inválido")
        setreadonly(rawMT, false)
        local ok, err = pcall(rawset, rawMT, "__namecall", hook)
        local locked, lockErr = pcall(setreadonly, rawMT, true)
        if not ok then error(err, 0) end
        installed = true
        if not locked then error(lockErr, 0) end
    end
    installed = true
    assert(type(oldNamecall) == "function", "Executor não retornou o namecall original")
    spy.coverage.namecall = true
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
                if type(newcclosure) == "function" then replacement = newcclosure(replacement) end
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
}, file = "IgniteSpy_Icons_v1.png", bytes = 29924, image = nil}
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
    local image = make("ImageLabel", {Name = "Glyph", Size = UDim2.fromScale(1, 1),
        BackgroundTransparency = 1, BorderSizePixel = 0, Image = "", ImageColor3 = color,
        ScaleType = Enum.ScaleType.Fit, ZIndex = 19}, canvas)
    local node = {image = image, fallback = fallback, kind = kind}
    iconAssets.nodes[canvas] = node
    on(image, "Changed", function(property)
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
    local parented = ok and pcall(function() gui.Parent = core end)
    if not parented then
        local found, playerGui = call(get(players, "LocalPlayer"), "FindFirstChildOfClass", "PlayerGui")
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
    for index = #nativeHooks, 1, -1 do
        local record = nativeHooks[index]
        if not record.restored then
            local done, reason = pcall(hookfunction, record.target, record.original)
            if done then record.restored = true
            else failures[#failures + 1] = "hookfunction: " .. tostring(reason) end
        end
    end
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
    buildUI()
    bindSpoof()
    startIcons()
    installHook()
    installDirectHooks()
    startDiscovery()
end)
if not ok then
    local cleaned, cleanupError = unload()
    error("ignite Spy: " .. tostring(err) .. (cleaned and "" or ("; " .. tostring(cleanupError))), 0)
end
env.IgniteSpy = spy
env.RemoteSpy = spy
setStatus("Pronto · Código / Execução / Proteção / Ferramentas · Encontrados lista os remotes do cliente")
return spy
