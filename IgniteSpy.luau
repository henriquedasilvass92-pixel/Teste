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
spy.version = "2.4.0"
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
local function icon(parent, kind, color)
    local canvas = make("Frame", {Name = "Icon", Position = UDim2.new(0, 10, 0.5, -8),
        Size = UDim2.fromOffset(16, 16), BackgroundTransparency = 1, Active = false, ZIndex = 17}, parent)
    local function line(x, y, w, h, rotation)
        return make("Frame", {Position = UDim2.fromOffset(x, y), Size = UDim2.fromOffset(w, h),
            Rotation = rotation or 0, BorderSizePixel = 0, BackgroundColor3 = color, ZIndex = 18}, canvas)
    end
    local function box(x, y, w, h)
        local frame = make("Frame", {Position = UDim2.fromOffset(x, y), Size = UDim2.fromOffset(w, h),
            BackgroundTransparency = 1, BorderSizePixel = 0, ZIndex = 18}, canvas)
        round(frame, 2, color)
    end
    if kind == "play" then
        line(3, 1, 2, 14) line(5, 3, 8, 2, 35) line(5, 11, 8, 2, -35)
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
    action("code", "Get Script", "Script de origem", "copy", semantic.code, function() needSelection(showScript) end)
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
