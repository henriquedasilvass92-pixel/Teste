-- CONFIG
assert(type(getgenv) == "function", "getgenv indisponível")
local env = getgenv()
local previous = rawget(env, "RemoteSpy")
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
    literalFields = 4096, literalBytes = 1000000}
local methods = {FireServer = true, InvokeServer = true, Fire = true}
local classes = {RemoteEvent = "FireServer", UnreliableRemoteEvent = "FireServer",
    RemoteFunction = "InvokeServer", BindableEvent = "Fire"}
local colors = {string = "85DB9D", number = "F4D477", boolean = "C6A1F6",
    ["nil"] = "9BA5B5", Instance = "70DDE8", table = "B1BCDA",
    other = "EAA887", error = "F18C99"}
local spy = {enabled = true, ignore = {}, blocked = {},
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
local function quote(value) return string.format("%q", value) end
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

-- HOOK
local function removeEntry(entry)
    entry.dead = true
    disconnect(entry.connections)
    destroy(entry.row)
    if entry.bucket.group == entry then entry.bucket.group = nil end
    if selected == entry then
        selected, editing = nil, nil
        set(detail, {Visible = false})
        set(modal, {Visible = false})
    end
end
local function newEntry(job, collapsed)
    if not alive or job.epoch ~= epoch then return end
    if collapsed then
        for i = #entries, 1, -1 do
            if entries[i].bucket == job.bucket then
                removeEntry(entries[i])
                table.remove(entries, i)
            end
        end
    end
    serial = serial + 1
    local plain, rich = displayArguments(job.args)
    local _, summary = displayArguments(job.args, true)
    local entry = {remote = job.remote, info = job.info, key = job.key,
        method = job.method, class = job.class, args = job.args, at = job.at,
        blocked = job.blocked, plain = plain, rich = rich, summary = summary, bucket = job.bucket,
        collapsed = collapsed, connections = {}, order = serial}
    entry.search = string.lower(entry.info.path .. "\n" .. entry.method .. "\n" .. plain)
    entries[#entries + 1] = entry
    if collapsed then job.bucket.group = entry end
    renderEntry(entry)
    while #entries > C.entries do removeEntry(table.remove(entries, 1)) end
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
    if workerRunning then return end
    workerRunning = true
    task.defer(function()
        local processed = 0
        while alive and qHead <= qTail do
            local item = queue[qHead]
            queue[qHead], qHead = nil, qHead + 1
            if item then
                local ok, err = pcall(process, item)
                if not ok then setStatus("Logger: " .. tostring(err)) end
            end
            processed = processed + 1
            if processed % 12 == 0 then task.wait() end
        end
        if qHead > qTail then queue, qHead, qTail = {}, 1, 0 end
        workerRunning = false
    end)
end
local function capture(remote, method, class, args)
    local info = getInfo(remote)
    local key, now = keyFor(info.path, method), os.clock()
    local blocked = spy.blocked[key] == true
    if not spy.enabled or spy.ignore[key] then return blocked end
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
    enqueue({remote = remote, info = info, key = key, method = method, class = class,
        args = args, at = now - started, blocked = blocked, bucket = bucket, epoch = epoch})
    return blocked
end
installHook = function()
    hook = function(self, ...)
        local method = getnamecallmethod()
        if not methods[method] or typeof(self) ~= "Instance" then return oldNamecall(self, ...) end
        if not alive or spy.spoofing[coroutine.running()] then return oldNamecall(self, ...) end
        local class = get(self, "ClassName")
        if classes[class] ~= method then return oldNamecall(self, ...) end
        local args = table.pack(...)
        local ok, blocked = pcall(capture, self, method, class, args)
        if ok and blocked then return nil end
        if method == "InvokeServer" then
            local returned = table.pack(oldNamecall(self, table.unpack(args, 1, args.n)))
            return table.unpack(returned, 1, returned.n)
        end
        return oldNamecall(self, table.unpack(args, 1, args.n))
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
end

-- UI
local bg, panel, ink = Color3.fromRGB(19, 23, 33), Color3.fromRGB(30, 36, 49), Color3.fromRGB(224, 231, 242)
local function label(parent, text, position, size)
    return make("TextLabel", {BackgroundTransparency = 1, Text = text, TextColor3 = ink,
        TextSize = 12, Font = Enum.Font.Code, TextXAlignment = Enum.TextXAlignment.Left,
        TextYAlignment = Enum.TextYAlignment.Top, Position = position, Size = size}, parent)
end
local function button(parent, text, position, size, callback, bucket)
    local object = make("TextButton", {Text = text, TextColor3 = ink, TextSize = 12,
        Font = Enum.Font.GothamMedium, BackgroundColor3 = Color3.fromRGB(49, 60, 79),
        BorderSizePixel = 0, Position = position, Size = size, AutoButtonColor = true}, parent)
    make("UICorner", {CornerRadius = UDim.new(0, 5)}, object)
    if callback then on(object, "Activated", callback, bucket) end
    return object
end
setStatus = function(text) if alive then set(statusLabel, {Text = short(text, 300)}) end end
refreshActions = function()
    if not selected then return end
    set(blockButton, {Text = spy.blocked[selected.key] and "Desbloquear" or "Block"})
    set(ignoreButton, {Text = spy.ignore[selected.key] and "Designorar" or "Ignore"})
end
refreshFilter = function()
    for _, entry in ipairs(entries) do
        set(entry.row, {Visible = query == "" or entry.search:find(query, 1, true) ~= nil})
    end
end
selectEntry = function(entry)
    if entry.dead then return end
    selected = entry
    set(metaLabel, {Text = entry.info.path .. "\n" .. entry.method .. " · " .. entry.class
        .. (entry.collapsed and " · amostra do grupo" or "")})
    set(argsLabel, {Text = entry.rich})
    set(detail, {Visible = true})
    refreshActions()
end
renderEntry = function(entry)
    local row = make("TextButton", {Size = UDim2.new(1, -8, 0, 88), Text = "",
        BackgroundColor3 = panel, BorderSizePixel = 0, LayoutOrder = entry.order,
        Visible = query == "" or entry.search:find(query, 1, true) ~= nil}, list)
    entry.row = row
    local badge = entry.class == "UnreliableRemoteEvent" and "Unreliable"
        or entry.class == "BindableEvent" and "Bindable"
        or entry.method == "InvokeServer" and "Invoke" or "Fire"
    local tint = badge == "Invoke" and Color3.fromRGB(125, 100, 192)
        or badge == "Unreliable" and Color3.fromRGB(173, 111, 54)
        or badge == "Bindable" and Color3.fromRGB(67, 143, 114) or Color3.fromRGB(54, 118, 176)
    entry.countLabel = label(row, "", UDim2.fromOffset(8, 5), UDim2.new(1, -110, 0, 18))
    local tag = label(row, badge, UDim2.new(1, -98, 0, 4), UDim2.fromOffset(90, 18))
    set(tag, {BackgroundTransparency = 0, BackgroundColor3 = tint,
        TextXAlignment = Enum.TextXAlignment.Center})
    local path = label(row, entry.info.path, UDim2.fromOffset(8, 27), UDim2.new(1, -16, 0, 18))
    set(path, {TextTruncate = Enum.TextTruncate.AtEnd})
    local summary = label(row, entry.summary:gsub("\n", "  "), UDim2.fromOffset(8, 48), UDim2.new(1, -16, 0, 34))
    set(summary, {RichText = true, TextWrapped = true, ClipsDescendants = true})
    set(entry.countLabel, {Text = string.format("+%.3fs%s%s", entry.at,
        entry.collapsed and (" · ×" .. entry.bucket.total) or "",
        entry.blocked and " · BLOCK" or "")})
    on(row, "Activated", function() selectEntry(entry) end, entry.connections)
end
local function clear()
    epoch = epoch + 1
    for _, entry in ipairs(entries) do removeEntry(entry) end
    entries, rates, dirty, queue, qHead, qTail = {}, {}, {}, {}, 1, 0
    total, dropped, selected, editing = 0, 0, nil, nil
    set(detail, {Visible = false})
    set(modal, {Visible = false})
    setStatus("Lista limpa")
end
local function buildUI()
    local ok, core = call(game, "GetService", "CoreGui")
    local _, players = call(game, "GetService", "Players")
    local _, input = call(game, "GetService", "UserInputService")
    local _, run = call(game, "GetService", "RunService")
    gui = make("ScreenGui", {Name = "RemoteSpy", IgnoreGuiInset = true,
        DisplayOrder = 100000, ResetOnSpawn = false, ZIndexBehavior = Enum.ZIndexBehavior.Sibling})
    local parented = ok and pcall(function() gui.Parent = core end)
    if not parented then
        local player = get(players, "LocalPlayer")
        local found, playerGui = call(player, "FindFirstChildOfClass", "PlayerGui")
        assert(found and playerGui, "CoreGui e PlayerGui indisponíveis")
        local attached, err = pcall(function() gui.Parent = playerGui end)
        assert(attached, err)
    end
    window = make("Frame", {Size = UDim2.fromScale(0.94, 0.84), Position = UDim2.fromScale(0.03, 0.08),
        BackgroundColor3 = bg, BorderSizePixel = 0, Active = true, ClipsDescendants = true}, gui)
    make("UISizeConstraint", {MaxSize = Vector2.new(1040, 760), MinSize = Vector2.new(290, 260)}, window)
    make("UICorner", {CornerRadius = UDim.new(0, 9)}, window)
    local header = make("Frame", {Size = UDim2.new(1, -48, 0, 32), BackgroundTransparency = 1,
        Active = true}, window)
    titleLabel = label(header, "REMOTE SPY · 0", UDim2.fromOffset(10, 8), UDim2.new(1, -12, 1, -8))
    button(window, "×", UDim2.new(1, -36, 0, 4), UDim2.fromOffset(30, 26), function()
        local done, err = unload()
        if not done then warn("RemoteSpy: " .. tostring(err)) end
    end)
    pauseButton = button(window, "Pausar", UDim2.fromOffset(8, 39), UDim2.fromOffset(78, 28), function()
        spy.enabled = not spy.enabled
        set(pauseButton, {Text = spy.enabled and "Pausar" or "Retomar"})
    end)
    button(window, "Limpar", UDim2.fromOffset(92, 39), UDim2.fromOffset(65, 28), clear)
    local search = make("TextBox", {Position = UDim2.fromOffset(164, 39), Size = UDim2.new(1, -172, 0, 28),
        BackgroundColor3 = panel, Text = "", PlaceholderText = "Buscar path / args",
        PlaceholderColor3 = Color3.fromRGB(143, 154, 177), TextColor3 = ink, TextSize = 12,
        Font = Enum.Font.Code, ClearTextOnFocus = false, BorderSizePixel = 0}, window)
    local changed = get(search, "Changed")
    local connection = changed:Connect(function(property)
        if alive and property == "Text" then
            query = string.lower(get(search, "Text") or "")
            refreshFilter()
        end
    end)
    connections[#connections + 1] = connection
    local content = make("Frame", {Position = UDim2.fromOffset(8, 76), Size = UDim2.new(1, -16, 1, -104),
        BackgroundTransparency = 1}, window)
    list = make("ScrollingFrame", {Size = UDim2.fromScale(1, 1), BackgroundTransparency = 1,
        BorderSizePixel = 0, ScrollBarThickness = 5, CanvasSize = UDim2.new(),
        AutomaticCanvasSize = Enum.AutomaticSize.Y}, content)
    make("UIListLayout", {Padding = UDim.new(0, 6), SortOrder = Enum.SortOrder.LayoutOrder}, list)
    detail = make("Frame", {Size = UDim2.fromScale(1, 1), BackgroundColor3 = bg,
        BorderSizePixel = 0, Visible = false, ZIndex = 2}, content)
    button(detail, "Voltar", UDim2.fromOffset(0, 0), UDim2.new(0.23, 0, 0, 28), function()
        set(detail, {Visible = false})
    end)
    blockButton = button(detail, "Block", UDim2.new(0.25, 0, 0, 0), UDim2.new(0.23, 0, 0, 28), function()
        if selected then spy.blocked[selected.key] = not spy.blocked[selected.key] or nil end
        refreshActions()
    end)
    ignoreButton = button(detail, "Ignore", UDim2.new(0.50, 0, 0, 0), UDim2.new(0.23, 0, 0, 28), function()
        if selected then spy.ignore[selected.key] = not spy.ignore[selected.key] or nil end
        refreshActions()
    end)
    button(detail, "Spoof / Call", UDim2.new(0.75, 0, 0, 0), UDim2.new(0.25, 0, 0, 28), function()
        if selected then openSpoof(selected) end
    end)
    local detailScroll = make("ScrollingFrame", {Position = UDim2.fromOffset(0, 36),
        Size = UDim2.new(1, 0, 1, -36), BackgroundTransparency = 1, BorderSizePixel = 0,
        CanvasSize = UDim2.new(), AutomaticCanvasSize = Enum.AutomaticSize.Y, ScrollBarThickness = 5}, detail)
    make("UIListLayout", {Padding = UDim.new(0, 12), SortOrder = Enum.SortOrder.LayoutOrder}, detailScroll)
    metaLabel = label(detailScroll, "", UDim2.new(), UDim2.new(1, -12, 0, 0))
    set(metaLabel, {AutomaticSize = Enum.AutomaticSize.Y, TextWrapped = true, LayoutOrder = 1})
    argsLabel = label(detailScroll, "", UDim2.new(), UDim2.new(1, -12, 0, 0))
    set(argsLabel, {AutomaticSize = Enum.AutomaticSize.Y, RichText = true,
        TextWrapped = true, LayoutOrder = 2})
    modal = make("Frame", {Size = UDim2.fromScale(1, 1), BackgroundColor3 = bg,
        BorderSizePixel = 0, Visible = false, ZIndex = 3}, content)
    button(modal, "Cancelar", UDim2.new(), UDim2.new(0.47, 0, 0, 28), function()
        set(modal, {Visible = false})
    end)
    callButton = button(modal, "Executar chamada", UDim2.new(0.50, 0, 0, 0), UDim2.new(0.50, 0, 0, 28))
    local editorScroll = make("ScrollingFrame", {Position = UDim2.fromOffset(0, 36),
        Size = UDim2.new(1, 0, 1, -36), BackgroundColor3 = panel, BorderSizePixel = 0,
        CanvasSize = UDim2.new(), AutomaticCanvasSize = Enum.AutomaticSize.Y, ScrollBarThickness = 6}, modal)
    codeBox = make("TextBox", {Position = UDim2.fromOffset(6, 4), Size = UDim2.new(1, -18, 0, 100),
        AutomaticSize = Enum.AutomaticSize.Y, BackgroundTransparency = 1, Text = "",
        TextColor3 = ink, TextSize = 13, Font = Enum.Font.Code, TextWrapped = true,
        TextXAlignment = Enum.TextXAlignment.Left, TextYAlignment = Enum.TextYAlignment.Top,
        ClearTextOnFocus = false, MultiLine = true}, editorScroll)
    statusLabel = label(window, "Pronto", UDim2.new(0, 8, 1, -23), UDim2.new(1, -16, 0, 18))
    set(statusLabel, {TextTruncate = Enum.TextTruncate.AtEnd})
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
        set(window, {Position = UDim2.new(position.X.Scale, position.X.Offset + delta.X,
            position.Y.Scale, position.Y.Offset + delta.Y)})
    end)
    on(input, "InputEnded", function(event)
        if event == dragInput then dragging, dragInput = false, nil end
    end)
    local elapsed = 0
    on(run, "Heartbeat", function(dt)
        elapsed = elapsed + dt
        if elapsed < 0.1 then return end
        elapsed = 0
        set(titleLabel, {Text = "REMOTE SPY · " .. total .. (dropped > 0 and (" · fila −" .. dropped) or "")})
        set(pauseButton, {Text = spy.enabled and "Pausar" or "Retomar"})
        for bucket in pairs(dirty) do
            local entry = bucket.group
            if entry and not entry.dead then
                set(entry.countLabel, {Text = string.format("+%.3fs · ×%d%s", entry.at,
                    bucket.total, entry.blocked and " · BLOCK" or "")})
            end
            dirty[bucket] = nil
        end
        local now = os.clock()
        for key, bucket in pairs(rates) do
            if now - bucket.last > C.window then rates[key] = nil end
        end
        if selected then refreshActions() end
    end)
end

-- SPOOF
openSpoof = function(entry)
    if busy then setStatus("Uma chamada ainda aguarda retorno") return end
    local ok, source = pcall(literalArguments, entry.args)
    editing = entry
    set(codeBox, {Text = ok and source or ""})
    set(modal, {Visible = true})
    setStatus(ok and "Edite expressões Luau; nils finais são preservados"
        or ("Não foi gerado literal: " .. tostring(source) .. ". Digite os argumentos manualmente."))
end
local function bindSpoof()
    on(callButton, "Activated", function()
        if busy or not editing or editing.dead then return end
        local entry, source = editing, get(codeBox, "Text") or ""
        if type(loadstring) ~= "function" then setStatus("loadstring indisponível") return end
        if #source > C.literalBytes then setStatus("Editor limitado a 1 MB") return end
        local ok, chunk, compileError = pcall(loadstring, "return " .. source, "RemoteSpyArguments")
        if not ok or not chunk then setStatus("Sintaxe: " .. tostring(compileError or chunk)) return end
        busy = true
        set(callButton, {Text = "Aguardando…"})
        task.spawn(function()
            local thread = coroutine.running()
            -- A marca é global pela API, mas pertence à thread para não ocultar outras chamadas.
            spy.spoofing[thread] = true
            local returned = table.pack(pcall(function()
                local target = resolve(entry.info)
                assert(target == entry.remote, "O path agora aponta para outra Instance")
                assert(classes[get(target, "ClassName")] == entry.method, "Classe/método incompatível")
                local args = table.pack(chunk())
                if not alive then error("Spy descarregado", 0) end
                -- Dot call evita depender do estado interno de getnamecallmethod fora do hook.
                local method = get(target, entry.method)
                assert(type(method) == "function", "Método indisponível")
                return method(target, table.unpack(args, 1, args.n))
            end))
            spy.spoofing[thread] = nil
            busy = false
            if not alive then return end
            set(callButton, {Text = "Executar chamada"})
            if returned[1] then
                local result = {n = returned.n - 1}
                for i = 2, returned.n do result[i - 1] = returned[i] end
                local plain = displayArguments(result)
                setStatus("Executado; retorno: " .. short(plain:gsub("\n", " | "), 240))
            else setStatus("Falha: " .. tostring(returned[2])) end
        end)
    end)
end

-- UNLOAD
unload = function()
    if restored then return true end
    alive, spy.enabled = false, false
    local ok, err = true, nil
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
    disconnect(connections)
    for _, entry in ipairs(entries) do removeEntry(entry) end
    destroy(gui)
    entries, rates, dirty, queue, pathCache = {}, {}, {}, {}, setmetatable({}, {__mode = "k"})
    selected, editing, gui = nil, nil, nil
    window, list, detail, modal, argsLabel, metaLabel, codeBox = nil, nil, nil, nil, nil, nil, nil
    titleLabel, statusLabel, pauseButton, blockButton, ignoreButton, callButton = nil, nil, nil, nil, nil, nil
    if not ok then return false, "Não foi possível restaurar __namecall: " .. tostring(err) end
    restored, installed = true, false
    if rawget(env, "RemoteSpy") == spy then env.RemoteSpy = nil end
    return true
end
spy.unload = unload
local ok, err = pcall(function()
    buildUI()
    bindSpoof()
    installHook()
end)
if not ok then
    local cleaned, cleanupError = unload()
    error("RemoteSpy: " .. tostring(err) .. (cleaned and "" or ("; " .. tostring(cleanupError))), 0)
end
env.RemoteSpy = spy
setStatus("Pronto · Pause suspende logs; Block continua ativo; Spoof ignora Block")
return spy
