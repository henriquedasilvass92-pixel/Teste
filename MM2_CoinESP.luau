-- MM2 Coin ESP | Execute no cliente. No Studio: LocalScript em StarterPlayerScripts.
-- RightShift: abrir/fechar menu | End: remover | Botao COIN: menu no celular.
-- Baseado no ESP enviado: somente moedas, sem dependencias de Drawing.
-- CoinCollected.OnClientEvent e uma notificacao; nao informa a posicao das moedas.
-- Detecta somente objetos presentes no Workspace deste cliente.

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local UIS = game:GetService("UserInputService")
local CollectionService = game:GetService("CollectionService")
local LP = Players.LocalPlayer
assert(LP, "MM2 Coin ESP precisa ser executado no cliente.")
local playerGui = LP:WaitForChild("PlayerGui")

local GUI_NAME = "MM2CoinESP"
local MARKER_NAME = "MM2CoinESP_Marker"
local old = playerGui:FindFirstChild(GUI_NAME)
if old then old:Destroy() end -- Destroying tambem encerra a execucao anterior.
for _, child in ipairs(playerGui:GetChildren()) do
    if child.Name == MARKER_NAME then child:Destroy() end
end

local CFG = {
    CoinESP = true,
    CoinBox = true,
    CoinText = true,
    CoinTracer = false,
    MaxDist = 600,
    UpdateInterval = 0.15,
    RescanInterval = 8,
}

-- Nomes possiveis, nao caminhos confirmados pelas capturas.
-- Para outro nome, adicione sua versao minuscula sem espacos, _ ou -.
local COIN_NAMES = {
    coin = true, coinmodel = true, coinserver = true,
    coinclient = true, coinvisual = true, coinpickup = true,
}
local CONTAINER_NAMES = {
    coincontainer = true, coins = true, coinfolder = true,
}
local GOLD = Color3.fromRGB(255, 205, 60)
local NEAR = Color3.fromRGB(255, 250, 170)
local WHITE = Color3.fromRGB(235, 235, 245)
local MUTED = Color3.fromRGB(155, 158, 177)
local connections, pool = {}, {}
local running, rescanRequested = true, false

local function connect(signal, callback)
    local connection = signal:Connect(callback)
    table.insert(connections, connection)
    return connection
end

local function create(className, props, parent)
    local object = Instance.new(className)
    for key, value in pairs(props) do object[key] = value end
    object.Parent = parent
    return object
end

local function corner(object, radius)
    create("UICorner", { CornerRadius = UDim.new(0, radius) }, object)
end

local gui = create("ScreenGui", {
    Name = GUI_NAME, ResetOnSpawn = false, IgnoreGuiInset = true,
    DisplayOrder = 999, ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
}, playerGui)

local overlay = create("Frame", {
    Name = "Tracers", Size = UDim2.fromScale(1, 1),
    BackgroundTransparency = 1, BorderSizePixel = 0, ZIndex = 1,
}, gui)
local openButton = create("TextButton", {
    Name = "MenuButton", Size = UDim2.fromOffset(76, 34),
    Position = UDim2.fromOffset(14, 92), BackgroundColor3 = Color3.fromRGB(29, 27, 24),
    BorderSizePixel = 0, Text = "COIN", TextColor3 = GOLD,
    TextSize = 13, Font = Enum.Font.GothamBold, ZIndex = 10,
}, gui)
corner(openButton, 9)

local panel = create("Frame", {
    Name = "Panel", Size = UDim2.fromOffset(244, 326),
    Position = UDim2.fromOffset(14, 134), BackgroundColor3 = Color3.fromRGB(18, 18, 24),
    BorderSizePixel = 0, Active = true, ZIndex = 10,
}, gui)
corner(panel, 10)
create("UIStroke", { Color = Color3.fromRGB(85, 74, 43), Thickness = 1 }, panel)

local title = create("TextLabel", {
    Name = "DragHandle", Size = UDim2.new(1, -48, 0, 38),
    Position = UDim2.fromOffset(12, 0), BackgroundTransparency = 1,
    Text = "MM2  |  COIN ESP", TextColor3 = GOLD,
    Font = Enum.Font.GothamBold, TextSize = 14,
    TextXAlignment = Enum.TextXAlignment.Left, Active = true, ZIndex = 11,
}, panel)
local closeButton = create("TextButton", {
    Size = UDim2.fromOffset(34, 34), Position = UDim2.new(1, -38, 0, 2),
    BackgroundTransparency = 1, Text = "-", TextSize = 24,
    TextColor3 = MUTED, Font = Enum.Font.GothamBold, ZIndex = 11,
}, panel)

local status = create("TextLabel", {
    Name = "Status", Size = UDim2.new(1, -24, 0, 40),
    Position = UDim2.fromOffset(12, 38), BackgroundTransparency = 1,
    Text = "Procurando moedas...", TextColor3 = MUTED,
    Font = Enum.Font.Gotham, TextSize = 11, TextWrapped = true,
    TextXAlignment = Enum.TextXAlignment.Left, ZIndex = 11,
}, panel)

local function button(text, y, callback)
    local b = create("TextButton", {
        Size = UDim2.new(1, -24, 0, 30), Position = UDim2.fromOffset(12, y),
        BackgroundColor3 = Color3.fromRGB(32, 32, 41), BorderSizePixel = 0,
        Text = text, TextColor3 = WHITE, TextSize = 12,
        Font = Enum.Font.Gotham, ZIndex = 11,
    }, panel)
    corner(b, 6)
    connect(b.Activated, callback) -- Mouse, toque e controle.
    return b
end

local function toggle(text, key, y)
    local b
    local function render()
        b.Text = text .. (CFG[key] and "   ON" or "   OFF")
        b.TextColor3 = CFG[key] and GOLD or MUTED
    end
    b = button("", y, function()
        CFG[key] = not CFG[key]
        render()
    end)
    render()
end
toggle("Coin ESP", "CoinESP", 82)
toggle("Caixa nas moedas", "CoinBox", 116)
toggle("Nome e distancia", "CoinText", 150)
toggle("Linha ate as moedas", "CoinTracer", 184)

create("TextLabel", {
    Size = UDim2.fromOffset(140, 28), Position = UDim2.fromOffset(12, 220),
    BackgroundTransparency = 1, Text = "Distancia maxima", TextColor3 = WHITE,
    TextSize = 12, Font = Enum.Font.Gotham,
    TextXAlignment = Enum.TextXAlignment.Left, ZIndex = 11,
}, panel)
local distanceBox = create("TextBox", {
    Name = "MaxDistance", Size = UDim2.fromOffset(66, 26),
    Position = UDim2.new(1, -78, 0, 220), BackgroundColor3 = Color3.fromRGB(32, 32, 41),
    BorderSizePixel = 0, Text = tostring(CFG.MaxDist), TextColor3 = GOLD,
    TextSize = 12, Font = Enum.Font.GothamBold, ClearTextOnFocus = false, ZIndex = 11,
}, panel)
corner(distanceBox, 5)
connect(distanceBox.FocusLost, function()
    local number = tonumber(distanceBox.Text)
    if number and number == number then CFG.MaxDist = math.clamp(number, 25, 5000) end
    distanceBox.Text = tostring(CFG.MaxDist)
end)
button("Atualizar busca", 254, function() rescanRequested = true end)
local unloadButton = button("REMOVER ESP", 288, function() gui:Destroy() end)
unloadButton.BackgroundColor3 = Color3.fromRGB(96, 37, 43)

local function normalized(name)
    return (name:lower():gsub("[%s_%-]", ""))
end

local function isPhysical(object)
    return object:IsA("BasePart") or object:IsA("Model") or object:IsA("Folder")
end

local function coinRoot(object)
    if not isPhysical(object) or not object:IsDescendantOf(workspace) then return nil end
    local current, root = object, nil
    while current and current ~= workspace do
        -- Nao marcar ferramentas, acessorios ou objetos dentro de personagens.
        if current:IsA("Tool") or current:IsA("Accessory")
            or (current:IsA("Model") and current:FindFirstChildOfClass("Humanoid")) then
            return nil
        end
        if isPhysical(current) then
            local name = normalized(current.Name)
            if not CONTAINER_NAMES[name] then
                local parent = current.Parent
                local named = COIN_NAMES[name] or name:match("^coin%d+$")
                local inContainer = parent and CONTAINER_NAMES[normalized(parent.Name)]
                if named or inContainer or CollectionService:HasTag(current, "Coin") then
                    root = current -- A raiz externa vence: sem duplicar Model + MeshPart.
                end
            end
        end
        current = current.Parent
    end
    return root
end

local function usablePart(part)
    return part and part:IsA("BasePart") and part:IsDescendantOf(workspace)
        and (1 - (1 - part.Transparency) * (1 - part.LocalTransparencyModifier)) < 0.98
end

local function getPart(root, cached)
    if root:IsA("BasePart") and usablePart(root) then return root end
    if usablePart(cached) and cached:IsDescendantOf(root) then return cached end
    if root:IsA("Model") and usablePart(root.PrimaryPart) then return root.PrimaryPart end
    for _, descendant in ipairs(root:GetDescendants()) do
        if usablePart(descendant) then return descendant end
    end
    return nil
end

local function removeCoin(root)
    local data = pool[root]
    if not data then return end
    if data.marker then data.marker:Destroy() end
    if data.line then data.line:Destroy() end
    pool[root] = nil
end

local function track(root)
    if root and not pool[root] then pool[root] = {} end
end

local function scan()
    local found = {}
    for _, object in ipairs(workspace:GetDescendants()) do
        local root = coinRoot(object)
        if root then found[root] = true end
    end
    for root in pairs(found) do track(root) end
    for root in pairs(pool) do
        if not found[root] then removeCoin(root) end
    end
end

local function makeMarker(data)
    data.marker = create("BillboardGui", {
        Name = MARKER_NAME, Size = UDim2.fromOffset(160, 44),
        AlwaysOnTop = true, LightInfluence = 0, Enabled = false,
    }, playerGui)
    data.box = create("Frame", {
        AnchorPoint = Vector2.new(0.5, 0.5), Position = UDim2.new(0.5, 0, 0.5, 5),
        Size = UDim2.fromOffset(16, 16), BackgroundTransparency = 1, BorderSizePixel = 0,
    }, data.marker)
    data.stroke = create("UIStroke", { Thickness = 1.5, Color = GOLD }, data.box)
    corner(data.box, 3)
    data.text = create("TextLabel", {
        Size = UDim2.new(1, 0, 0, 18), BackgroundTransparency = 1,
        Font = Enum.Font.GothamBold, TextSize = 11, TextColor3 = GOLD,
        TextStrokeTransparency = 0.2, TextStrokeColor3 = Color3.new(0, 0, 0),
    }, data.marker)
end

local nearest, detected, inRange = nil, 0, 0
local function refresh()
    local camera = workspace.CurrentCamera
    local character = LP.Character
    local hrp = character and character:FindFirstChild("HumanoidRootPart")
    local origin = (hrp and hrp.Position) or (camera and camera.CFrame.Position)
    nearest, detected, inRange = nil, 0, 0
    local bestDistance = math.huge

    for root, data in pairs(pool) do
        if coinRoot(root) ~= root then
            removeCoin(root)
        else
            data.part = getPart(root, data.part)
            data.visible = false
            if data.part then
                detected = detected + 1
                local distance = origin and (data.part.Position - origin).Magnitude or math.huge
                data.distance = distance
                if distance <= CFG.MaxDist then
                    inRange = inRange + 1
                    data.visible = CFG.CoinESP and camera ~= nil
                    if distance < bestDistance then
                        nearest, bestDistance = root, distance
                    end
                end
            end
        end
    end

    for root, data in pairs(pool) do
        if data.visible then
            if not data.marker then makeMarker(data) end
            local near = root == nearest
            local color = near and NEAR or GOLD
            data.marker.Adornee = data.part
            -- O limite e calculado a partir do jogador, nao da camera.
            data.marker.MaxDistance = 0
            data.marker.Enabled = CFG.CoinBox or CFG.CoinText
            data.box.Visible = CFG.CoinBox
            data.box.Size = UDim2.fromOffset(near and 22 or 16, near and 22 or 16)
            data.stroke.Color = color
            data.text.Visible = CFG.CoinText
            data.text.TextColor3 = color
            data.text.Text = (near and "[+] COIN  " or "COIN  ")
                .. tostring(math.floor(data.distance)) .. " studs"
        elseif data.marker then
            data.marker.Enabled = false
        end
        if data.line and (not data.visible or not CFG.CoinTracer) then
            data.line.Visible = false
        end
    end

    if not CFG.CoinESP then
        status.Text = "ESP desligado | Detectadas: " .. detected
    elseif detected == 0 then
        status.Text = "Nenhuma moeda detectada neste cliente.\nAguardando moedas do mapa..."
    else
        status.Text = "Detectadas: " .. detected .. " | No alcance: " .. inRange
            .. (nearest and ("\nMais proxima: " .. math.floor(bestDistance) .. " studs") or "")
    end
end

connect(workspace.DescendantAdded, function(object)
    if running then track(coinRoot(object)) end
end)
connect(workspace.DescendantRemoving, function(object)
    removeCoin(object)
end)
connect(CollectionService:GetInstanceAddedSignal("Coin"), function(object)
    if running then track(coinRoot(object)) end
end)
connect(CollectionService:GetInstanceRemovedSignal("Coin"), function()
    rescanRequested = true
end)

-- Somente as linhas precisam acompanhar a camera a cada frame.
connect(RunService.RenderStepped, function()
    local camera = workspace.CurrentCamera
    if not camera then
        for _, data in pairs(pool) do
            if data.line then data.line.Visible = false end
        end
        return
    end
    for root, data in pairs(pool) do
        if CFG.CoinESP and CFG.CoinTracer and data.visible and usablePart(data.part) then
            local point, onScreen = camera:WorldToViewportPoint(data.part.Position)
            if onScreen and point.Z > 0 then
                if not data.line then
                    data.line = create("Frame", {
                        AnchorPoint = Vector2.new(0.5, 0.5), BorderSizePixel = 0,
                        BackgroundTransparency = 0.25, ZIndex = 1,
                    }, overlay)
                end
                local start = Vector2.new(camera.ViewportSize.X / 2, camera.ViewportSize.Y - 5)
                local finish = Vector2.new(point.X, point.Y)
                local delta = finish - start
                data.line.Size = UDim2.fromOffset(delta.Magnitude, 1)
                data.line.Position = UDim2.fromOffset((start.X + finish.X) / 2, (start.Y + finish.Y) / 2)
                data.line.Rotation = math.deg(math.atan2(delta.Y, delta.X))
                data.line.BackgroundColor3 = root == nearest and NEAR or GOLD
                data.line.Visible = true
            elseif data.line then
                data.line.Visible = false
            end
        elseif data.line then
            data.line.Visible = false
        end
    end
end)

local elapsed, scanElapsed = 0, 0
connect(RunService.Heartbeat, function(dt)
    elapsed, scanElapsed = elapsed + dt, scanElapsed + dt
    if elapsed < CFG.UpdateInterval then return end
    elapsed = 0
    if rescanRequested or scanElapsed >= CFG.RescanInterval then
        rescanRequested, scanElapsed = false, 0
        scan() -- Recupera tambem objetos renomeados depois de serem criados.
    end
    refresh()
end)

connect(openButton.Activated, function() panel.Visible = not panel.Visible end)
connect(closeButton.Activated, function() panel.Visible = false end)
connect(UIS.InputBegan, function(input, processed)
    if processed or UIS:GetFocusedTextBox() then return end
    if input.KeyCode == Enum.KeyCode.RightShift then panel.Visible = not panel.Visible end
    if input.KeyCode == Enum.KeyCode.End then gui:Destroy() end
end)

local dragInput, dragStart, panelStart
connect(title.InputBegan, function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton1
        or input.UserInputType == Enum.UserInputType.Touch then
        dragInput, dragStart, panelStart = input, input.Position, panel.Position
    end
end)
connect(UIS.InputChanged, function(input)
    if not dragInput then return end
    local isMouse = dragInput.UserInputType == Enum.UserInputType.MouseButton1
        and input.UserInputType == Enum.UserInputType.MouseMovement
    if input == dragInput or isMouse then
        local delta = input.Position - dragStart
        local camera = workspace.CurrentCamera
        local viewport = camera and camera.ViewportSize or Vector2.new(800, 600)
        panel.Position = UDim2.fromOffset(
            math.clamp(panelStart.X.Offset + delta.X, 0, math.max(0, viewport.X - 60)),
            math.clamp(panelStart.Y.Offset + delta.Y, 0, math.max(0, viewport.Y - 38))
        )
    end
end)
connect(UIS.InputEnded, function(input)
    if input == dragInput or (dragInput
        and dragInput.UserInputType == Enum.UserInputType.MouseButton1
        and input.UserInputType == Enum.UserInputType.MouseButton1) then
        dragInput = nil
    end
end)

connect(gui.Destroying, function()
    if not running then return end
    running = false
    for _, connection in ipairs(connections) do connection:Disconnect() end
    for root in pairs(pool) do removeCoin(root) end
end)

scan()
refresh()
