--===============================================================
-- MM2 HUB | ESP + UTILIDADES | Menu original com todos os recursos juntos
-- RightShift: menu | End: remover | Celular: botao MM2 HUB
-- Execute um unico script no cliente. A interface nao baixa bibliotecas externas.
-- Encerre o script antigo pelo UNLOAD antes de usar esta versao.
-- Papeis inferidos pelas ferramentas replicadas; coleta depende do servidor.
--===============================================================

local Players = game:GetService("Players")
local RunService = game:GetService("RunService")
local Lighting = game:GetService("Lighting")
local UIS = game:GetService("UserInputService")
local CollectionService = game:GetService("CollectionService")
local LP = Players.LocalPlayer
assert(LP, "MM2 Hub deve ser executado no cliente.")
local playerGui = LP:WaitForChild("PlayerGui")
local GUI_NAME, MARKER_NAME = "MM2Hub", "MM2HubMarker"
for _, name in ipairs({GUI_NAME, "MM2HubRayfieldRuntime", "MM2CoinESP"}) do
    local old = playerGui:FindFirstChild(name)
    if old then old:Destroy() end
end
for _, child in ipairs(playerGui:GetChildren()) do
    if child.Name == MARKER_NAME or child.Name == "MM2HubRayfieldMarker" then child:Destroy() end
end

local CFG = {
    PlayerESP = true, Box = true, Tracer = false, IgnoreLocal = true, ItemESP = true,
    CoinESP = true, CoinBox = true, CoinText = true, CoinTracer = false,
    AutoFly = false, FlySpeed = 35, CoinOffset = Vector3.new(0, 2, 0),
    ArrivalRadius = 0.65, CollectionWait = 0.5, RetryDelay = 8,
    Fullbright = false, Noclip = false, Movement = true,
    WalkSpeed = 16, JumpPower = 50, MaxDist = 600,
    UpdateInterval = 0.15, RescanInterval = 8,
}
local C = {
    Murder = Color3.fromRGB(255, 60, 60), Sheriff = Color3.fromRGB(60, 150, 255),
    Innocent = Color3.fromRGB(70, 255, 130), Dead = Color3.fromRGB(160, 160, 160),
    Coin = Color3.fromRGB(255, 205, 60), CoinNear = Color3.fromRGB(255, 250, 170),
    Gun = Color3.fromRGB(90, 170, 255), Knife = Color3.fromRGB(255, 90, 90),
}
local GOLD, NEAR = C.Coin, C.CoinNear
local WHITE = Color3.fromRGB(235, 235, 245)
local COIN_NAMES = {
    coin = true, coinmodel = true, coinserver = true,
    coinclient = true, coinvisual = true, coinpickup = true,
}
local CONTAINER_NAMES = {coincontainer = true, coins = true, coinfolder = true}
local WEAPON_NAMES = {gun = true, knife = true, revolver = true, gundrop = true, knifedrop = true}
local connections, coinPool, itemPool, playerPool = {}, {}, {}, {}
local running, rescanRequested = true, false
local FlyToggle, CoinLabel, FlightLabel
local stopFlight, unload
local status, flightStatus = {Text = "Procurando moedas..."}, {Text = "Voo desligado"}
local ZERO = Vector3.new(0, 0, 0)

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
    create("UICorner", {CornerRadius = UDim.new(0, radius)}, object)
end
local gui = create("ScreenGui", {
    Name = GUI_NAME, ResetOnSpawn = false, IgnoreGuiInset = true,
    DisplayOrder = 999, ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
}, playerGui)
local overlay = create("Frame", {
    Name = "ESP", Size = UDim2.fromScale(1, 1),
    BackgroundTransparency = 1, BorderSizePixel = 0,
}, gui)
local function renderFly()
    if FlyToggle and FlyToggle.CurrentValue ~= CFG.AutoFly then FlyToggle:Set(CFG.AutoFly) end
end
local function fmtDist(distance)
    if distance >= 1000 then return string.format("%.1fk", distance / 1000) end
    return tostring(math.floor(distance))
end
local function originPosition(camera)
    local character = LP.Character
    local root = character and character:FindFirstChild("HumanoidRootPart")
    return root and root.Position or (camera and camera.CFrame.Position)
end
local function textObject(parent, size)
    return create("TextLabel", {
        BackgroundTransparency = 1, Font = Enum.Font.GothamBold, TextSize = size,
        TextColor3 = WHITE, TextStrokeTransparency = 0.2,
        TextStrokeColor3 = Color3.new(0, 0, 0), BorderSizePixel = 0,
    }, parent)
end
local function setLine(line, from, to, color)
    local delta = to - from
    line.Size = UDim2.fromOffset(delta.Magnitude, 1)
    line.Position = UDim2.fromOffset((from.X + to.X) / 2, (from.Y + to.Y) / 2)
    line.Rotation = math.deg(math.atan2(delta.Y, delta.X))
    line.BackgroundColor3, line.Visible = color, true
end
local function newLine(parent)
    return create("Frame", {
        AnchorPoint = Vector2.new(0.5, 0.5), BorderSizePixel = 0,
        BackgroundTransparency = 0.25, Visible = false,
    }, parent)
end

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
    local data = coinPool[root]
    if not data then return end
    if data.marker then data.marker:Destroy() end
    if data.line then data.line:Destroy() end
    coinPool[root] = nil
end

local function track(root)
    if root and not coinPool[root] then coinPool[root] = {} end
end

-- Colisoes compartilhadas pelo noclip manual e pelo voo.
local collisionState, movementState, lightingState
local function releaseNoclip()
    local previous = collisionState
    collisionState = nil
    if not previous then return end
    for _, connection in ipairs(previous.connections) do connection:Disconnect() end
    for part, original in pairs(previous.parts) do
        if part.Parent then part.CanCollide = original end
    end
end
local function applyNoclip(character, active)
    if collisionState and (not active or collisionState.character ~= character) then releaseNoclip() end
    if not active or not character then return end
    if not collisionState then
        local state = {character = character, parts = {}, connections = {}}
        collisionState = state
        local function remember(object)
            if object:IsA("BasePart") then
                if state.parts[object] == nil then state.parts[object] = object.CanCollide end
                object.CanCollide = false
            end
        end
        state.connections[1] = character.DescendantAdded:Connect(remember)
        state.connections[2] = character.DescendantRemoving:Connect(function(object)
            local original = state.parts[object]
            if original ~= nil then object.CanCollide = original; state.parts[object] = nil end
        end)
        for _, object in ipairs(character:GetDescendants()) do remember(object) end
    end
    for part in pairs(collisionState.parts) do
        if part:IsDescendantOf(character) then part.CanCollide = false end
    end
end
local function restoreMovement()
    local previous = movementState
    movementState = nil
    if previous and previous.humanoid.Parent then
        previous.humanoid.WalkSpeed = previous.WalkSpeed
        previous.humanoid.JumpPower = previous.JumpPower
        previous.humanoid.UseJumpPower = previous.UseJumpPower
    end
end
local function applyMovement()
    local character = LP.Character
    local hum = character and character:FindFirstChildOfClass("Humanoid")
    if movementState and (not CFG.Movement or hum ~= movementState.humanoid) then restoreMovement() end
    if not CFG.Movement or not hum or hum.Health <= 0 then return end
    if not movementState then
        movementState = {humanoid = hum, WalkSpeed = hum.WalkSpeed,
            JumpPower = hum.JumpPower, UseJumpPower = hum.UseJumpPower}
    end
    hum.WalkSpeed, hum.JumpPower, hum.UseJumpPower = CFG.WalkSpeed, CFG.JumpPower, true
end
local FULLBRIGHT = {
    Brightness = 3, ClockTime = 12, Ambient = Color3.fromRGB(180, 180, 180),
    OutdoorAmbient = Color3.fromRGB(180, 180, 180), FogEnd = 1e6, GlobalShadows = false,
}
local function applyFullbright(on)
    if on then
        if not lightingState then
            lightingState = {}
            for key in pairs(FULLBRIGHT) do lightingState[key] = Lighting[key] end
        end
        for key, value in pairs(FULLBRIGHT) do Lighting[key] = value end
    elseif lightingState then
        for key, value in pairs(lightingState) do Lighting[key] = value end
        lightingState = nil
    end
end

local function weaponRoot(object)
    if not (isPhysical(object) or object:IsA("Tool")) or not object:IsDescendantOf(workspace) then return nil end
    local current, root = object, nil
    while current and current ~= workspace do
        if current:IsA("Accessory") or (current:IsA("Model") and current:FindFirstChildOfClass("Humanoid")) then
            return nil
        end
        if (isPhysical(current) or current:IsA("Tool")) and WEAPON_NAMES[normalized(current.Name)] then root = current end
        current = current.Parent
    end
    return root
end
local function clearItem(root)
    local data = itemPool[root]
    if data and data.marker then data.marker:Destroy() end
    itemPool[root] = nil
end
local function discover(object)
    track(coinRoot(object))
    local weapon = weaponRoot(object)
    if weapon and not itemPool[weapon] then itemPool[weapon] = {} end
end
local function scan()
    local coins, weapons = {}, {}
    for _, object in ipairs(workspace:GetDescendants()) do
        local coin, weapon = coinRoot(object), weaponRoot(object)
        if coin then coins[coin] = true end
        if weapon then weapons[weapon] = true end
    end
    for coin in pairs(coins) do track(coin) end
    for weapon in pairs(weapons) do if not itemPool[weapon] then itemPool[weapon] = {} end end
    for coin in pairs(coinPool) do if not coins[coin] then removeCoin(coin) end end
    for weapon in pairs(itemPool) do if not weapons[weapon] then clearItem(weapon) end end
end

-- VOO EM PE: velocidade fisica constante, sem ancorar ou saltar para o alvo.
-- Os constraints mantem a flutuacao e a orientacao vertical. CanTouch e preservado.
local flight, flightClock = nil, 0
local cooldowns = setmetatable({}, { __mode = "k" })

stopFlight = function()
    local previous = flight
    flight = nil
    if previous then
        for _, connection in ipairs(previous.connections) do connection:Disconnect() end
        for _, object in ipairs(previous.objects) do object:Destroy() end
        if previous.root.Parent then
            previous.root.AssemblyLinearVelocity = ZERO
            previous.root.AssemblyAngularVelocity = ZERO
        end
        if previous.idle then
            previous.idle:Stop(0.1)
            previous.idle:Destroy()
        end
        if previous.animate and previous.animate.Parent then
            previous.animate.Disabled = previous.animateDisabled
        end
        local hum = previous.humanoid
        if hum.Parent then
            hum.AutoRotate = previous.autoRotate
            hum.PlatformStand = previous.platformStand
            if hum.Health > 0 then
                local state = previous.state
                if state == Enum.HumanoidStateType.Physics then
                    state = Enum.HumanoidStateType.GettingUp
                end
                hum:ChangeState(state)
                -- Animate reinicia suas proprias trilhas ao ser reativado.
                if not previous.animate or previous.animateDisabled then
                    for _, saved in ipairs(previous.tracks) do
                        pcall(function()
                            saved.track:Play(0.15, saved.weight, saved.speed)
                            saved.track.TimePosition = saved.position
                        end)
                    end
                end
            end
        end
    end
    applyNoclip(LP.Character, running and CFG.Noclip)
    flightStatus.Text = "Voo desligado"
end

local function pauseFlight()
    CFG.AutoFly = false
    renderFly()
    stopFlight()
end

local function startFlight(character, humanoid, root)
    local session = {
        character = character, humanoid = humanoid, root = root,
        autoRotate = humanoid.AutoRotate, platformStand = humanoid.PlatformStand,
        state = humanoid:GetState(), objects = {}, connections = {}, tracks = {},
    }
    flight = session -- Permite limpar inclusive uma inicializacao interrompida.
    session.connections[1] = humanoid.Died:Connect(pauseFlight)
    applyNoclip(character, true)

    local animate = character:FindFirstChild("Animate")
    if animate and animate:IsA("LocalScript") then
        session.animate, session.animateDisabled = animate, animate.Disabled
        animate.Disabled = true
    end
    local animator = humanoid:FindFirstChildOfClass("Animator")
    if animator then
        for _, track in ipairs(animator:GetPlayingAnimationTracks()) do
            table.insert(session.tracks, {
                track = track, position = track.TimePosition, speed = track.Speed,
                weight = track.WeightCurrent,
            })
            track:Stop(0.15)
        end
        -- Usa a animacao idle do proprio avatar; sem animacao de corrida/queda.
        local idleFolder = session.animate and session.animate:FindFirstChild("idle")
        local idleAnimation = idleFolder and idleFolder:FindFirstChildWhichIsA("Animation", true)
        if idleAnimation then
            local ok, idle = pcall(function() return animator:LoadAnimation(idleAnimation) end)
            if ok then
                session.idle = idle
                idle.Looped = true
                idle.Priority = Enum.AnimationPriority.Idle
                idle:Play(0.15)
            end
        end
    end

    local attachment = create("Attachment", { Name = "CoinFlightAttachment" }, root)
    table.insert(session.objects, attachment)
    session.velocity = create("LinearVelocity", {
        Name = "CoinFlightVelocity", Attachment0 = attachment,
        RelativeTo = Enum.ActuatorRelativeTo.World,
        VelocityConstraintMode = Enum.VelocityConstraintMode.Vector,
        ForceLimitsEnabled = false, VectorVelocity = ZERO,
    }, root)
    table.insert(session.objects, session.velocity)
    local facing = root.CFrame.LookVector
    local flat = Vector3.new(facing.X, 0, facing.Z)
    session.facing = flat.Magnitude > 0.01 and flat.Unit or Vector3.new(0, 0, -1)
    session.upright = create("AlignOrientation", {
        Name = "CoinFlightUpright", Attachment0 = attachment,
        Mode = Enum.OrientationAlignmentMode.OneAttachment, RigidityEnabled = true,
        CFrame = CFrame.lookAt(ZERO, session.facing),
    }, root)
    table.insert(session.objects, session.upright)
    humanoid.AutoRotate = false
    humanoid.PlatformStand = false
    humanoid:ChangeState(Enum.HumanoidStateType.Physics)
    root.AssemblyLinearVelocity = ZERO
    root.AssemblyAngularVelocity = ZERO
    return session
end

local function selectTarget(position)
    local best, bestDistance = nil, CFG.MaxDist
    for root, data in pairs(coinPool) do
        if (cooldowns[root] or 0) <= flightClock and coinRoot(root) == root then
            data.part = getPart(root, data.part)
            if data.part then
                local distance = (data.part.Position - position).Magnitude
                if distance <= bestDistance then best, bestDistance = root, distance end
            end
        end
    end
    return best, bestDistance
end

local function flightStep(dt)
    flightClock = flightClock + math.max(dt, 0)
    if not CFG.AutoFly then return end
    local character = LP.Character
    local humanoid = character and character:FindFirstChildOfClass("Humanoid")
    local root = character and character:FindFirstChild("HumanoidRootPart")
    if not humanoid or humanoid.Health <= 0 or not root or not root:IsA("BasePart") then
        if flight then pauseFlight() end
        flightStatus.Text = "Aguardando personagem vivo"
        return
    end
    if flight and (flight.character ~= character or flight.root ~= root) then
        pauseFlight()
        return
    end
    if root.Anchored or humanoid.Sit then
        if flight then pauseFlight() end
        flightStatus.Text = "Aguardando personagem livre e fora do assento"
        return
    end

    if not flight then
        local first = selectTarget(root.Position)
        if not first then
            flightStatus.Text = "Aguardando moeda no alcance"
            return
        end
        startFlight(character, humanoid, root)
    end
    local session = flight
    humanoid.AutoRotate = false
    humanoid.PlatformStand = false
    humanoid:Move(ZERO, false)
    humanoid:ChangeState(Enum.HumanoidStateType.Physics)
    session.velocity.VectorVelocity = ZERO
    root.AssemblyAngularVelocity = ZERO

    local data = session.target and coinPool[session.target]
    local part = data and getPart(session.target, data.part)
    if not part or coinRoot(session.target) ~= session.target
        or (part.Position - root.Position).Magnitude > CFG.MaxDist then
        session.target, session.arrivedAt = nil, nil
    end
    if not session.target then
        local target, distance = selectTarget(root.Position)
        session.target, session.arrivedAt = target, nil
        if not target then
            flightStatus.Text = "Flutuando; aguardando outras moedas"
            return
        end
        session.deadline = flightClock + math.max(10, distance / CFG.FlySpeed * 3 + 5)
        data = coinPool[target]
        part = data and getPart(target, data.part)
    end
    if not part then return end

    local delta = part.Position + CFG.CoinOffset - root.Position
    local distance = delta.Magnitude
    if distance > 0.02 then
        local speed = math.min(CFG.FlySpeed, distance / math.max(dt, 1 / 240))
        session.velocity.VectorVelocity = delta.Unit * speed
        local flat = Vector3.new(delta.X, 0, delta.Z)
        if flat.Magnitude > 0.05 then session.facing = flat.Unit end
    end
    session.upright.CFrame = CFrame.lookAt(ZERO, session.facing)

    if distance <= CFG.ArrivalRadius then
        session.arrivedAt = session.arrivedAt or flightClock
        flightStatus.Text = "Sobre a moeda; aguardando coleta"
        if flightClock - session.arrivedAt >= CFG.CollectionWait then
            -- Nao apaga a moeda e nao simula confirmacao do servidor.
            cooldowns[session.target] = flightClock + CFG.RetryDelay
            session.target, session.arrivedAt = nil, nil
        end
    elseif flightClock >= session.deadline then
        cooldowns[session.target] = flightClock + CFG.RetryDelay
        session.target, session.arrivedAt = nil, nil
        flightStatus.Text = "Alvo sem progresso; buscando outra moeda"
    else
        session.arrivedAt = nil
        flightStatus.Text = "Voando em pe | " .. math.floor(distance) .. " studs ate a moeda"
    end
end

local function makeMarker(data)
    data.marker = create("BillboardGui", {
        Name = MARKER_NAME, Size = UDim2.fromOffset(160, 44),
        AlwaysOnTop = true, LightInfluence = 0, Enabled = false, ResetOnSpawn = false,
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

    for root, data in pairs(coinPool) do
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

    for root, data in pairs(coinPool) do
        if data.visible then
            if not data.marker or data.marker.Parent ~= playerGui then makeMarker(data) end
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

-- ESP DE JOGADORES: Frames/TextLabels nativos; nao precisa de Drawing.
local function getRole(player)
    local character = player.Character
    local hum = character and character:FindFirstChildOfClass("Humanoid")
    if not hum or hum.Health <= 0 then return "MORTO", C.Dead end
    local hasKnife, hasGun = false, false
    for _, container in ipairs({character, player:FindFirstChild("Backpack")}) do
        if container then
            for _, object in ipairs(container:GetChildren()) do
                if object:IsA("Tool") then
                    hasKnife = hasKnife or object.Name == "Knife"
                    hasGun = hasGun or object.Name == "Gun" or object.Name == "Revolver"
                end
            end
        end
    end
    if hasKnife then return "MURDERER", C.Murder end
    if hasGun then return "SHERIFF", C.Sheriff end
    return "INOCENTE", C.Innocent
end
local function removePlayer(player)
    local data = playerPool[player]
    if data then data.group:Destroy() end
    playerPool[player] = nil
end
local function makePlayer(player)
    local data = {}
    data.group = create("Frame", {Name = "Player_" .. player.Name, Size = UDim2.fromScale(1, 1),
        BackgroundTransparency = 1, Visible = false}, overlay)
    data.boxOut = create("Frame", {BackgroundTransparency = 1, BorderSizePixel = 0}, data.group)
    create("UIStroke", {Color = Color3.new(0, 0, 0), Thickness = 3, Transparency = 0.3}, data.boxOut)
    data.box = create("Frame", {BackgroundTransparency = 1, BorderSizePixel = 0}, data.group)
    data.stroke = create("UIStroke", {Thickness = 1}, data.box)
    data.name, data.role, data.dist = textObject(data.group, 13), textObject(data.group, 12), textObject(data.group, 11)
    data.hpBg = create("Frame", {BackgroundColor3 = Color3.fromRGB(30, 30, 30), BorderSizePixel = 0}, data.group)
    data.hpFg = create("Frame", {BorderSizePixel = 0}, data.group)
    data.line = newLine(data.group)
    playerPool[player] = data
    return data
end
local function updatePlayer(player, camera, origin)
    local existing = playerPool[player]
    if existing then existing.group.Visible = false end
    if not CFG.PlayerESP or (player == LP and CFG.IgnoreLocal) or not camera or not origin then return end
    local character = player.Character
    local root = character and character:FindFirstChild("HumanoidRootPart")
    local hum = character and character:FindFirstChildOfClass("Humanoid")
    if not root or not hum or hum.Health <= 0 then return end
    local distance = (root.Position - origin).Magnitude
    if distance > CFG.MaxDist then return end
    local head = character:FindFirstChild("Head")
    local top, topOn = camera:WorldToViewportPoint((head and head.Position or root.Position) + Vector3.new(0, 0.6, 0))
    local bottom, bottomOn = camera:WorldToViewportPoint(root.Position - Vector3.new(0, 2.9, 0))
    if not topOn or not bottomOn or top.Z <= 0 or bottom.Z <= 0 then return end
    local data = existing or makePlayer(player)
    local role, color = getRole(player)
    local height = math.max(math.abs(bottom.Y - top.Y), 14)
    local width = height * 0.52
    local x, y = top.X - width / 2, math.min(top.Y, bottom.Y)
    data.group.Visible = true
    data.boxOut.Visible, data.box.Visible = CFG.Box, CFG.Box
    data.hpBg.Visible, data.hpFg.Visible = CFG.Box, CFG.Box
    data.boxOut.Position, data.box.Position = UDim2.fromOffset(x, y), UDim2.fromOffset(x, y)
    data.boxOut.Size, data.box.Size = UDim2.fromOffset(width, height), UDim2.fromOffset(width, height)
    data.stroke.Color = color
    local hp = math.clamp(hum.Health / math.max(hum.MaxHealth, 1), 0, 1)
    data.hpBg.Position, data.hpBg.Size = UDim2.fromOffset(x - 6, y), UDim2.fromOffset(3, height)
    data.hpFg.Position, data.hpFg.Size = UDim2.fromOffset(x - 6, y + height * (1 - hp)), UDim2.fromOffset(3, height * hp)
    data.hpFg.BackgroundColor3 = Color3.fromRGB(240, 60, 60):Lerp(C.Innocent, hp)
    for _, entry in ipairs({{data.name, player.Name, y - 32}, {data.role, role, y - 17},
        {data.dist, fmtDist(distance) .. " studs", y + height + 2}}) do
        local label = entry[1]
        label.Text, label.TextColor3 = entry[2], color
        label.Size = UDim2.fromOffset(200, 16)
        label.Position = UDim2.fromOffset(top.X - 100, entry[3])
    end
    data.dist.TextColor3 = WHITE
    data.line.Visible = CFG.Tracer
    if CFG.Tracer then
        setLine(data.line, Vector2.new(camera.ViewportSize.X / 2, camera.ViewportSize.Y - 5),
            Vector2.new(bottom.X, bottom.Y), color)
    end
end
local function refreshItems(camera)
    local origin = originPosition(camera)
    for root, data in pairs(itemPool) do
        if weaponRoot(root) ~= root then
            clearItem(root)
        else
            data.part = getPart(root, data.part)
            local distance = origin and data.part and (data.part.Position - origin).Magnitude or math.huge
            if CFG.ItemESP and camera and data.part and distance <= CFG.MaxDist then
                if not data.marker or data.marker.Parent ~= playerGui then
                    data.marker = create("BillboardGui", {
                        Name = MARKER_NAME, Size = UDim2.fromOffset(180, 24),
                        AlwaysOnTop = true, LightInfluence = 0, ResetOnSpawn = false,
                    }, playerGui)
                    data.text = textObject(data.marker, 12)
                    data.text.Size = UDim2.fromScale(1, 1)
                end
                data.marker.Enabled, data.marker.Adornee = true, data.part
                data.text.TextColor3 = normalized(root.Name):find("knife", 1, true) and C.Knife or C.Gun
                data.text.Text = string.upper(root.Name) .. " [" .. fmtDist(distance) .. "]"
            elseif data.marker then data.marker.Enabled = false end
        end
    end
end
local function render()
    local camera = workspace.CurrentCamera
    local origin = originPosition(camera)
    for _, player in ipairs(Players:GetPlayers()) do updatePlayer(player, camera, origin) end
    for root, data in pairs(coinPool) do
        if CFG.CoinESP and CFG.CoinTracer and camera and data.visible and usablePart(data.part) then
            local point, onScreen = camera:WorldToViewportPoint(data.part.Position)
            if onScreen and point.Z > 0 then
                if not data.line then data.line = newLine(overlay) end
                setLine(data.line, Vector2.new(camera.ViewportSize.X / 2, camera.ViewportSize.Y - 5),
                    Vector2.new(point.X, point.Y), root == nearest and NEAR or GOLD)
            elseif data.line then data.line.Visible = false end
        elseif data.line then data.line.Visible = false end
    end
end

-- MENU ORIGINAL: lista vertical, secoes, indicadores verdes e campos numericos.
unload = function()
    if not running then return end
    running = false
    CFG.AutoFly = false
    for _, connection in ipairs(connections) do connection:Disconnect() end
    stopFlight()
    releaseNoclip()
    restoreMovement()
    applyFullbright(false)
    for player in pairs(playerPool) do removePlayer(player) end
    for coin in pairs(coinPool) do removeCoin(coin) end
    for item in pairs(itemPool) do clearItem(item) end
    if gui.Parent then gui:Destroy() end
end
connect(gui.Destroying, unload)

local main, title
local function setupInterface()
    local camera = workspace.CurrentCamera
    local viewport = camera and camera.ViewportSize or Vector2.new(800, 600)
    local height = math.clamp(viewport.Y - 150, 220, 400)
    main = create("Frame", {
        Name = "Main", Size = UDim2.fromOffset(244, height),
        Position = UDim2.fromOffset(20, math.min(120, math.max(12, viewport.Y - height - 12))),
        BackgroundColor3 = Color3.fromRGB(18, 18, 22), BackgroundTransparency = 0.05,
        BorderSizePixel = 0, Active = true, ZIndex = 20,
    }, gui)
    corner(main, 8)
    create("UIStroke", {Color = Color3.fromRGB(90, 90, 110), Thickness = 1}, main)
    title = create("TextLabel", {
        Name = "DragHandle", Size = UDim2.new(1, 0, 0, 32),
        BackgroundColor3 = Color3.fromRGB(30, 30, 38), BackgroundTransparency = 0.2,
        BorderSizePixel = 0, Text = "MM2 HUB  |  ESP", TextColor3 = WHITE,
        Font = Enum.Font.GothamBold, TextSize = 13, Active = true, ZIndex = 21,
    }, main)
    corner(title, 8)
    local minimize = create("TextButton", {
        Name = "Minimize", Size = UDim2.fromOffset(28, 28), Position = UDim2.new(1, -30, 0, 2),
        BackgroundTransparency = 1, Text = "-", TextColor3 = WHITE,
        Font = Enum.Font.GothamBold, TextSize = 20, ZIndex = 22,
    }, main)
    connect(minimize.Activated, function() main.Visible = false end)
    local openButton = create("TextButton", {
        Name = "MenuButton", Size = UDim2.fromOffset(88, 32),
        Position = UDim2.fromOffset(20, 76), BackgroundColor3 = Color3.fromRGB(30, 30, 38),
        BorderSizePixel = 0, Text = "MM2 HUB", TextColor3 = WHITE,
        Font = Enum.Font.GothamBold, TextSize = 12, ZIndex = 30,
    }, gui)
    corner(openButton, 7)
    connect(openButton.Activated, function() main.Visible = not main.Visible end)

    local scroll = create("ScrollingFrame", {
        Name = "Controls", Size = UDim2.new(1, -12, 1, -40), Position = UDim2.fromOffset(6, 36),
        BackgroundTransparency = 1, BorderSizePixel = 0, ScrollBarThickness = 3,
        ScrollBarImageColor3 = Color3.fromRGB(140, 140, 170),
        CanvasSize = UDim2.fromOffset(0, 0), AutomaticCanvasSize = Enum.AutomaticSize.Y,
        ZIndex = 21,
    }, main)
    create("UIListLayout", {Padding = UDim.new(0, 4), SortOrder = Enum.SortOrder.LayoutOrder}, scroll)
    local order = 0
    local function add(object)
        order = order + 1
        object.LayoutOrder, object.Parent = order, scroll
        return object
    end
    local function section(text)
        add(create("TextLabel", {
            Name = "Section_" .. text, Size = UDim2.new(1, -6, 0, 20),
            BackgroundTransparency = 1, Text = "— " .. text,
            TextXAlignment = Enum.TextXAlignment.Left,
            TextColor3 = Color3.fromRGB(140, 140, 170), Font = Enum.Font.GothamBold,
            TextSize = 11, ZIndex = 22,
        }))
    end
    local function label(name, initial, color)
        local object = add(create("TextLabel", {
            Name = name, Size = UDim2.new(1, -6, 0, 38), BackgroundTransparency = 1,
            Text = initial, TextColor3 = color or Color3.fromRGB(180, 180, 200),
            TextXAlignment = Enum.TextXAlignment.Left, TextWrapped = true,
            Font = Enum.Font.Gotham, TextSize = 11, ZIndex = 22,
        }))
        return {Set = function(_, text) object.Text = text end}
    end
    local function toggle(text, key, callback)
        local button = add(create("TextButton", {
            Name = "MM2_" .. key, Size = UDim2.new(1, -6, 0, 30), Text = "",
            BackgroundColor3 = Color3.fromRGB(32, 32, 40), BorderSizePixel = 0,
            AutoButtonColor = true, ZIndex = 22,
        }))
        corner(button, 5)
        create("TextLabel", {
            Size = UDim2.new(1, -34, 1, 0), Position = UDim2.fromOffset(8, 0),
            BackgroundTransparency = 1, Text = text, TextColor3 = Color3.fromRGB(220, 220, 230),
            Font = Enum.Font.Gotham, TextSize = 12, TextXAlignment = Enum.TextXAlignment.Left,
            ZIndex = 23,
        }, button)
        local dot = create("Frame", {
            Name = "Dot", Size = UDim2.fromOffset(10, 10), Position = UDim2.new(1, -20, 0.5, -5),
            BorderSizePixel = 0, ZIndex = 23,
        }, button)
        corner(dot, 10)
        local control = {CurrentValue = CFG[key]}
        local function renderDot()
            dot.BackgroundColor3 = CFG[key] and Color3.fromRGB(90, 230, 130) or Color3.fromRGB(70, 70, 85)
            control.CurrentValue = CFG[key]
        end
        function control:Set(value)
            if not running then return end
            CFG[key] = value == true
            renderDot()
            if callback then callback(CFG[key]) end
        end
        connect(button.Activated, function() control:Set(not CFG[key]) end)
        renderDot()
        return control
    end
    local function numberRow(text, key, minimum, maximum, callback)
        local row = add(create("Frame", {
            Name = "Row_" .. key, Size = UDim2.new(1, -6, 0, 30),
            BackgroundColor3 = Color3.fromRGB(32, 32, 40), BorderSizePixel = 0, ZIndex = 22,
        }))
        corner(row, 5)
        create("TextLabel", {
            Size = UDim2.new(1, -76, 1, 0), Position = UDim2.fromOffset(8, 0),
            BackgroundTransparency = 1, Text = text, TextColor3 = Color3.fromRGB(220, 220, 230),
            Font = Enum.Font.Gotham, TextSize = 12, TextXAlignment = Enum.TextXAlignment.Left,
            ZIndex = 23,
        }, row)
        local input = create("TextBox", {
            Name = "MM2_" .. key, Size = UDim2.fromOffset(60, 22), Position = UDim2.new(1, -68, 0.5, -11),
            BackgroundColor3 = Color3.fromRGB(22, 22, 28), BorderSizePixel = 0,
            Text = tostring(CFG[key]), TextColor3 = Color3.fromRGB(150, 220, 255),
            Font = Enum.Font.GothamBold, TextSize = 12, ClearTextOnFocus = false, ZIndex = 23,
        }, row)
        corner(input, 4)
        connect(input.FocusLost, function()
            if not running then return end
            local value = tonumber(input.Text)
            if value and value == value then
                CFG[key] = math.clamp(value, minimum, maximum)
                if callback then callback(CFG[key]) end
            end
            input.Text = tostring(CFG[key])
        end)
    end
    local function button(name, text, color, callback)
        local object = add(create("TextButton", {
            Name = name, Size = UDim2.new(1, -6, 0, 30), BackgroundColor3 = color,
            BorderSizePixel = 0, Text = text, TextColor3 = WHITE,
            Font = Enum.Font.GothamBold, TextSize = 12, ZIndex = 22,
        }))
        corner(object, 5)
        connect(object.Activated, callback)
    end

    section("PLAYERS")
    toggle("Player ESP", "PlayerESP")
    toggle("Caixa (box)", "Box")
    toggle("Linha (tracer)", "Tracer")
    toggle("Ignorar eu", "IgnoreLocal")
    section("MOEDAS")
    CoinLabel = label("CoinStatus", "Procurando moedas...", GOLD)
    toggle("Coin ESP", "CoinESP")
    toggle("Caixa nas moedas", "CoinBox")
    toggle("Nome e distancia", "CoinText")
    toggle("Linha ate moeda", "CoinTracer")
    FlyToggle = toggle("Voar em pe ate moedas", "AutoFly", function(on)
        if not on then stopFlight() end
    end)
    numberRow("Velocidade voo", "FlySpeed", 5, 120)
    numberRow("Pausa na moeda", "CollectionWait", 0.1, 2)
    FlightLabel = label("FlightStatus", "Voo desligado")
    button("Rescan", "Atualizar busca", Color3.fromRGB(32, 32, 40), function()
        if running then rescanRequested = true end
    end)
    section("ITENS")
    toggle("Item ESP", "ItemESP")
    section("MUNDO")
    toggle("Fullbright", "Fullbright", applyFullbright)
    toggle("Noclip", "Noclip", function(on) applyNoclip(LP.Character, on or flight ~= nil) end)
    toggle("Aplicar velocidade/pulo", "Movement", function(on)
        if on then applyMovement() else restoreMovement() end
    end)
    numberRow("WalkSpeed", "WalkSpeed", 16, 300, applyMovement)
    numberRow("JumpPower", "JumpPower", 50, 400, applyMovement)
    section("OUTROS")
    numberRow("Dist. max", "MaxDist", 50, 5000)
    button("Unload", "UNLOAD", Color3.fromRGB(120, 40, 45), unload)
end
local ready, interfaceError = pcall(setupInterface)
if not ready then
    unload()
    warn("[MM2 HUB] Erro no menu: " .. tostring(interfaceError))
    return
end

local lastCoinText, lastFlightText
local function refreshLabels()
    if CoinLabel and status.Text ~= lastCoinText then
        lastCoinText = status.Text
        CoinLabel:Set(status.Text)
    end
    if FlightLabel and flightStatus.Text ~= lastFlightText then
        lastFlightText = flightStatus.Text
        FlightLabel:Set(flightStatus.Text)
    end
end
local dragInput, dragStart, startPosition
connect(title.InputBegan, function(input)
    if input.UserInputType == Enum.UserInputType.MouseButton1 or input.UserInputType == Enum.UserInputType.Touch then
        dragInput, dragStart, startPosition = input, input.Position, main.Position
    end
end)
connect(UIS.InputChanged, function(input)
    if not dragInput then return end
    local mouseMove = dragInput.UserInputType == Enum.UserInputType.MouseButton1
        and input.UserInputType == Enum.UserInputType.MouseMovement
    if input == dragInput or mouseMove then
        local delta = input.Position - dragStart
        local camera = workspace.CurrentCamera
        local viewport = camera and camera.ViewportSize or Vector2.new(800, 600)
        main.Position = UDim2.fromOffset(
            math.clamp(startPosition.X.Offset + delta.X, 0, math.max(0, viewport.X - 60)),
            math.clamp(startPosition.Y.Offset + delta.Y, 0, math.max(0, viewport.Y - 32))
        )
    end
end)
connect(UIS.InputEnded, function(input)
    if input == dragInput or (dragInput and dragInput.UserInputType == Enum.UserInputType.MouseButton1
        and input.UserInputType == Enum.UserInputType.MouseButton1) then dragInput = nil end
end)
connect(workspace.DescendantAdded, function(object) if running then discover(object) end end)
connect(workspace.DescendantRemoving, function(object) removeCoin(object); clearItem(object) end)
connect(CollectionService:GetInstanceAddedSignal("Coin"), function(object)
    if running then track(coinRoot(object)) end
end)
connect(CollectionService:GetInstanceRemovedSignal("Coin"), function() rescanRequested = true end)
connect(Players.PlayerRemoving, removePlayer)
connect(LP.CharacterRemoving, function()
    pauseFlight()
    releaseNoclip()
    restoreMovement()
end)
connect(RunService.PreSimulation, function(dt)
    local ok, message = pcall(flightStep, dt)
    if not ok then
        pauseFlight()
        flightStatus.Text = "Voo interrompido; veja o console"
        warn("[MM2 HUB] Voo: " .. tostring(message))
    end
    local character = LP.Character
    local hum = character and character:FindFirstChildOfClass("Humanoid")
    applyNoclip(character, hum and hum.Health > 0 and (CFG.Noclip or flight ~= nil))
end)
connect(RunService.RenderStepped, render)
local elapsed, scanElapsed = 0, 0
connect(RunService.Heartbeat, function(dt)
    elapsed, scanElapsed = elapsed + dt, scanElapsed + dt
    if elapsed < CFG.UpdateInterval then return end
    elapsed = 0
    if rescanRequested or scanElapsed >= CFG.RescanInterval then
        rescanRequested, scanElapsed = false, 0
        scan()
    end
    refresh()
    refreshItems(workspace.CurrentCamera)
    applyMovement()
    if CFG.Fullbright then applyFullbright(true) end
    refreshLabels()
end)
connect(UIS.InputBegan, function(input, processed)
    if processed or UIS:GetFocusedTextBox() then return end
    if input.KeyCode == Enum.KeyCode.RightShift then
        main.Visible = not main.Visible
    elseif input.KeyCode == Enum.KeyCode.End then
        unload()
    end
end)
scan()
refresh()
refreshItems(workspace.CurrentCamera)
applyMovement()
refreshLabels()
