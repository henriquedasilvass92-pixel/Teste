--===============================================================
-- MM2 HUB | ESP + UTILIDADES | Orion Library + pistola do xerife + moedas
-- RightShift: menu | End: remover | Celular: botao MM2 HUB
-- Execute um unico script no cliente. Carrega uma versao fixa da Orion Library.
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
    PlayerESP = true, Box = true, Tracer = false, IgnoreLocal = true, ItemESP = true, GunDropESP = true, AutoGun = false,
    CoinESP = true, CoinBox = true, CoinText = true, CoinTracer = false,
    AutoFly = false, FlySpeed = 35, CoinOffset = Vector3.new(0, 2, 0),
    ArrivalRadius = 0.65, CollectionWait = 0.5, RetryDelay = 8,
    Fullbright = false, Noclip = false, Movement = true,
    WalkSpeed = 16, JumpPower = 50, MaxDist = 600,
    UpdateInterval = 0.15, RescanInterval = 8,
    GunAttemptTime = 1.5, GunRetryDelay = 3,
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
local WEAPON_NAMES = {gun = true, knife = true, revolver = true, gundrop = true, knifedrop = true, droppedgun = true, revolverdrop = true}
local connections, coinPool, itemPool, playerPool = {}, {}, {}, {}
local running, rescanRequested = true, false
local OrionLib, orionGui, orionMain, orionScale
local FlyToggle, GunToggle, CoinLabel, FlightLabel, GunLabel
local menuVisible = true
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
    DisplayOrder = 10, ZIndexBehavior = Enum.ZIndexBehavior.Sibling,
}, playerGui)
local overlay = create("Frame", {
    Name = "ESP", Size = UDim2.fromScale(1, 1),
    BackgroundTransparency = 1, BorderSizePixel = 0,
}, gui)
local function renderFly()
    if FlyToggle and FlyToggle.Value ~= CFG.AutoFly then FlyToggle:Set(CFG.AutoFly) end
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
    if data and data.highlight then data.highlight:Destroy() end
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

-- PISTOLA CAIDA: detecao local independente do ESP; nao cria/duplica ferramentas.
local GUN_NAMES = {gun = true, revolver = true, gundrop = true, droppedgun = true, revolverdrop = true}
local gunClock, gunJob = 0, nil
local gunCooldowns = setmetatable({}, {__mode = "k"})
local gunStatus = {Text = "Aguardando pistola cair no mapa"}
local function isGunDrop(root)
    return root and GUN_NAMES[normalized(root.Name)] and weaponRoot(root) == root
end
local function localHasTool(names)
    for _, container in pairs({LP.Character, LP:FindFirstChild("Backpack")}) do
        if container then
            for _, object in ipairs(container:GetChildren()) do
                if object:IsA("Tool") and names[normalized(object.Name)] then return true end
            end
        end
    end
    return false
end
local function hasGun()
    return localHasTool({gun = true, revolver = true, sheriffgun = true})
end
local function pickupPart(root)
    if not isGunDrop(root) then return nil end
    -- A peca com TouchTransmitter pode ser um hitbox transparente.
    if root:IsA("BasePart") and root:FindFirstChildOfClass("TouchTransmitter") then return root end
    for _, object in ipairs(root:GetDescendants()) do
        if object:IsA("BasePart") and object:FindFirstChildOfClass("TouchTransmitter") then return object end
    end
    if root:IsA("Tool") then
        local handle = root:FindFirstChild("Handle")
        if handle and handle:IsA("BasePart") then return handle end
    end
    return getPart(root)
end
local function nearestGun(position, respectCooldown)
    local best, bestPart, bestDistance, bestRank = nil, nil, math.huge, -1
    for root in pairs(itemPool) do
        if isGunDrop(root) and (not respectCooldown or (gunCooldowns[root] or 0) <= gunClock) then
            local part = pickupPart(root)
            if part then
                local name = normalized(root.Name)
                local rank = (name == "gundrop" or name == "droppedgun" or name == "revolverdrop") and 2 or 1
                local distance = (part.Position - position).Magnitude
                if rank > bestRank or (rank == bestRank and distance < bestDistance) then
                    best, bestPart, bestDistance, bestRank = root, part, distance, rank
                end
            end
        end
    end
    return best, bestPart, bestDistance
end
local function freeCharacter()
    local character = LP.Character
    local hum = character and character:FindFirstChildOfClass("Humanoid")
    local root = character and character:FindFirstChild("HumanoidRootPart")
    if not hum or hum.Health <= 0 or not root or not root:IsA("BasePart") then return nil end
    if root.Anchored or hum.Sit then return nil end
    return character, hum, root
end
local function moveToGun(root, target, part)
    if not part or not isGunDrop(target) or not part:IsDescendantOf(workspace) then return false end
    -- Interrompe o voo de moedas para que ele nao afaste o personagem da pistola.
    pauseFlight()
    root.AssemblyLinearVelocity, root.AssemblyAngularVelocity = ZERO, ZERO
    root.CFrame = CFrame.new(part.Position + Vector3.new(0, 2.25, 0)) * root.CFrame.Rotation
    return true
end
local function teleportToGun()
    if not running then return end
    local _, _, root = freeCharacter()
    if not root then gunStatus.Text = "Aguarde um personagem vivo e livre"; return end
    local target, part = nearestGun(root.Position, false)
    if not target then gunStatus.Text = "Nenhuma pistola caida carregada no cliente"; return end
    if moveToGun(root, target, part) then gunStatus.Text = "Teleportado para a pistola caida" end
end
local function gunStep(dt)
    gunClock = gunClock + math.max(dt, 0)
    if hasGun() then
        gunJob = nil
        gunStatus.Text = "Pistola confirmada no inventario"
        return
    end
    local character, _, root = freeCharacter()
    if not character then
        gunJob = nil
        gunStatus.Text = "Aguardando personagem vivo e livre"
        return
    end
    if not CFG.AutoGun then
        gunJob = nil
        local target, _, distance = nearestGun(root.Position, false)
        gunStatus.Text = target and ("Pistola caida: " .. fmtDist(distance) .. " studs") or "Aguardando pistola cair no mapa"
        return
    end
    if localHasTool({knife = true}) then
        gunJob = nil
        gunStatus.Text = "Coleta pausada: personagem com Knife"
        return
    end
    if gunJob and gunJob.character ~= character then gunJob = nil end
    if gunJob then
        local job = gunJob
        local part = pickupPart(job.target)
        if not part then
            gunCooldowns[job.target] = gunClock + CFG.GunRetryDelay
            gunJob = nil
            gunStatus.Text = "Pistola retirada do chao; aguardando inventario"
            return
        end
        if gunClock >= job.deadline or (part.Position - root.Position).Magnitude > 8 then
            gunCooldowns[job.target] = gunClock + CFG.GunRetryDelay
            gunJob = nil
            gunStatus.Text = "Coleta nao confirmada; aguardando nova tentativa"
            return
        end
        gunStatus.Text = "Aguardando o jogo confirmar a coleta"
        if gunClock >= job.nextTouch then
            job.nextTouch = gunClock + 0.25
            if type(firetouchinterest) == "function" then
                -- Opcional no executor; sem suporte, a queda normal apos o TP faz a aproximacao.
                pcall(function()
                    firetouchinterest(root, part, 0)
                    firetouchinterest(root, part, 1)
                end)
            end
        end
        return
    end
    local target, part = nearestGun(root.Position, true)
    if not target then gunStatus.Text = "Auto coleta ativa; aguardando pistola disponivel"; return end
    if moveToGun(root, target, part) then
        gunJob = {target = target, character = character,
            deadline = gunClock + CFG.GunAttemptTime, nextTouch = gunClock}
        gunStatus.Text = "Indo pegar a pistola caida"
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
            local gunDrop = isGunDrop(root)
            local enabled = (gunDrop and CFG.GunDropESP) or (not gunDrop and CFG.ItemESP)
            if enabled and camera and data.part and distance <= CFG.MaxDist then
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
                data.text.Text = (gunDrop and "PISTOLA CAIDA" or string.upper(root.Name)) .. " [" .. fmtDist(distance) .. "]"
                if gunDrop then
                    if not data.highlight or data.highlight.Parent ~= data.part then
                        if data.highlight then data.highlight:Destroy() end
                        data.highlight = create("Highlight", {
                            Name = "MM2GunDropHighlight", Adornee = root:IsA("Model") and root or data.part,
                            DepthMode = Enum.HighlightDepthMode.AlwaysOnTop, FillColor = C.Gun,
                            OutlineColor = C.Gun, FillTransparency = 0.75, OutlineTransparency = 0,
                        }, data.part)
                    end
                end
            else
                if data.marker then data.marker.Enabled = false end
                if data.highlight then data.highlight:Destroy(); data.highlight = nil end
            end
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

-- ORION LIBRARY: versao fixa, carregada do repositorio do autor.
unload = function(destroyWindow)
    if not running then return end
    running = false
    CFG.AutoFly, CFG.AutoGun, gunJob = false, false, nil
    for _, connection in ipairs(connections) do connection:Disconnect() end
    stopFlight()
    releaseNoclip()
    restoreMovement()
    applyFullbright(false)
    for player in pairs(playerPool) do removePlayer(player) end
    for coin in pairs(coinPool) do removeCoin(coin) end
    for item in pairs(itemPool) do clearItem(item) end
    if gui.Parent then gui:Destroy() end
    if destroyWindow and OrionLib then OrionLib:Destroy() end
end
connect(gui.Destroying, function() unload(true) end)

local uiParent = playerGui
if type(gethui) == "function" then
    local ok, parent = pcall(gethui)
    if ok and parent then uiParent = parent end
end
local loaded, library = pcall(function()
    assert(type(loadstring) == "function", "O executor nao oferece loadstring.")
    local url = "https://raw.githubusercontent.com/jensonhirst/Orion/8f28028b08e4f719307b86133918724c52724c27/source"
    local source = game:HttpGet(url)
    assert(type(source) == "string" and #source > 0, "Resposta vazia ao carregar Orion.")
    -- Nome exclusivo: a Orion nao remove janelas de outros scripts.
    source = source:gsub('Orion.Name = "Orion"', 'Orion.Name = "MM2HubOrionUI"', 1)
    source = source:gsub('local function SaveCfg%(Name%)', 'local function SaveCfg(Name)\n if not OrionLib.SaveCfg then return end', 1)
    local chunk, message = loadstring(source)
    assert(chunk, message)
    if type(setfenv) == "function" and type(getfenv) == "function" then
        -- Compatibilidade com executores sem gethui, sem alterar o ambiente global.
        local environment = setmetatable({gethui = function() return uiParent end, syn = false}, {__index = getfenv(chunk)})
        setfenv(chunk, environment)
    end
    return chunk()
end)
if not loaded or type(library) ~= "table" or type(library.MakeWindow) ~= "function" then
    unload(false)
    local partial = uiParent:FindFirstChild("MM2HubOrionUI")
    if partial then partial:Destroy() end
    warn("[MM2 HUB] Nao foi possivel carregar Orion: " .. tostring(library))
    return
end
OrionLib = library
local originalDestroy = OrionLib.Destroy
OrionLib.Destroy = function(self)
    unload(false)
    for _, connection in ipairs(self.Connections or {}) do connection:Disconnect() end
    if originalDestroy then return originalDestroy(self) end
end
local function setMenuVisible(on)
    menuVisible = on == true
    if orionMain then orionMain.Visible = menuVisible end
end
local function resizeOrion()
    local camera = workspace.CurrentCamera
    if orionScale and camera then
        local viewport = camera.ViewportSize
        orionScale.Scale = math.min(1, math.max(0.35, math.min((viewport.X - 20) / 615, (viewport.Y - 80) / 344)))
    end
end
local function setupInterface()
    local window = OrionLib:MakeWindow({Name = "MM2 HUB | ESP + Pistola",
        HidePremium = true, SaveConfig = false, ConfigFolder = "MM2HubOrion",
        IntroEnabled = false, CloseCallback = function() menuVisible = false end})
    local function tab(name)
        return window:MakeTab({Name = name, Icon = "", PremiumOnly = false})
    end
    local playersTab, coinsTab, gunTab, worldTab, settingsTab = tab("Jogadores"), tab("Moedas"), tab("Pistola e itens"), tab("Mundo"), tab("Configuracoes")
    local function toggle(parent, name, key, callback)
        return parent:AddToggle({Name = name, Default = CFG[key], Save = false, Flag = "MM2_" .. key,
            Callback = function(value)
                if not running then return end
                CFG[key] = value == true
                if callback then callback(CFG[key]) end
            end})
    end
    local function number(parent, name, key, minimum, maximum, callback)
        parent:AddTextbox({Name = name, Default = tostring(CFG[key]), TextDisappear = false,
            Callback = function(text)
                if not running then return end
                local value = tonumber(text)
                if value and value == value then
                    CFG[key] = math.clamp(value, minimum, maximum)
                    if callback then callback(CFG[key]) end
                end
            end})
    end
    playersTab:AddSection({Name = "Visualizacao"})
    toggle(playersTab, "Player ESP", "PlayerESP")
    toggle(playersTab, "Caixa e barra de vida", "Box")
    toggle(playersTab, "Linha ate jogadores", "Tracer")
    toggle(playersTab, "Ignorar meu personagem", "IgnoreLocal")
    playersTab:AddParagraph("Papeis", "Cores inferidas pelas ferramentas visiveis no cliente: Knife em vermelho e Gun/Revolver em azul.")
    coinsTab:AddSection({Name = "ESP de moedas"})
    CoinLabel = coinsTab:AddLabel("Procurando moedas...")
    toggle(coinsTab, "Coin ESP", "CoinESP")
    toggle(coinsTab, "Caixa nas moedas", "CoinBox")
    toggle(coinsTab, "Nome e distancia", "CoinText")
    toggle(coinsTab, "Linha ate moedas", "CoinTracer")
    coinsTab:AddSection({Name = "Voo em pe"})
    FlyToggle = toggle(coinsTab, "Voar em pe ate moedas", "AutoFly", function(on) if not on then stopFlight() end end)
    number(coinsTab, "Velocidade voo (5-120)", "FlySpeed", 5, 120)
    number(coinsTab, "Pausa na moeda (0.1-2 s)", "CollectionWait", 0.1, 2)
    FlightLabel = coinsTab:AddLabel("Voo desligado")
    gunTab:AddSection({Name = "Pistola do xerife caida"})
    GunLabel = gunTab:AddLabel("Aguardando pistola cair no mapa")
    toggle(gunTab, "ESP da pistola caida", "GunDropESP")
    gunTab:AddButton({Name = "Teleportar para a pistola caida", Callback = teleportToGun})
    GunToggle = toggle(gunTab, "Pegar pistola automaticamente", "AutoGun", function(on)
        if not on then gunJob = nil end
    end)
    gunTab:AddParagraph("Coleta", "A busca automatica leva o personagem ate a pistola. A confirmacao acontece quando Gun/Revolver aparece na mochila ou na mao. O voo de moedas e pausado ao ir para a arma.")
    gunTab:AddSection({Name = "Outros itens"})
    toggle(gunTab, "ESP de outras armas largadas", "ItemESP")
    gunTab:AddButton({Name = "Atualizar busca de moedas e armas", Callback = function() if running then rescanRequested = true end end})
    worldTab:AddSection({Name = "Ambiente"})
    toggle(worldTab, "Fullbright", "Fullbright", applyFullbright)
    toggle(worldTab, "Noclip manual", "Noclip", function(on) applyNoclip(LP.Character, on or flight ~= nil) end)
    worldTab:AddSection({Name = "Personagem"})
    toggle(worldTab, "Aplicar velocidade e pulo", "Movement", function(on) if on then applyMovement() else restoreMovement() end end)
    number(worldTab, "WalkSpeed (16-300)", "WalkSpeed", 16, 300, applyMovement)
    number(worldTab, "JumpPower (50-400)", "JumpPower", 50, 400, applyMovement)
    number(settingsTab, "Distancia maxima ESP/moedas (50-5000)", "MaxDist", 50, 5000)
    settingsTab:AddParagraph("Controles", "RightShift abre/fecha o menu. No celular, toque em MM2 HUB. End ou Remover hub encerra os recursos e restaura os estados.")
    settingsTab:AddButton({Name = "Remover hub", Callback = function() unload(true) end})
    OrionLib:Init()
    orionGui = uiParent:FindFirstChild("MM2HubOrionUI")
    assert(orionGui, "A janela Orion nao foi encontrada no cliente.")
    orionGui.ResetOnSpawn, orionGui.DisplayOrder = false, 1000
    for _, child in ipairs(orionGui:GetChildren()) do
        if child:IsA("Frame") and child:FindFirstChild("TopBar") then orionMain = child; break end
    end
    assert(orionMain, "Painel principal da Orion nao encontrado.")
    orionScale = create("UIScale", {Scale = 1}, orionMain)
    resizeOrion()
    connect(orionGui.Destroying, function() unload(false) end)
    local button = create("TextButton", {
        Name = "MenuButton", Size = UDim2.fromOffset(90, 34), Position = UDim2.fromOffset(14, 80),
        BackgroundColor3 = Color3.fromRGB(25, 25, 25), BorderSizePixel = 0,
        Text = "MM2 HUB", TextColor3 = WHITE, Font = Enum.Font.GothamBold, TextSize = 12, ZIndex = 30,
    }, gui)
    corner(button, 8)
    connect(button.Activated, function() setMenuVisible(not menuVisible) end)
    -- A Orion classica arrasta com mouse; este trecho acrescenta o arraste por toque.
    local top = orionMain:FindFirstChild("TopBar")
    top.Active = true
    local touch, touchStart, frameStart
    connect(top.InputBegan, function(input)
        if input.UserInputType == Enum.UserInputType.Touch then touch, touchStart, frameStart = input, input.Position, orionMain.Position end
    end)
    connect(UIS.InputChanged, function(input)
        if input == touch then
            local delta = input.Position - touchStart
            orionMain.Position = UDim2.new(frameStart.X.Scale, frameStart.X.Offset + delta.X, frameStart.Y.Scale, frameStart.Y.Offset + delta.Y)
        end
    end)
    connect(UIS.InputEnded, function(input) if input == touch then touch = nil end end)
end
local ready, message = pcall(setupInterface)
if not ready then unload(true); warn("[MM2 HUB] Orion: " .. tostring(message)); return end
local lastCoinText, lastFlightText, lastGunText
local function refreshLabels()
    if CoinLabel and status.Text ~= lastCoinText then lastCoinText = status.Text; CoinLabel:Set((status.Text:gsub("\n", " | "))) end
    if FlightLabel and flightStatus.Text ~= lastFlightText then lastFlightText = flightStatus.Text; FlightLabel:Set(flightStatus.Text) end
    if GunLabel and gunStatus.Text ~= lastGunText then lastGunText = gunStatus.Text; GunLabel:Set(gunStatus.Text) end
end
connect(workspace.DescendantAdded, function(object) if running then discover(object) end end)
connect(workspace.DescendantRemoving, function(object) removeCoin(object); clearItem(object) end)
connect(CollectionService:GetInstanceAddedSignal("Coin"), function(object)
    if running then track(coinRoot(object)) end
end)
connect(CollectionService:GetInstanceRemovedSignal("Coin"), function() rescanRequested = true end)
connect(Players.PlayerRemoving, removePlayer)
connect(LP.CharacterRemoving, function()
    gunJob = nil
    pauseFlight()
    releaseNoclip()
    restoreMovement()
end)
connect(RunService.PreSimulation, function(dt)
    if gunJob and CFG.AutoFly then pauseFlight() end
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
    local elapsedGun = elapsed
    elapsed = 0
    if rescanRequested or scanElapsed >= CFG.RescanInterval then
        rescanRequested, scanElapsed = false, 0
        scan()
    end
    refresh()
    refreshItems(workspace.CurrentCamera)
    local ok, message = pcall(gunStep, elapsedGun)
    if not ok then
        gunJob = nil
        if GunToggle then GunToggle:Set(false) else CFG.AutoGun = false end
        warn("[MM2 HUB] Pistola: " .. tostring(message))
    end
    applyMovement()
    if CFG.Fullbright then applyFullbright(true) end
    resizeOrion()
    refreshLabels()
end)
connect(UIS.InputBegan, function(input, processed)
    if processed or UIS:GetFocusedTextBox() then return end
    if input.KeyCode == Enum.KeyCode.RightShift then
        setMenuVisible(not menuVisible)
    elseif input.KeyCode == Enum.KeyCode.End then
        unload(true)
    end
end)
scan()
refresh()
refreshItems(workspace.CurrentCamera)
applyMovement()
refreshLabels()
