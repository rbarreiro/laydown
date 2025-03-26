import Laydown

def schema :=
  SchemaDef.new "caaty"
  [
    (
      "chatMessage",
      .tuple [.string, .string],
      .record [
        ("timestamp", .datetime),
        (
          "content",
          .sum [
            (
              "userMessage",
              .record [("text", .string)]
            ),
            (
              "form",
              .record [
              ]
            )
          ]
        )
      ]
    )
  ]

def server := #server ["user"] [schema]{
  .dbService
    {
      name := "userMessage",
      args := [("message", .string), ("chatId", .string)],
      res := option .string,
      access := .roles ["user"]
    }
    (
      [laydown|
        do {
          let n ← now,
          let u ← uuid,
          let r_ ← chatMessage#insertI
                      (chatId, u,)
                      {timestamp := n, content := Mk(userMessage, {text := message})},
          return Mk(none)
        }
      ]
    )
}

def chat [SubEnv ui e] : Lexp e ((roleApi (some "user") server) ⟶ .effect .ui) :=
  [laydown|
    λ api =>
      do{
        let msg ← !createSignal "",
        let send := do{
          let m ← msg#get,
          let _ ← api#userMessage {message := m, chatId := "chat0"},
          return ()
        },
        let change := λ x => do{
          msg#set x,
          return ()
        },
        [ui|
          Chat<br>
          ___(change) b[Send](send)
        ]
      }
  ]

def app := #rapp [server] {
    [laydown|
      do {
        let s ← connect Mk(user, {user := "user", password := "password"}),
        match s with{
          Mk (guest, x) => [ui| Please login ],
          Mk (user, x) => !chat x
        }
      }
    ]
}


#eval genApp app
--#eval deployApp "localhost" 6401 app

--def main : IO Unit :=
--  IO.println s!"Hello, !"
