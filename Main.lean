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

def server := #server [schema]{
  .dbService
    {
      name := "userMessage",
      args := [("message", .string), ("chatId", .string)],
      res := option .string,
      roles := .roles ["user", "admin"]
    }
    (
      [laydown|
        do {
          let n ← now,
          let u ← uuid,
          let r_ := chatMessage#insertI (chatId, u,) {timestamp := n, content := Mk(userMessage, {text := message})},
          return Mk(none)
        }
      ]
    )
}


def app := #rapp [server] {
    [laydown|
      [ui|
        ola mundo
      ]
    ]
}


#eval genApp app
--#eval deployApp "localhost" 6401 app

--def main : IO Unit :=
--  IO.println s!"Hello, !"
