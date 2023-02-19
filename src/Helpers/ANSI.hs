module Helpers.ANSI where

import Data.Text (Text)

colorInRed :: Text -> Text
colorInRed t = "\ESC[31m" <> t <> "\ESC[97m"

bold :: Text -> Text
bold t = "\ESC[1m" <> t <> "\ESC[22m"
