module Helpers.ANSI where

import Data.Text (Text)

-- | This uses ANSI to color the text in red.
colorInRed :: Text -> Text
colorInRed t = "\ESC[31m" <> t <> "\ESC[97m"

-- | This uses ANSI to color the text in green.
colorInGreen :: Text -> Text
colorInGreen t = "\ESC[32m" <> t <> "\ESC[97m"

-- | This uses Unicode to display a heavy check mark and ANSI to color the text green.
successText :: Text -> Text
successText t = colorInGreen $ "[\x2714] " <> t

-- | This uses Unicode to display a heavy ballot X and ANSI to color the text red.
failureText :: Text -> Text
failureText t = colorInRed $ "[\x2718] " <> t

bold :: Text -> Text
bold t = "\ESC[1m" <> t <> "\ESC[22m"
