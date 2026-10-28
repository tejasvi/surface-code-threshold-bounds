import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3664 = true := by
  decide +kernel

theorem tot3664 : totK PA10K2 A10K2.t3664 = [0, 0, 0, 466630630354, 1825160763644, 1943318161396, 513496587724, 31768748853, 0, 0] := by
  decide +kernel

theorem rows3665 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3665 = true := by
  decide +kernel

theorem tot3665 : totK PA10K2 A10K2.t3665 = [0, 0, 505996508307, 1701579956683, 1769114343718, 639196200195, 65047721478, 0, 0, 0] := by
  decide +kernel

theorem rows3666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3666 = true := by
  decide +kernel

theorem tot3666 : totK PA10K2 A10K2.t3666 = [0, 0, 304062355366, 1511872713361, 2070013728760, 724828532804, 43794028532, 0, 0, 0] := by
  decide +kernel

theorem rows3667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3667 = true := by
  decide +kernel

theorem tot3667 : totK PA10K2 A10K2.t3667 = [0, 0, 0, 693833955008, 2130016827795, 1544611918249, 262781531238, 6354482628, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
