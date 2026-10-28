import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6504 = true := by
  decide +kernel

theorem tot6504 : totK PA10K2 A10K2.t6504 = [0, 0, 0, 1040151265596, 2425612804649, 1019330923112, 70010502433, 0, 0, 0] := by
  decide +kernel

theorem rows6505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6505 = true := by
  decide +kernel

theorem tot6505 : totK PA10K2 A10K2.t6505 = [0, 511028321977, 1682706476578, 1554047937060, 633005109994, 491551511498, 144586921448, 6354482628, 0, 0] := by
  decide +kernel

theorem rows6506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6506 = true := by
  decide +kernel

theorem tot6506 : totK PA10K2 A10K2.t6506 = [0, 116150967364, 889045580074, 2195534402606, 1640947430270, 289259304479, 7237400819, 0, 0, 0] := by
  decide +kernel

theorem rows6507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6507 = true := by
  decide +kernel

theorem tot6507 : totK PA10K2 A10K2.t6507 = [0, 469604387256, 1832758999862, 1997074381851, 562821558965, 32780555804, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
