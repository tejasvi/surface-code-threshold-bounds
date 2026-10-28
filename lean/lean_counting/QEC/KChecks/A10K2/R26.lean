import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t104 = true := by
  decide +kernel

theorem tot104 : totK PA10K2 A10K2.t104 = [185282364397, 1297514627093, 2275331212774, 1037069731006, 103419867757, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t105 = true := by
  decide +kernel

theorem tot105 : totK PA10K2 A10K2.t105 = [77751972864, 582683804361, 1765261359941, 1792919096850, 484697756840, 30831673886, 0, 0, 0, 0] := by
  decide +kernel

theorem rows106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t106 = true := by
  decide +kernel

theorem tot106 : totK PA10K2 A10K2.t106 = [441323131297, 1758980768201, 1931206090895, 512544020769, 26491486257, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t107 = true := by
  decide +kernel

theorem tot107 : totK PA10K2 A10K2.t107 = [65877326683, 756063022298, 1935559796656, 1532301246648, 361150980793, 25734533292, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
