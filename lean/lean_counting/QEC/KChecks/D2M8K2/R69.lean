import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t276 = true := by
  decide +kernel

theorem tot276 : totK PD2M8K2 D2M8K2.t276 = [0, 156277929291, 454404174288, 273234815770, 18894005237, 0, 0, 0] := by
  decide +kernel

theorem rows277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t277 = true := by
  decide +kernel

theorem tot277 : totK PD2M8K2 D2M8K2.t277 = [0, 0, 269973626948, 508785363901, 114590268870, 1162515529, 0, 0] := by
  decide +kernel

theorem rows278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t278 = true := by
  decide +kernel

theorem tot278 : totK PD2M8K2 D2M8K2.t278 = [0, 87240234242, 330040781023, 377974583170, 101097317047, 4030866388, 0, 0] := by
  decide +kernel

theorem rows279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t279 = true := by
  decide +kernel

theorem tot279 : totK PD2M8K2 D2M8K2.t279 = [0, 172266343934, 455698695259, 264324869043, 24660925241, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
