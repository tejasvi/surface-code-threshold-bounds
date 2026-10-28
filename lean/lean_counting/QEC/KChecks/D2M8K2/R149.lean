import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t596 = true := by
  decide +kernel

theorem tot596 : totK PD2M8K2 D2M8K2.t596 = [158590860039, 461037492528, 265085950822, 18881656955, 0, 0, 0, 0] := by
  decide +kernel

theorem rows597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t597 = true := by
  decide +kernel

theorem tot597 : totK PD2M8K2 D2M8K2.t597 = [0, 224595093234, 495561175218, 166451149797, 7233348802, 0, 0, 0] := by
  decide +kernel

theorem rows598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t598 = true := by
  decide +kernel

theorem tot598 : totK PD2M8K2 D2M8K2.t598 = [72288947806, 282622128067, 391126380110, 132154494366, 6017336459, 0, 0, 0] := by
  decide +kernel

theorem rows599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t599 = true := by
  decide +kernel

theorem tot599 : totK PD2M8K2 D2M8K2.t599 = [159859753201, 452087368552, 255569876642, 19325996429, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
