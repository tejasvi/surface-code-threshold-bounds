import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5368 = true := by
  decide +kernel

theorem tot5368 : totK PD2M8K2 D2M8K2.t5368 = [0, 0, 179945842210, 444288110445, 268261290588, 30177078596, 0, 0] := by
  decide +kernel

theorem rows5369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5369 = true := by
  decide +kernel

theorem tot5369 : totK PD2M8K2 D2M8K2.t5369 = [0, 0, 208128947429, 488154097430, 214587889489, 9194426045, 0, 0] := by
  decide +kernel

theorem rows5370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5370 = true := by
  decide +kernel

theorem tot5370 : totK PD2M8K2 D2M8K2.t5370 = [0, 0, 189573429010, 473150886396, 221028855348, 14815639298, 0, 0] := by
  decide +kernel

theorem rows5371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5371 = true := by
  decide +kernel

theorem tot5371 : totK PD2M8K2 D2M8K2.t5371 = [0, 0, 164268887527, 435118964568, 273739051338, 27718573415, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
