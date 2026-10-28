import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9272 = true := by
  decide +kernel

theorem tot9272 : totK PD2M8K2 D2M8K2.t9272 = [0, 195454112708, 464453960781, 217843109197, 16961779594, 0, 0, 0] := by
  decide +kernel

theorem rows9273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9273 = true := by
  decide +kernel

theorem tot9273 : totK PD2M8K2 D2M8K2.t9273 = [0, 187889714047, 493160188859, 193887713756, 3705122438, 0, 0, 0] := by
  decide +kernel

theorem rows9274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9274 = true := by
  decide +kernel

theorem tot9274 : totK PD2M8K2 D2M8K2.t9274 = [0, 163374322970, 455443063530, 242961665351, 15082621884, 0, 0, 0] := by
  decide +kernel

theorem rows9275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9275 = true := by
  decide +kernel

theorem tot9275 : totK PD2M8K2 D2M8K2.t9275 = [0, 0, 282407795175, 482692727224, 86631235121, 1239866073, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
