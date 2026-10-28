import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14956 = true := by
  decide +kernel

theorem tot14956 : totK PD2M8K2 D2M8K2.t14956 = [0, 181579309578, 444868167705, 262490003756, 29207709579, 0, 0, 0] := by
  decide +kernel

theorem rows14957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14957 = true := by
  decide +kernel

theorem tot14957 : totK PD2M8K2 D2M8K2.t14957 = [0, 104179871769, 440742119000, 329255241170, 35259403363, 0, 0, 0] := by
  decide +kernel

theorem rows14958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14958 = true := by
  decide +kernel

theorem tot14958 : totK PD2M8K2 D2M8K2.t14958 = [0, 67421206113, 305793510165, 427840269093, 100711594663, 1429815836, 0, 0] := by
  decide +kernel

theorem rows14959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14959 = true := by
  decide +kernel

theorem tot14959 : totK PD2M8K2 D2M8K2.t14959 = [0, 181958296282, 471821526877, 253876281201, 23322141510, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
