import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13412 = true := by
  decide +kernel

theorem tot13412 : totK PD2M8K2 D2M8K2.t13412 = [0, 0, 0, 192308070507, 475755438877, 192333438082, 12177165453, 0] := by
  decide +kernel

theorem rows13413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13413 = true := by
  decide +kernel

theorem tot13413 : totK PD2M8K2 D2M8K2.t13413 = [0, 0, 0, 266289825864, 490844117209, 128158144319, 2530668022, 0] := by
  decide +kernel

theorem rows13414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13414 = true := by
  decide +kernel

theorem tot13414 : totK PD2M8K2 D2M8K2.t13414 = [0, 0, 0, 228415245584, 469237326550, 166135359181, 11092222415, 0] := by
  decide +kernel

theorem rows13415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13415 = true := by
  decide +kernel

theorem tot13415 : totK PD2M8K2 D2M8K2.t13415 = [0, 0, 0, 166546049220, 479582110767, 204947305146, 8566329634, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
