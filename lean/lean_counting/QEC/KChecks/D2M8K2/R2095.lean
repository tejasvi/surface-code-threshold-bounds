import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8380 = true := by
  decide +kernel

theorem tot8380 : totK PD2M8K2 D2M8K2.t8380 = [0, 18514691823, 284791301913, 463605346524, 112390979102, 3824247485, 0, 0] := by
  decide +kernel

theorem rows8381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8381 = true := by
  decide +kernel

theorem tot8381 : totK PD2M8K2 D2M8K2.t8381 = [0, 188263917633, 469928558557, 235508109977, 19950425398, 0, 0, 0] := by
  decide +kernel

theorem rows8382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8382 = true := by
  decide +kernel

theorem tot8382 : totK PD2M8K2 D2M8K2.t8382 = [0, 189071721914, 464622839827, 228622296683, 12551143345, 0, 0, 0] := by
  decide +kernel

theorem rows8383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8383 = true := by
  decide +kernel

theorem tot8383 : totK PD2M8K2 D2M8K2.t8383 = [0, 38228932023, 329831105474, 430810589906, 90969198117, 1242138600, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
