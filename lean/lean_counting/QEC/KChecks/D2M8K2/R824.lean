import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3296 = true := by
  decide +kernel

theorem tot3296 : totK PD2M8K2 D2M8K2.t3296 = [0, 0, 259998635878, 491728828751, 148605358672, 3946843644, 0, 0] := by
  decide +kernel

theorem rows3297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3297 = true := by
  decide +kernel

theorem tot3297 : totK PD2M8K2 D2M8K2.t3297 = [0, 135735544409, 334319455287, 335087252091, 121911584611, 8863302705, 0, 0] := by
  decide +kernel

theorem rows3298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3298 = true := by
  decide +kernel

theorem tot3298 : totK PD2M8K2 D2M8K2.t3298 = [0, 186120084929, 471524968592, 235251919112, 14923218525, 0, 0, 0] := by
  decide +kernel

theorem rows3299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3299 = true := by
  decide +kernel

theorem tot3299 : totK PD2M8K2 D2M8K2.t3299 = [0, 118952075233, 447428315118, 320392733571, 35191313595, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
