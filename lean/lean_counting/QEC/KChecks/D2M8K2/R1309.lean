import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5236 = true := by
  decide +kernel

theorem tot5236 : totK PD2M8K2 D2M8K2.t5236 = [0, 170862182657, 467580720009, 266242938456, 26906571523, 0, 0, 0] := by
  decide +kernel

theorem rows5237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5237 = true := by
  decide +kernel

theorem tot5237 : totK PD2M8K2 D2M8K2.t5237 = [0, 0, 177053538203, 447796296916, 253079477816, 25373788367, 0, 0] := by
  decide +kernel

theorem rows5238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5238 = true := by
  decide +kernel

theorem tot5238 : totK PD2M8K2 D2M8K2.t5238 = [0, 0, 213406221805, 497762099003, 195279415356, 5430665091, 0, 0] := by
  decide +kernel

theorem rows5239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5239 = true := by
  decide +kernel

theorem tot5239 : totK PD2M8K2 D2M8K2.t5239 = [0, 156254519113, 370099766416, 267360123134, 110695100493, 6804944647, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
