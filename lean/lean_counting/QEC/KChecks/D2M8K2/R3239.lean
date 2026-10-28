import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12956 = true := by
  decide +kernel

theorem tot12956 : totK PD2M8K2 D2M8K2.t12956 = [0, 107991234938, 377866771757, 379549905303, 50665197736, 0, 0, 0] := by
  decide +kernel

theorem rows12957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12957 = true := by
  decide +kernel

theorem tot12957 : totK PD2M8K2 D2M8K2.t12957 = [0, 200551682437, 475868499663, 223795261055, 14011441845, 0, 0, 0] := by
  decide +kernel

theorem rows12958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12958 = true := by
  decide +kernel

theorem tot12958 : totK PD2M8K2 D2M8K2.t12958 = [0, 111385534382, 432086584054, 316430516691, 35770351126, 0, 0, 0] := by
  decide +kernel

theorem rows12959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12959 = true := by
  decide +kernel

theorem tot12959 : totK PD2M8K2 D2M8K2.t12959 = [0, 0, 175977219671, 448383265059, 260434352089, 25111704080, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
