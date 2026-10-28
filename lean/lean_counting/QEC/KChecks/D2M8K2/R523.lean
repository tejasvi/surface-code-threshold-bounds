import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2092 = true := by
  decide +kernel

theorem tot2092 : totK PD2M8K2 D2M8K2.t2092 = [0, 0, 166168681481, 466169347078, 229513702657, 9064506700, 0, 0] := by
  decide +kernel

theorem rows2093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2093 = true := by
  decide +kernel

theorem tot2093 : totK PD2M8K2 D2M8K2.t2093 = [0, 0, 70852419618, 350708446583, 387057432982, 74411443496, 1310285577, 0] := by
  decide +kernel

theorem rows2094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2094 = true := by
  decide +kernel

theorem tot2094 : totK PD2M8K2 D2M8K2.t2094 = [0, 0, 72115230909, 370193740351, 408984457537, 40135168055, 0, 0] := by
  decide +kernel

theorem rows2095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2095 = true := by
  decide +kernel

theorem tot2095 : totK PD2M8K2 D2M8K2.t2095 = [0, 0, 172144073541, 449643902465, 270799305479, 25592387646, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
