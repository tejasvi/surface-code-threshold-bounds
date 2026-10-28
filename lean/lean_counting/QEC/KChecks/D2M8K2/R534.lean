import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2136 = true := by
  decide +kernel

theorem tot2136 : totK PD2M8K2 D2M8K2.t2136 = [0, 0, 178913973926, 469624753272, 229498824405, 13772981906, 0, 0] := by
  decide +kernel

theorem rows2137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2137 = true := by
  decide +kernel

theorem tot2137 : totK PD2M8K2 D2M8K2.t2137 = [0, 0, 184297217625, 475508521363, 213035684517, 7870241454, 0, 0] := by
  decide +kernel

theorem rows2138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2138 = true := by
  decide +kernel

theorem tot2138 : totK PD2M8K2 D2M8K2.t2138 = [0, 93964257987, 302005420123, 365396850037, 147633823061, 13468148062, 0, 0] := by
  decide +kernel

theorem rows2139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2139 = true := by
  decide +kernel

theorem tot2139 : totK PD2M8K2 D2M8K2.t2139 = [0, 174063212179, 449716742537, 248749480899, 21103394462, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
