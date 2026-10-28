import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2056 = true := by
  decide +kernel

theorem tot2056 : totK PD2M8K2 D2M8K2.t2056 = [0, 92722817510, 389412305057, 356314267715, 57093393945, 1096505104, 0, 0] := by
  decide +kernel

theorem rows2057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2057 = true := by
  decide +kernel

theorem tot2057 : totK PD2M8K2 D2M8K2.t2057 = [0, 0, 320429010557, 511992635023, 81958549225, 0, 0, 0] := by
  decide +kernel

theorem rows2058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2058 = true := by
  decide +kernel

theorem tot2058 : totK PD2M8K2 D2M8K2.t2058 = [0, 0, 193000942461, 497431710210, 184840974955, 5253830308, 0, 0] := by
  decide +kernel

theorem rows2059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2059 = true := by
  decide +kernel

theorem tot2059 : totK PD2M8K2 D2M8K2.t2059 = [0, 0, 173191321074, 447272481831, 230144569932, 17973025655, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
