import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13212 = true := by
  decide +kernel

theorem tot13212 : totK PD2M8K2 D2M8K2.t13212 = [0, 0, 81950250438, 359293591420, 376936911620, 66281462295, 1107157161, 0] := by
  decide +kernel

theorem rows13213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13213 = true := by
  decide +kernel

theorem tot13213 : totK PD2M8K2 D2M8K2.t13213 = [0, 0, 24878004333, 306063565136, 438892912943, 105837550293, 3824247485, 0] := by
  decide +kernel

theorem rows13214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13214 = true := by
  decide +kernel

theorem tot13214 : totK PD2M8K2 D2M8K2.t13214 = [0, 0, 178711947894, 460186782540, 239873905556, 19170520137, 0, 0] := by
  decide +kernel

theorem rows13215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13215 = true := by
  decide +kernel

theorem tot13215 : totK PD2M8K2 D2M8K2.t13215 = [0, 0, 206920606899, 481922137511, 215551034534, 10479590111, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
