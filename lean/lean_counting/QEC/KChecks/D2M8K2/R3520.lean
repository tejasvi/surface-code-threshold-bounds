import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14080 = true := by
  decide +kernel

theorem tot14080 : totK PD2M8K2 D2M8K2.t14080 = [0, 0, 161246247974, 479630411946, 245935903743, 12363726046, 0, 0] := by
  decide +kernel

theorem rows14081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14081 = true := by
  decide +kernel

theorem tot14081 : totK PD2M8K2 D2M8K2.t14081 = [0, 0, 188685811601, 471663672196, 219740557617, 12443528988, 0, 0] := by
  decide +kernel

theorem rows14082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14082 = true := by
  decide +kernel

theorem tot14082 : totK PD2M8K2 D2M8K2.t14082 = [0, 0, 204222259587, 494889319652, 195577251596, 10110453329, 0, 0] := by
  decide +kernel

theorem rows14083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14083 = true := by
  decide +kernel

theorem tot14083 : totK PD2M8K2 D2M8K2.t14083 = [0, 0, 171500360709, 442098458301, 244464050563, 16433856951, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
