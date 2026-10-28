import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t180 = true := by
  decide +kernel

theorem tot180 : totK PD2M8K2 D2M8K2.t180 = [0, 137287924046, 439786735588, 290218888242, 23777527448, 0, 0, 0] := by
  decide +kernel

theorem rows181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t181 = true := by
  decide +kernel

theorem tot181 : totK PD2M8K2 D2M8K2.t181 = [0, 0, 208958015627, 488163865662, 163375352409, 9467973755, 0, 0] := by
  decide +kernel

theorem rows182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t182 = true := by
  decide +kernel

theorem tot182 : totK PD2M8K2 D2M8K2.t182 = [0, 87978670910, 323893970575, 375738263528, 86615658092, 3423684254, 0, 0] := by
  decide +kernel

theorem rows183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t183 = true := by
  decide +kernel

theorem tot183 : totK PD2M8K2 D2M8K2.t183 = [0, 159156753757, 459950228281, 268018953550, 18682401836, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
