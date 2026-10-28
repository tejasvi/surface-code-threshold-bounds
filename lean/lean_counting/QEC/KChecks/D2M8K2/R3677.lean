import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14708 = true := by
  decide +kernel

theorem tot14708 : totK PD2M8K2 D2M8K2.t14708 = [0, 0, 178467773161, 469936947818, 230148380727, 13673275291, 0, 0] := by
  decide +kernel

theorem rows14709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14709 = true := by
  decide +kernel

theorem tot14709 : totK PD2M8K2 D2M8K2.t14709 = [0, 0, 0, 306823769765, 438048411853, 76351512040, 1095107716, 0] := by
  decide +kernel

theorem rows14710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14710 = true := by
  decide +kernel

theorem tot14710 : totK PD2M8K2 D2M8K2.t14710 = [0, 137762673120, 292871221722, 163932025236, 202682275374, 76590533551, 3819176523, 0] := by
  decide +kernel

theorem rows14711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14711 = true := by
  decide +kernel

theorem tot14711 : totK PD2M8K2 D2M8K2.t14711 = [0, 180908228213, 464794824374, 221216588124, 12637928123, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
