import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13956 = true := by
  decide +kernel

theorem tot13956 : totK PD2M8K2 D2M8K2.t13956 = [0, 0, 180635191996, 509715802449, 210039431380, 5430665091, 0, 0] := by
  decide +kernel

theorem rows13957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13957 = true := by
  decide +kernel

theorem tot13957 : totK PD2M8K2 D2M8K2.t13957 = [0, 159862974851, 402462667149, 253767493426, 87845578655, 6804944647, 0, 0] := by
  decide +kernel

theorem rows13958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13958 = true := by
  decide +kernel

theorem tot13958 : totK PD2M8K2 D2M8K2.t13958 = [0, 188649201026, 466724131499, 217054249162, 12160257916, 0, 0, 0] := by
  decide +kernel

theorem rows13959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13959 = true := by
  decide +kernel

theorem tot13959 : totK PD2M8K2 D2M8K2.t13959 = [0, 71594238069, 348454832679, 411403266856, 73299981841, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
