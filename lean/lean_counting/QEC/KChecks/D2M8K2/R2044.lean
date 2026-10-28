import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8176 = true := by
  decide +kernel

theorem tot8176 : totK PD2M8K2 D2M8K2.t8176 = [0, 0, 172179909266, 456618642161, 249597711197, 26258679262, 0, 0] := by
  decide +kernel

theorem rows8177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8177 = true := by
  decide +kernel

theorem tot8177 : totK PD2M8K2 D2M8K2.t8177 = [0, 0, 160609534383, 454545890965, 273700500966, 17643368064, 0, 0] := by
  decide +kernel

theorem rows8178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8178 = true := by
  decide +kernel

theorem tot8178 : totK PD2M8K2 D2M8K2.t8178 = [0, 98160669442, 326055332408, 326073209186, 147423702111, 13566916688, 0, 0] := by
  decide +kernel

theorem rows8179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8179 = true := by
  decide +kernel

theorem tot8179 : totK PD2M8K2 D2M8K2.t8179 = [0, 176846130152, 458830813598, 232639715968, 15244488776, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
