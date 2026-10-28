import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13284 = true := by
  decide +kernel

theorem tot13284 : totK PD2M8K2 D2M8K2.t13284 = [0, 0, 188251728806, 502558173742, 218255619904, 7674465901, 0, 0] := by
  decide +kernel

theorem rows13285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13285 = true := by
  decide +kernel

theorem tot13285 : totK PD2M8K2 D2M8K2.t13285 = [0, 178256666961, 435531548838, 217077595849, 64282559178, 6427737504, 0, 0] := by
  decide +kernel

theorem rows13286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13286 = true := by
  decide +kernel

theorem tot13286 : totK PD2M8K2 D2M8K2.t13286 = [0, 194663736069, 453804152263, 216093502344, 14001064343, 0, 0, 0] := by
  decide +kernel

theorem rows13287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13287 = true := by
  decide +kernel

theorem tot13287 : totK PD2M8K2 D2M8K2.t13287 = [0, 33672053050, 303013033820, 438696606910, 97443532424, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
