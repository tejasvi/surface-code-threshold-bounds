import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4324 = true := by
  decide +kernel

theorem tot4324 : totK PD2M8K2 D2M8K2.t4324 = [0, 0, 0, 197420335906, 493272146104, 206804656032, 9087086961, 0] := by
  decide +kernel

theorem rows4325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4325 = true := by
  decide +kernel

theorem tot4325 : totK PD2M8K2 D2M8K2.t4325 = [0, 0, 0, 163289276100, 457572964393, 244785388718, 16642304715, 0] := by
  decide +kernel

theorem rows4326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4326 = true := by
  decide +kernel

theorem tot4326 : totK PD2M8K2 D2M8K2.t4326 = [0, 0, 0, 192515669701, 471873247246, 218336432471, 9456084904, 0] := by
  decide +kernel

theorem rows4327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4327 = true := by
  decide +kernel

theorem tot4327 : totK PD2M8K2 D2M8K2.t4327 = [0, 0, 0, 218916975889, 499576840061, 169337798122, 6802056411, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
