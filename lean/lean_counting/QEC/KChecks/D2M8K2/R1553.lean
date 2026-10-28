import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6212 = true := by
  decide +kernel

theorem tot6212 : totK PD2M8K2 D2M8K2.t6212 = [165557862225, 449605740771, 279840349900, 30127456144, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6213 = true := by
  decide +kernel

theorem tot6213 : totK PD2M8K2 D2M8K2.t6213 = [92616578666, 389467057527, 360279991833, 56834662025, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows6214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6214 = true := by
  decide +kernel

theorem tot6214 : totK PD2M8K2 D2M8K2.t6214 = [0, 229553002147, 498085118649, 159585360673, 3699256714, 0, 0, 0] := by
  decide +kernel

theorem rows6215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6215 = true := by
  decide +kernel

theorem tot6215 : totK PD2M8K2 D2M8K2.t6215 = [0, 193435241928, 463265451455, 212353198785, 16893639594, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
