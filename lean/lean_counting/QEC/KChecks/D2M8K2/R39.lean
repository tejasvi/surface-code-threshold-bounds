import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t156 = true := by
  decide +kernel

theorem tot156 : totK PD2M8K2 D2M8K2.t156 = [0, 195721509789, 489919758288, 197824842192, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t157 = true := by
  decide +kernel

theorem tot157 : totK PD2M8K2 D2M8K2.t157 = [0, 176266447934, 466928731458, 233121137834, 14631128802, 0, 0, 0] := by
  decide +kernel

theorem rows158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t158 = true := by
  decide +kernel

theorem tot158 : totK PD2M8K2 D2M8K2.t158 = [0, 184829948231, 477197442091, 208397676356, 7913321096, 0, 0, 0] := by
  decide +kernel

theorem rows159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t159 = true := by
  decide +kernel

theorem tot159 : totK PD2M8K2 D2M8K2.t159 = [0, 55661912469, 333477558031, 416255405900, 79594944865, 1310285577, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
