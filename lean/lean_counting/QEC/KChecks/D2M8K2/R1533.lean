import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6132 = true := by
  decide +kernel

theorem tot6132 : totK PD2M8K2 D2M8K2.t6132 = [138985563802, 439631297095, 291385013587, 21335924603, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6133 = true := by
  decide +kernel

theorem tot6133 : totK PD2M8K2 D2M8K2.t6133 = [0, 186109382791, 466944516599, 189969608609, 10680993762, 0, 0, 0] := by
  decide +kernel

theorem rows6134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6134 = true := by
  decide +kernel

theorem tot6134 : totK PD2M8K2 D2M8K2.t6134 = [155200294621, 392347907328, 282701812087, 62712632585, 2569691499, 0, 0, 0] := by
  decide +kernel

theorem rows6135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6135 = true := by
  decide +kernel

theorem tot6135 : totK PD2M8K2 D2M8K2.t6135 = [162499566603, 442093395143, 258266054937, 26927685455, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
