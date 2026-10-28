import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15036 = true := by
  decide +kernel

theorem tot15036 : totK PD2M8K2 D2M8K2.t15036 = [0, 137652961692, 348891976287, 293789274135, 114904439866, 6804944647, 0, 0] := by
  decide +kernel

theorem rows15037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15037 = true := by
  decide +kernel

theorem tot15037 : totK PD2M8K2 D2M8K2.t15037 = [0, 161254466261, 438402545716, 276212138996, 29851081663, 0, 0, 0] := by
  decide +kernel

theorem rows15038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15038 = true := by
  decide +kernel

theorem tot15038 : totK PD2M8K2 D2M8K2.t15038 = [0, 122531782185, 434262270170, 318445020327, 25734061195, 0, 0, 0] := by
  decide +kernel

theorem rows15039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15039 = true := by
  decide +kernel

theorem tot15039 : totK PD2M8K2 D2M8K2.t15039 = [0, 0, 212597395193, 484235970753, 173178661339, 7611474319, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
