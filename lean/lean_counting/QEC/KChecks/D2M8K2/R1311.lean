import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5244 = true := by
  decide +kernel

theorem tot5244 : totK PD2M8K2 D2M8K2.t5244 = [0, 171131259913, 439717938527, 276936439821, 30590613803, 0, 0, 0] := by
  decide +kernel

theorem rows5245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5245 = true := by
  decide +kernel

theorem tot5245 : totK PD2M8K2 D2M8K2.t5245 = [0, 87922896509, 365390234692, 366014468956, 69816634516, 1197396724, 0, 0] := by
  decide +kernel

theorem rows5246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5246 = true := by
  decide +kernel

theorem tot5246 : totK PD2M8K2 D2M8K2.t5246 = [0, 0, 255394905019, 493038404977, 152433820358, 8242271503, 0, 0] := by
  decide +kernel

theorem rows5247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5247 = true := by
  decide +kernel

theorem tot5247 : totK PD2M8K2 D2M8K2.t5247 = [0, 103410131108, 335813647552, 377742221404, 101547802048, 2332971745, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
