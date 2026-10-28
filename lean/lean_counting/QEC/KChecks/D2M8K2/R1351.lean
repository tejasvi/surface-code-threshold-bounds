import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5404 = true := by
  decide +kernel

theorem tot5404 : totK PD2M8K2 D2M8K2.t5404 = [0, 0, 0, 209517643599, 485436783431, 179217361685, 6656488309, 0] := by
  decide +kernel

theorem rows5405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5405 = true := by
  decide +kernel

theorem tot5405 : totK PD2M8K2 D2M8K2.t5405 = [0, 0, 173220819551, 442224118960, 279531589699, 34641945991, 0, 0] := by
  decide +kernel

theorem rows5406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5406 = true := by
  decide +kernel

theorem tot5406 : totK PD2M8K2 D2M8K2.t5406 = [0, 0, 171128825911, 486822877090, 240486734999, 20285660382, 0, 0] := by
  decide +kernel

theorem rows5407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5407 = true := by
  decide +kernel

theorem tot5407 : totK PD2M8K2 D2M8K2.t5407 = [0, 0, 0, 303049312586, 527775439420, 84747099322, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
