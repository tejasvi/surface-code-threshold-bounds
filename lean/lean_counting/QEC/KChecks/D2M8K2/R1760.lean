import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7040 = true := by
  decide +kernel

theorem tot7040 : totK PD2M8K2 D2M8K2.t7040 = [0, 0, 0, 301765193529, 473101248925, 82609423381, 1054738420, 0] := by
  decide +kernel

theorem rows7041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7041 = true := by
  decide +kernel

theorem tot7041 : totK PD2M8K2 D2M8K2.t7041 = [0, 0, 82469601113, 332786015182, 343595903472, 85589124736, 3732315745, 0] := by
  decide +kernel

theorem rows7042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7042 = true := by
  decide +kernel

theorem tot7042 : totK PD2M8K2 D2M8K2.t7042 = [0, 0, 176102721579, 463980030045, 234812532148, 16629160294, 0, 0] := by
  decide +kernel

theorem rows7043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7043 = true := by
  decide +kernel

theorem tot7043 : totK PD2M8K2 D2M8K2.t7043 = [0, 0, 138969820468, 434736840495, 278879720039, 20961688742, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
