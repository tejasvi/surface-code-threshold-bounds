import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10388 = true := by
  decide +kernel

theorem tot10388 : totK PD2M8K2 D2M8K2.t10388 = [0, 0, 0, 203147928185, 485563922231, 177559008682, 10086186284, 0] := by
  decide +kernel

theorem rows10389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10389 = true := by
  decide +kernel

theorem tot10389 : totK PD2M8K2 D2M8K2.t10389 = [0, 0, 0, 195343719241, 459890458479, 192087339019, 12109972807, 0] := by
  decide +kernel

theorem rows10390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10390 = true := by
  decide +kernel

theorem tot10390 : totK PD2M8K2 D2M8K2.t10390 = [0, 0, 0, 30092709635, 351015564626, 397096776843, 70837697126, 1310517177] := by
  decide +kernel

theorem rows10391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10391 = true := by
  decide +kernel

theorem tot10391 : totK PD2M8K2 D2M8K2.t10391 = [0, 0, 0, 85178250718, 411155472769, 309789774358, 32582388804, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
