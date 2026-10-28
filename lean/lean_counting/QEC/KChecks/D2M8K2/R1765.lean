import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7060 = true := by
  decide +kernel

theorem tot7060 : totK PD2M8K2 D2M8K2.t7060 = [0, 0, 201019355927, 480666871834, 177259351179, 9668735432, 0, 0] := by
  decide +kernel

theorem rows7061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7061 = true := by
  decide +kernel

theorem tot7061 : totK PD2M8K2 D2M8K2.t7061 = [0, 87770539582, 315244149627, 375915187078, 95262728171, 3581949829, 0, 0] := by
  decide +kernel

theorem rows7062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7062 = true := by
  decide +kernel

theorem tot7062 : totK PD2M8K2 D2M8K2.t7062 = [0, 151725520883, 442653628003, 262176708524, 22620860668, 0, 0, 0] := by
  decide +kernel

theorem rows7063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7063 = true := by
  decide +kernel

theorem tot7063 : totK PD2M8K2 D2M8K2.t7063 = [0, 174721482019, 463214948521, 234390304834, 13916467904, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
