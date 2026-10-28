import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15840 = true := by
  decide +kernel

theorem tot15840 : totK PD2M8K2 D2M8K2.t15840 = [0, 0, 182507398429, 450738244776, 272968685748, 28690462113, 0, 0] := by
  decide +kernel

theorem rows15841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15841 = true := by
  decide +kernel

theorem tot15841 : totK PD2M8K2 D2M8K2.t15841 = [0, 0, 170966567726, 456978844255, 247724345977, 16955635238, 0, 0] := by
  decide +kernel

theorem rows15842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15842 = true := by
  decide +kernel

theorem tot15842 : totK PD2M8K2 D2M8K2.t15842 = [0, 0, 0, 275115951270, 481679278233, 127974289433, 4031931762, 0] := by
  decide +kernel

theorem rows15843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15843 = true := by
  decide +kernel

theorem tot15843 : totK PD2M8K2 D2M8K2.t15843 = [0, 0, 109701948906, 349826950687, 343757915029, 75189226161, 1186940923, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
