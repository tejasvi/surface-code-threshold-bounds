import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11724 = true := by
  decide +kernel

theorem tot11724 : totK PD2M8K2 D2M8K2.t11724 = [0, 107081524770, 413976868716, 334693977676, 31878142677, 0, 0, 0] := by
  decide +kernel

theorem rows11725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11725 = true := by
  decide +kernel

theorem tot11725 : totK PD2M8K2 D2M8K2.t11725 = [0, 0, 257008772206, 468013604558, 130596824439, 4879840392, 0, 0] := by
  decide +kernel

theorem rows11726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11726 = true := by
  decide +kernel

theorem tot11726 : totK PD2M8K2 D2M8K2.t11726 = [0, 172647945751, 446118191098, 255226023169, 31079752632, 0, 0, 0] := by
  decide +kernel

theorem rows11727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11727 = true := by
  decide +kernel

theorem tot11727 : totK PD2M8K2 D2M8K2.t11727 = [0, 160666605225, 451894547130, 276211496093, 16329115559, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
