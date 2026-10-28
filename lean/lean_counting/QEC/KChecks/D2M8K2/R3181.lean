import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12724 = true := by
  decide +kernel

theorem tot12724 : totK PD2M8K2 D2M8K2.t12724 = [0, 182755202180, 462500846180, 260656445971, 24549257228, 0, 0, 0] := by
  decide +kernel

theorem rows12725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12725 = true := by
  decide +kernel

theorem tot12725 : totK PD2M8K2 D2M8K2.t12725 = [0, 171733395207, 473810621566, 234953002507, 12321710050, 0, 0, 0] := by
  decide +kernel

theorem rows12726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12726 = true := by
  decide +kernel

theorem tot12726 : totK PD2M8K2 D2M8K2.t12726 = [0, 0, 283935760882, 515377009282, 103566501258, 0, 0, 0] := by
  decide +kernel

theorem rows12727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12727 = true := by
  decide +kernel

theorem tot12727 : totK PD2M8K2 D2M8K2.t12727 = [0, 31608431453, 202770021947, 433757117151, 186318747703, 12003981235, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
