import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5840 = true := by
  decide +kernel

theorem tot5840 : totK PD2M8K2 D2M8K2.t5840 = [0, 197009132114, 465623107104, 210435445798, 12267505601, 0, 0, 0] := by
  decide +kernel

theorem rows5841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5841 = true := by
  decide +kernel

theorem tot5841 : totK PD2M8K2 D2M8K2.t5841 = [0, 23162532892, 315853124753, 447256637814, 83898359918, 1206465782, 0, 0] := by
  decide +kernel

theorem rows5842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5842 = true := by
  decide +kernel

theorem tot5842 : totK PD2M8K2 D2M8K2.t5842 = [0, 107795697168, 398060258646, 364135995420, 40973796253, 0, 0, 0] := by
  decide +kernel

theorem rows5843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5843 = true := by
  decide +kernel

theorem tot5843 : totK PD2M8K2 D2M8K2.t5843 = [0, 204218281583, 483994733183, 214375180840, 11405872210, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
