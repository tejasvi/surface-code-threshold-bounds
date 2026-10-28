import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12824 = true := by
  decide +kernel

theorem tot12824 : totK PD2M8K2 D2M8K2.t12824 = [0, 192741264048, 458739160603, 227043490710, 17115888737, 0, 0, 0] := by
  decide +kernel

theorem rows12825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12825 = true := by
  decide +kernel

theorem tot12825 : totK PD2M8K2 D2M8K2.t12825 = [0, 43574399416, 331422890415, 419346174567, 86112046408, 1369150432, 0, 0] := by
  decide +kernel

theorem rows12826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12826 = true := by
  decide +kernel

theorem tot12826 : totK PD2M8K2 D2M8K2.t12826 = [0, 93537328149, 393199780281, 397005544979, 46462177920, 0, 0, 0] := by
  decide +kernel

theorem rows12827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12827 = true := by
  decide +kernel

theorem tot12827 : totK PD2M8K2 D2M8K2.t12827 = [0, 174650386013, 448577479814, 255011551741, 22776814218, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
