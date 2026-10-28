import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3768 = true := by
  decide +kernel

theorem tot3768 : totK PD2M8K2 D2M8K2.t3768 = [71577605977, 335464074657, 408561374175, 88386130154, 1164319620, 0, 0, 0] := by
  decide +kernel

theorem rows3769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3769 = true := by
  decide +kernel

theorem tot3769 : totK PD2M8K2 D2M8K2.t3769 = [0, 213159543311, 486138788605, 170603557100, 9404247146, 0, 0, 0] := by
  decide +kernel

theorem rows3770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3770 = true := by
  decide +kernel

theorem tot3770 : totK PD2M8K2 D2M8K2.t3770 = [152520434204, 421812802050, 280022592562, 58034789228, 2481160468, 0, 0, 0] := by
  decide +kernel

theorem rows3771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3771 = true := by
  decide +kernel

theorem tot3771 : totK PD2M8K2 D2M8K2.t3771 = [174688021177, 446457524086, 266902765325, 21004720169, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
