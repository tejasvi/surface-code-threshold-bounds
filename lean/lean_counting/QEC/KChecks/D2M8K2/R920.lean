import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3680 = true := by
  decide +kernel

theorem tot3680 : totK PD2M8K2 D2M8K2.t3680 = [0, 0, 0, 319269608294, 429016907649, 73466442487, 1138244013, 0] := by
  decide +kernel

theorem rows3681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3681 = true := by
  decide +kernel

theorem tot3681 : totK PD2M8K2 D2M8K2.t3681 = [0, 0, 161520073018, 426923599558, 269599486078, 29780046611, 0, 0] := by
  decide +kernel

theorem rows3682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3682 = true := by
  decide +kernel

theorem tot3682 : totK PD2M8K2 D2M8K2.t3682 = [0, 0, 189072048694, 492276453338, 197645854586, 10035653310, 0, 0] := by
  decide +kernel

theorem rows3683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3683 = true := by
  decide +kernel

theorem tot3683 : totK PD2M8K2 D2M8K2.t3683 = [0, 0, 235733568723, 487650008948, 151192410596, 2954213869, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
