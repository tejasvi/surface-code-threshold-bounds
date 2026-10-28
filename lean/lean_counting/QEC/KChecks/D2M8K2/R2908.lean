import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11632 = true := by
  decide +kernel

theorem tot11632 : totK PD2M8K2 D2M8K2.t11632 = [0, 271406022921, 504652244435, 111858466485, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows11633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11633 = true := by
  decide +kernel

theorem tot11633 : totK PD2M8K2 D2M8K2.t11633 = [153805469543, 413618566547, 320793045156, 41676841362, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11634 = true := by
  decide +kernel

theorem tot11634 : totK PD2M8K2 D2M8K2.t11634 = [179738808188, 470788935891, 234385662240, 15508862681, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11635 = true := by
  decide +kernel

theorem tot11635 : totK PD2M8K2 D2M8K2.t11635 = [86211245440, 383036839491, 353867071103, 74883492726, 8415650999, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
