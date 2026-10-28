import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10636 = true := by
  decide +kernel

theorem tot10636 : totK PD2M8K2 D2M8K2.t10636 = [0, 36923124222, 213271964408, 429856446521, 214333417904, 7957747042, 0, 0] := by
  decide +kernel

theorem rows10637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10637 = true := by
  decide +kernel

theorem tot10637 : totK PD2M8K2 D2M8K2.t10637 = [0, 181693055532, 445138393108, 247235068319, 22791680701, 0, 0, 0] := by
  decide +kernel

theorem rows10638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10638 = true := by
  decide +kernel

theorem tot10638 : totK PD2M8K2 D2M8K2.t10638 = [0, 178747526861, 478551336483, 223420300806, 12373752831, 0, 0, 0] := by
  decide +kernel

theorem rows10639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10639 = true := by
  decide +kernel

theorem tot10639 : totK PD2M8K2 D2M8K2.t10639 = [0, 0, 282189376318, 496523140760, 98523059360, 1164319620, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
