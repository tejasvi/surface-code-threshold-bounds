import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5120 = true := by
  decide +kernel

theorem tot5120 : totK PD2M8K2 D2M8K2.t5120 = [0, 0, 176152732542, 444883213452, 271445429067, 25724595562, 0, 0] := by
  decide +kernel

theorem rows5121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5121 = true := by
  decide +kernel

theorem tot5121 : totK PD2M8K2 D2M8K2.t5121 = [0, 0, 173925717690, 486837045914, 253400507178, 10140659148, 0, 0] := by
  decide +kernel

theorem rows5122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5122 = true := by
  decide +kernel

theorem tot5122 : totK PD2M8K2 D2M8K2.t5122 = [0, 0, 0, 218063747067, 464015343331, 209202498723, 21400436502, 0] := by
  decide +kernel

theorem rows5123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5123 = true := by
  decide +kernel

theorem tot5123 : totK PD2M8K2 D2M8K2.t5123 = [0, 0, 0, 175439101909, 493685223821, 220156732168, 7994456143, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
