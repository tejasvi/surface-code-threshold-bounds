import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9440 = true := by
  decide +kernel

theorem tot9440 : totK PD2M8K2 D2M8K2.t9440 = [193788386382, 487234169330, 206784139343, 9852138406, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9441 = true := by
  decide +kernel

theorem tot9441 : totK PD2M8K2 D2M8K2.t9441 = [197518268422, 466872813701, 213388396292, 12534051746, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9442 = true := by
  decide +kernel

theorem tot9442 : totK PD2M8K2 D2M8K2.t9442 = [19434252169, 306972769009, 464522059529, 101512626863, 1369150432, 0, 0, 0] := by
  decide +kernel

theorem rows9443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9443 = true := by
  decide +kernel

theorem tot9443 : totK PD2M8K2 D2M8K2.t9443 = [74831621714, 358838481482, 419657189454, 54936197638, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
