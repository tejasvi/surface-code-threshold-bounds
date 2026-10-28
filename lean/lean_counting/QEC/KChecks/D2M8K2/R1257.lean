import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5028 = true := by
  decide +kernel

theorem tot5028 : totK PD2M8K2 D2M8K2.t5028 = [0, 0, 83296233045, 353470276865, 358012309332, 71479951759, 1162935789, 0] := by
  decide +kernel

theorem rows5029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5029 = true := by
  decide +kernel

theorem tot5029 : totK PD2M8K2 D2M8K2.t5029 = [0, 0, 0, 241972118822, 467693376777, 152375143770, 9389920916, 0] := by
  decide +kernel

theorem rows5030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5030 = true := by
  decide +kernel

theorem tot5030 : totK PD2M8K2 D2M8K2.t5030 = [0, 0, 154680704036, 387780950728, 262030728293, 58823897485, 2463340669, 0] := by
  decide +kernel

theorem rows5031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5031 = true := by
  decide +kernel

theorem tot5031 : totK PD2M8K2 D2M8K2.t5031 = [0, 0, 173833904659, 470100693402, 247099169476, 18252358503, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
