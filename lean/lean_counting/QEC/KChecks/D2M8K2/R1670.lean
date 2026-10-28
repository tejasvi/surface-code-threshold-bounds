import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6680 = true := by
  decide +kernel

theorem tot6680 : totK PD2M8K2 D2M8K2.t6680 = [0, 92473523498, 376660755143, 398666176517, 44035805419, 0, 0, 0] := by
  decide +kernel

theorem rows6681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6681 = true := by
  decide +kernel

theorem tot6681 : totK PD2M8K2 D2M8K2.t6681 = [0, 157452722597, 447478365131, 291066700938, 28252641472, 0, 0, 0] := by
  decide +kernel

theorem rows6682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6682 = true := by
  decide +kernel

theorem tot6682 : totK PD2M8K2 D2M8K2.t6682 = [0, 156753643563, 454913920807, 271617357646, 21630889883, 0, 0, 0] := by
  decide +kernel

theorem rows6683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6683 = true := by
  decide +kernel

theorem tot6683 : totK PD2M8K2 D2M8K2.t6683 = [0, 0, 244950359355, 498186315089, 171764643840, 9654694938, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
