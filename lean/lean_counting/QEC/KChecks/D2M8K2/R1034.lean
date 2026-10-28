import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4136 = true := by
  decide +kernel

theorem tot4136 : totK PD2M8K2 D2M8K2.t4136 = [0, 131749273644, 444321780249, 303343682298, 22484654116, 0, 0, 0] := by
  decide +kernel

theorem rows4137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4137 = true := by
  decide +kernel

theorem tot4137 : totK PD2M8K2 D2M8K2.t4137 = [0, 0, 213884088338, 491408388667, 176024283471, 9587713104, 0, 0] := by
  decide +kernel

theorem rows4138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4138 = true := by
  decide +kernel

theorem tot4138 : totK PD2M8K2 D2M8K2.t4138 = [0, 95383810356, 332903438820, 357330690001, 92612884297, 3462014130, 0, 0] := by
  decide +kernel

theorem rows4139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4139 = true := by
  decide +kernel

theorem tot4139 : totK PD2M8K2 D2M8K2.t4139 = [0, 160655174269, 443909319831, 282274618446, 30508507079, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
