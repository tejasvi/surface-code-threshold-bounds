import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2020 = true := by
  decide +kernel

theorem tot2020 : totK PD2M8K2 D2M8K2.t2020 = [0, 145772694100, 444536082377, 300921596267, 26397140704, 0, 0, 0] := by
  decide +kernel

theorem rows2021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2021 = true := by
  decide +kernel

theorem tot2021 : totK PD2M8K2 D2M8K2.t2021 = [0, 0, 224548355834, 494560437396, 153652601376, 2303467656, 0, 0] := by
  decide +kernel

theorem rows2022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2022 = true := by
  decide +kernel

theorem tot2022 : totK PD2M8K2 D2M8K2.t2022 = [0, 0, 191918659405, 464310723139, 219197428842, 15262856049, 0, 0] := by
  decide +kernel

theorem rows2023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2023 = true := by
  decide +kernel

theorem tot2023 : totK PD2M8K2 D2M8K2.t2023 = [0, 0, 209477287366, 505294428118, 172655623332, 2519015093, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
