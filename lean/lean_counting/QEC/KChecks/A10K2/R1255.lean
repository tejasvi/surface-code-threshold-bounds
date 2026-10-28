import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5020 = true := by
  decide +kernel

theorem tot5020 : totK PA10K2 A10K2.t5020 = [0, 461607179050, 1614106439225, 1805775947548, 812917966158, 167172683729, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows5021 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5021 = true := by
  decide +kernel

theorem tot5021 : totK PA10K2 A10K2.t5021 = [0, 174514764450, 913657882279, 2004252170946, 1567030567559, 296746088838, 6962742351, 0, 0, 0] := by
  decide +kernel

theorem rows5022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5022 = true := by
  decide +kernel

theorem tot5022 : totK PA10K2 A10K2.t5022 = [0, 443112635974, 1758395194472, 1959253659621, 551004414828, 32040661968, 0, 0, 0, 0] := by
  decide +kernel

theorem rows5023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t5023 = true := by
  decide +kernel

theorem tot5023 : totK PA10K2 A10K2.t5023 = [0, 124055991748, 952169025340, 1934095992656, 1321829887868, 298725765898, 24614390653, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
