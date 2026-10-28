import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15020 = true := by
  decide +kernel

theorem tot15020 : totK PD2M8K2 D2M8K2.t15020 = [0, 0, 237679279289, 472733156020, 183431055854, 10597857724, 0, 0] := by
  decide +kernel

theorem rows15021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15021 = true := by
  decide +kernel

theorem tot15021 : totK PD2M8K2 D2M8K2.t15021 = [0, 0, 190066178369, 487174696226, 218964259669, 11380923020, 0, 0] := by
  decide +kernel

theorem rows15022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15022 = true := by
  decide +kernel

theorem tot15022 : totK PD2M8K2 D2M8K2.t15022 = [0, 0, 166524922457, 450910045672, 242041597355, 13174244095, 0, 0] := by
  decide +kernel

theorem rows15023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15023 = true := by
  decide +kernel

theorem tot15023 : totK PD2M8K2 D2M8K2.t15023 = [0, 0, 0, 281383396963, 479250269943, 93697162865, 1135526696, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
