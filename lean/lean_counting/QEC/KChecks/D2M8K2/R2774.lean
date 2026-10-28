import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11096 = true := by
  decide +kernel

theorem tot11096 : totK PD2M8K2 D2M8K2.t11096 = [0, 0, 288940050121, 503442484903, 80328485691, 1310285577, 0, 0] := by
  decide +kernel

theorem rows11097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11097 = true := by
  decide +kernel

theorem tot11097 : totK PD2M8K2 D2M8K2.t11097 = [0, 171648112585, 437998665659, 263868768477, 29479654785, 0, 0, 0] := by
  decide +kernel

theorem rows11098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11098 = true := by
  decide +kernel

theorem tot11098 : totK PD2M8K2 D2M8K2.t11098 = [0, 193941082821, 467261863512, 209363787702, 12032668289, 0, 0, 0] := by
  decide +kernel

theorem rows11099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11099 = true := by
  decide +kernel

theorem tot11099 : totK PD2M8K2 D2M8K2.t11099 = [0, 34089752144, 326797569790, 448735358632, 74718844074, 1075657031, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
