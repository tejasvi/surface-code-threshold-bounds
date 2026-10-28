import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9408 = true := by
  decide +kernel

theorem tot9408 : totK PD2M8K2 D2M8K2.t9408 = [0, 89929757808, 385527506426, 330578972459, 55083657519, 1326647619, 0, 0] := by
  decide +kernel

theorem rows9409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9409 = true := by
  decide +kernel

theorem tot9409 : totK PD2M8K2 D2M8K2.t9409 = [0, 0, 301972024334, 502911703998, 71586580351, 0, 0, 0] := by
  decide +kernel

theorem rows9410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9410 = true := by
  decide +kernel

theorem tot9410 : totK PD2M8K2 D2M8K2.t9410 = [0, 178053511748, 438836396291, 271808464169, 27204099255, 0, 0, 0] := by
  decide +kernel

theorem rows9411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9411 = true := by
  decide +kernel

theorem tot9411 : totK PD2M8K2 D2M8K2.t9411 = [0, 175727005596, 475020400705, 234447889446, 15700860799, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
