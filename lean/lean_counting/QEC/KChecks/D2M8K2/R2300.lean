import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9200 = true := by
  decide +kernel

theorem tot9200 : totK PD2M8K2 D2M8K2.t9200 = [123749881987, 327197757585, 359648066440, 110555239492, 3880716147, 0, 0, 0] := by
  decide +kernel

theorem rows9201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9201 = true := by
  decide +kernel

theorem tot9201 : totK PD2M8K2 D2M8K2.t9201 = [205117391890, 475694560851, 218502274330, 15361233756, 0, 0, 0, 0] := by
  decide +kernel

theorem rows9202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9202 = true := by
  decide +kernel

theorem tot9202 : totK PD2M8K2 D2M8K2.t9202 = [4200607152, 300984532694, 486728833545, 117286735148, 2592220497, 0, 0, 0] := by
  decide +kernel

theorem rows9203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9203 = true := by
  decide +kernel

theorem tot9203 : totK PD2M8K2 D2M8K2.t9203 = [0, 197301268606, 466884518817, 217344454866, 16915366700, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
