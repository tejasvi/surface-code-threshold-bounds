import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15476 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15476 = true := by
  decide +kernel

theorem tot15476 : totK PD2M8K2 D2M8K2.t15476 = [0, 0, 245173467647, 493854878197, 156679130457, 8200189783, 0, 0] := by
  decide +kernel

theorem rows15477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15477 = true := by
  decide +kernel

theorem tot15477 : totK PD2M8K2 D2M8K2.t15477 = [0, 133759602454, 375651504822, 311688334829, 77486641299, 2263379853, 0, 0] := by
  decide +kernel

theorem rows15478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15478 = true := by
  decide +kernel

theorem tot15478 : totK PD2M8K2 D2M8K2.t15478 = [0, 167681261547, 437082087563, 280592669414, 30419930744, 0, 0, 0] := by
  decide +kernel

theorem rows15479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15479 = true := by
  decide +kernel

theorem tot15479 : totK PD2M8K2 D2M8K2.t15479 = [0, 106277543241, 420434876474, 339077438343, 36032491128, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
