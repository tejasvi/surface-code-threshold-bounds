import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15084 = true := by
  decide +kernel

theorem tot15084 : totK PD2M8K2 D2M8K2.t15084 = [0, 107971457226, 427868950273, 348850944116, 30508105564, 0, 0, 0] := by
  decide +kernel

theorem rows15085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15085 = true := by
  decide +kernel

theorem tot15085 : totK PD2M8K2 D2M8K2.t15085 = [0, 0, 201387240308, 491333210240, 182068180907, 4967996017, 0, 0] := by
  decide +kernel

theorem rows15086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15086 = true := by
  decide +kernel

theorem tot15086 : totK PD2M8K2 D2M8K2.t15086 = [0, 0, 199160657282, 457641242572, 216548043994, 17080783126, 0, 0] := by
  decide +kernel

theorem rows15087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15087 = true := by
  decide +kernel

theorem tot15087 : totK PD2M8K2 D2M8K2.t15087 = [0, 0, 192921405704, 487591022029, 199161083511, 9610913563, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
