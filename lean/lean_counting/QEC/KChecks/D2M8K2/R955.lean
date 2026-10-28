import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3820 = true := by
  decide +kernel

theorem tot3820 : totK PD2M8K2 D2M8K2.t3820 = [0, 88698579362, 376860256565, 349424381698, 54451245849, 1171084559, 0, 0] := by
  decide +kernel

theorem rows3821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3821 = true := by
  decide +kernel

theorem tot3821 : totK PD2M8K2 D2M8K2.t3821 = [0, 0, 238236548198, 475271163461, 157297811382, 8462178015, 0, 0] := by
  decide +kernel

theorem rows3822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3822 = true := by
  decide +kernel

theorem tot3822 : totK PD2M8K2 D2M8K2.t3822 = [0, 137036695107, 365246540834, 297092170079, 75667423239, 3472187823, 0, 0] := by
  decide +kernel

theorem rows3823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3823 = true := by
  decide +kernel

theorem tot3823 : totK PD2M8K2 D2M8K2.t3823 = [0, 185446988392, 464545544592, 251503354905, 18418208341, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
