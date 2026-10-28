import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8304 = true := by
  decide +kernel

theorem tot8304 : totK PD2M8K2 D2M8K2.t8304 = [0, 203278056814, 488619697541, 211503461708, 11311631362, 0, 0, 0] := by
  decide +kernel

theorem rows8305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8305 = true := by
  decide +kernel

theorem tot8305 : totK PD2M8K2 D2M8K2.t8305 = [0, 187500027654, 486651170159, 225026489167, 12773261822, 0, 0, 0] := by
  decide +kernel

theorem rows8306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8306 = true := by
  decide +kernel

theorem tot8306 : totK PD2M8K2 D2M8K2.t8306 = [0, 179289773595, 442421537045, 263986986888, 27181631858, 0, 0, 0] := by
  decide +kernel

theorem rows8307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8307 = true := by
  decide +kernel

theorem tot8307 : totK PD2M8K2 D2M8K2.t8307 = [0, 87926934625, 388033636209, 345013599068, 52054982587, 1171084559, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
