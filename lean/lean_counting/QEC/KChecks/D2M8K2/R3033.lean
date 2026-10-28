import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12132 = true := by
  decide +kernel

theorem tot12132 : totK PD2M8K2 D2M8K2.t12132 = [0, 164123983786, 440095412103, 283823805208, 29976125450, 0, 0, 0] := by
  decide +kernel

theorem rows12133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12133 = true := by
  decide +kernel

theorem tot12133 : totK PD2M8K2 D2M8K2.t12133 = [0, 101713183239, 410983926550, 335707189261, 38258606517, 0, 0, 0] := by
  decide +kernel

theorem rows12134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12134 = true := by
  decide +kernel

theorem tot12134 : totK PD2M8K2 D2M8K2.t12134 = [0, 0, 217824168650, 485529980504, 177687548398, 9668735432, 0, 0] := by
  decide +kernel

theorem rows12135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12135 = true := by
  decide +kernel

theorem tot12135 : totK PD2M8K2 D2M8K2.t12135 = [0, 93572726759, 339446714640, 350143799189, 94198258493, 3581949829, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
