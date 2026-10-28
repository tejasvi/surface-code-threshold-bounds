import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1104 = true := by
  decide +kernel

theorem tot1104 : totK PD2M8K2 D2M8K2.t1104 = [0, 171880627952, 438556385599, 272958833557, 30342314246, 0, 0, 0] := by
  decide +kernel

theorem rows1105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1105 = true := by
  decide +kernel

theorem tot1105 : totK PD2M8K2 D2M8K2.t1105 = [0, 142682526657, 456099452804, 273121648806, 18539301185, 0, 0, 0] := by
  decide +kernel

theorem rows1106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1106 = true := by
  decide +kernel

theorem tot1106 : totK PD2M8K2 D2M8K2.t1106 = [0, 0, 330778008413, 516460820887, 74421865588, 0, 0, 0] := by
  decide +kernel

theorem rows1107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1107 = true := by
  decide +kernel

theorem tot1107 : totK PD2M8K2 D2M8K2.t1107 = [0, 177884604614, 385515929338, 253161620702, 80202910718, 3880716147, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
