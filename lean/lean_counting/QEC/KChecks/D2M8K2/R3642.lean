import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14568 = true := by
  decide +kernel

theorem tot14568 : totK PD2M8K2 D2M8K2.t14568 = [50237987801, 224982914247, 424538672875, 198375236211, 9355690997, 0, 0, 0] := by
  decide +kernel

theorem rows14569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14569 = true := by
  decide +kernel

theorem tot14569 : totK PD2M8K2 D2M8K2.t14569 = [186734894247, 461820538770, 250652451389, 23006903105, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14570 = true := by
  decide +kernel

theorem tot14570 : totK PD2M8K2 D2M8K2.t14570 = [108444201513, 428269576195, 340474497719, 32025533088, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14571 = true := by
  decide +kernel

theorem tot14571 : totK PD2M8K2 D2M8K2.t14571 = [0, 213566503823, 495616287879, 182160237601, 9469033438, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
