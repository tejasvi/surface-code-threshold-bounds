import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5420 = true := by
  decide +kernel

theorem tot5420 : totK PD2M8K2 D2M8K2.t5420 = [0, 0, 182312272185, 460824487581, 246386939642, 22727590616, 0, 0] := by
  decide +kernel

theorem rows5421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5421 = true := by
  decide +kernel

theorem tot5421 : totK PD2M8K2 D2M8K2.t5421 = [0, 0, 199297713072, 474974588478, 214943799156, 12272470228, 0, 0] := by
  decide +kernel

theorem rows5422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5422 = true := by
  decide +kernel

theorem tot5422 : totK PD2M8K2 D2M8K2.t5422 = [0, 0, 19433589518, 309464988325, 463403557797, 96229844899, 1164319620, 0] := by
  decide +kernel

theorem rows5423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5423 = true := by
  decide +kernel

theorem tot5423 : totK PD2M8K2 D2M8K2.t5423 = [0, 0, 0, 213267548241, 483531119336, 176837787856, 8319232408, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
