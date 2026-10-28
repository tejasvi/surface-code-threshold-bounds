import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2116 = true := by
  decide +kernel

theorem tot2116 : totK PD2M8K2 D2M8K2.t2116 = [0, 131000226796, 438143696495, 299548032863, 25057468589, 0, 0, 0] := by
  decide +kernel

theorem rows2117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2117 = true := by
  decide +kernel

theorem tot2117 : totK PD2M8K2 D2M8K2.t2117 = [0, 0, 200089291190, 476592408397, 188299693997, 9668735432, 0, 0] := by
  decide +kernel

theorem rows2118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2118 = true := by
  decide +kernel

theorem tot2118 : totK PD2M8K2 D2M8K2.t2118 = [0, 87503642934, 321721476645, 374020628854, 100572717580, 3581949829, 0, 0] := by
  decide +kernel

theorem rows2119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2119 = true := by
  decide +kernel

theorem tot2119 : totK PD2M8K2 D2M8K2.t2119 = [0, 157950295526, 444566581534, 267870903770, 25338516709, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
