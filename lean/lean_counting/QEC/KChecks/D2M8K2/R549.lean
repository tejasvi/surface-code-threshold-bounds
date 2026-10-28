import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2196 = true := by
  decide +kernel

theorem tot2196 : totK PD2M8K2 D2M8K2.t2196 = [0, 0, 120572411280, 435778847841, 290076131460, 22147105371, 0, 0] := by
  decide +kernel

theorem rows2197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2197 = true := by
  decide +kernel

theorem tot2197 : totK PD2M8K2 D2M8K2.t2197 = [0, 0, 0, 319795792740, 455054804714, 75699517924, 1021600638, 0] := by
  decide +kernel

theorem rows2198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2198 = true := by
  decide +kernel

theorem tot2198 : totK PD2M8K2 D2M8K2.t2198 = [0, 0, 161780566314, 389569443056, 258337960013, 62562552534, 3552795014, 0] := by
  decide +kernel

theorem rows2199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t2199 = true := by
  decide +kernel

theorem tot2199 : totK PD2M8K2 D2M8K2.t2199 = [0, 28547172183, 199907515371, 444822243398, 223078283557, 13394709669, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
