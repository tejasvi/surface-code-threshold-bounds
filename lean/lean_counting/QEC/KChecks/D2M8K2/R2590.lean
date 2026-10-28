import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10360 = true := by
  decide +kernel

theorem tot10360 : totK PD2M8K2 D2M8K2.t10360 = [0, 0, 88681645057, 384023543335, 362834030220, 46680436414, 1075657031, 0] := by
  decide +kernel

theorem rows10361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10361 = true := by
  decide +kernel

theorem tot10361 : totK PD2M8K2 D2M8K2.t10361 = [0, 0, 84383129986, 421485211514, 363069274134, 35279051677, 0, 0] := by
  decide +kernel

theorem rows10362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10362 = true := by
  decide +kernel

theorem tot10362 : totK PD2M8K2 D2M8K2.t10362 = [0, 0, 180193777942, 455567059811, 261516582720, 25305654963, 0, 0] := by
  decide +kernel

theorem rows10363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10363 = true := by
  decide +kernel

theorem tot10363 : totK PD2M8K2 D2M8K2.t10363 = [0, 0, 160579605283, 460600483594, 258425241727, 19344651702, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
