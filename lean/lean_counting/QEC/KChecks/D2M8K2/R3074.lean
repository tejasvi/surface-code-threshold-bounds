import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12296 = true := by
  decide +kernel

theorem tot12296 : totK PD2M8K2 D2M8K2.t12296 = [0, 210047151610, 469770205301, 195360599480, 9713690252, 0, 0, 0] := by
  decide +kernel

theorem rows12297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12297 = true := by
  decide +kernel

theorem tot12297 : totK PD2M8K2 D2M8K2.t12297 = [0, 76452344322, 383167107772, 338879769292, 52737414375, 1239866073, 0, 0] := by
  decide +kernel

theorem rows12298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12298 = true := by
  decide +kernel

theorem tot12298 : totK PD2M8K2 D2M8K2.t12298 = [0, 19982995165, 323764127386, 473160591278, 59519939507, 0, 0, 0] := by
  decide +kernel

theorem rows12299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12299 = true := by
  decide +kernel

theorem tot12299 : totK PD2M8K2 D2M8K2.t12299 = [0, 179020212113, 449997955176, 265540172868, 25997048245, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
