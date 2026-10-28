import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t412 = true := by
  decide +kernel

theorem tot412 : totK PD2M8K2 D2M8K2.t412 = [0, 182266461531, 470480940329, 234752231787, 13698234747, 0, 0, 0] := by
  decide +kernel

theorem rows413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t413 = true := by
  decide +kernel

theorem tot413 : totK PD2M8K2 D2M8K2.t413 = [0, 193161962327, 471301176221, 220891455173, 12443528988, 0, 0, 0] := by
  decide +kernel

theorem rows414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t414 = true := by
  decide +kernel

theorem tot414 : totK PD2M8K2 D2M8K2.t414 = [0, 184239626840, 467422405397, 226331257890, 15844255384, 0, 0, 0] := by
  decide +kernel

theorem rows415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t415 = true := by
  decide +kernel

theorem tot415 : totK PD2M8K2 D2M8K2.t415 = [0, 184927962690, 455639151194, 222972939289, 16702988424, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
