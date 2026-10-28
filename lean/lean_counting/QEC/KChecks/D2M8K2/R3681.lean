import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14724 = true := by
  decide +kernel

theorem tot14724 : totK PD2M8K2 D2M8K2.t14724 = [0, 0, 289484017988, 500969637551, 106682900073, 1198073392, 0, 0] := by
  decide +kernel

theorem rows14725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14725 = true := by
  decide +kernel

theorem tot14725 : totK PD2M8K2 D2M8K2.t14725 = [0, 0, 202459797730, 467906979275, 193447461925, 11985024718, 0, 0] := by
  decide +kernel

theorem rows14726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14726 = true := by
  decide +kernel

theorem tot14726 : totK PD2M8K2 D2M8K2.t14726 = [0, 175712015083, 462465575094, 256691999168, 25520062365, 0, 0, 0] := by
  decide +kernel

theorem rows14727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14727 = true := by
  decide +kernel

theorem tot14727 : totK PD2M8K2 D2M8K2.t14727 = [0, 191032714284, 458425168112, 240045290070, 19318830111, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
