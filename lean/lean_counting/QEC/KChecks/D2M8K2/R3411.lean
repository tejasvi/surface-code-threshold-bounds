import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13644 = true := by
  decide +kernel

theorem tot13644 : totK PD2M8K2 D2M8K2.t13644 = [28464616062, 209198139640, 438499579708, 185442845907, 11879463720, 0, 0, 0] := by
  decide +kernel

theorem rows13645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13645 = true := by
  decide +kernel

theorem tot13645 : totK PD2M8K2 D2M8K2.t13645 = [189695431939, 462384789398, 245207118034, 21820606400, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13646 = true := by
  decide +kernel

theorem tot13646 : totK PD2M8K2 D2M8K2.t13646 = [191083501060, 475848354197, 218840191133, 12499826157, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13647 = true := by
  decide +kernel

theorem tot13647 : totK PD2M8K2 D2M8K2.t13647 = [0, 285752411414, 501604808435, 108707063411, 1198073392, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
