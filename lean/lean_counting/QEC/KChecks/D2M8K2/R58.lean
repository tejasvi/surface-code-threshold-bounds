import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t232 = true := by
  decide +kernel

theorem tot232 : totK PD2M8K2 D2M8K2.t232 = [0, 68563118959, 268865912688, 399200314363, 146646231109, 5348807592, 0, 0] := by
  decide +kernel

theorem rows233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t233 = true := by
  decide +kernel

theorem tot233 : totK PD2M8K2 D2M8K2.t233 = [0, 192160971684, 465535955556, 244117289696, 20485833121, 0, 0, 0] := by
  decide +kernel

theorem rows234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t234 = true := by
  decide +kernel

theorem tot234 : totK PD2M8K2 D2M8K2.t234 = [0, 174614079737, 480690032967, 235041774188, 12523541424, 0, 0, 0] := by
  decide +kernel

theorem rows235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t235 = true := by
  decide +kernel

theorem tot235 : totK PD2M8K2 D2M8K2.t235 = [0, 0, 282969236218, 506454363887, 106837346816, 1178750802, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
